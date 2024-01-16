(***********************************************************************)
(*                                                                     *)
(* Copyright (c) 2022-Present.                                         *)
(* Programming System Laboratory (PSL), Hanyang University.            *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* This software is distributed under the term of the BSD license.     *)
(* See the LICENSE file for details.                                   *)
(*                                                                     *)
(***********************************************************************)

open Utils

let input_files = ref []
let decl_file = ref ""
let pass_trace_file = ref ""
let fail_trace_file = ref ""

let args : string -> unit = fun f ->
  let arg_list = BatString.split_on_string ~by:" " f in 
  let _ = debug "arg_list: %s \n" (BatString.concat " " arg_list) in
  if List.length arg_list = 3 then
    let _ = decl_file := List.nth arg_list 0 in
    let _ = pass_trace_file := List.nth arg_list 1 in
    let _ = fail_trace_file := List.nth arg_list 2 in
    let _ = debug "Decl file:\n" in
    ()
  else
    let _ = error "Error: Invalid arguments\n" in
    exit 1


let usage_msg = "danmuji.exe [-verbose] <decl_file> <pass_trace> <fail_trace>"

let anon_fun filenames = input_files := filenames :: !input_files

let check_args () =
  if List.length !input_files < 3 then
    let _ = error "Error: Invalid arguments" in
    exit 1
  else
    let _ = decl_file := List.nth !input_files 2 in
    let _ = pass_trace_file := List.nth !input_files 1 in
    let _ = fail_trace_file := List.nth !input_files 0 in
    if not (Sys.file_exists !decl_file) then
      let _ = error "Error: Declaration file does not exist" in
      exit 1
    else if not (Sys.file_exists !pass_trace_file) then
      let _ = error "Error: Pass trace file does not exist" in
      exit 1
    else if not (Sys.file_exists !fail_trace_file) then
      let _ = error "Error: Fail trace file does not exist" in
      exit 1
    else
      let _ = debug "Argument parse completed\n" in
    ()

let () =
  Arg.parse Options.options anon_fun usage_msg;
  check_args ();
  let decls = Utils.parse_decls !decl_file in
  let _ =  debug "# of Decls : %d\n" (BatMap.cardinal decls) in
  let pass_trace = Utils.parse_traces !pass_trace_file decls in
  debug "# of Pass trace : %d\n" (List.length pass_trace);
  let fail_trace = Utils.parse_traces !fail_trace_file decls in
  debug "# of Fail trace : %d\n" (List.length fail_trace);
  let _ = debug "Start to generate invariants\n" in
  let invariants = Invariants.generate_invariants decls in
  let _ = debug "# of invariants : %d\n" (List.length invariants) in
  let _ = print_endline (Printf.sprintf "Hypothesis Space : %d" (List.length invariants)) in
  let _ = debug "Start to check pass traces\n" in
  let pass_result = Invariants.validate invariants pass_trace true in
  let _ = debug "# of passing invariants : %d\n" (List.length pass_result) in
  let _ = debug "Start to check fail traces\n" in
  let fail_result = Invariants.validate pass_result fail_trace false in
  debug "# of failing invariants : %d\n" (List.length fail_result);
  if !Options.verbose then
    let _ = debug "============ FINAL INVARIANTS ============\n" in
    let _ = List.iter (fun inv -> debug "%s\n" (Invariants.string_of_invariant inv)) fail_result in ()
  else 
    let _ = List.iter (fun inv -> print_endline (Printf.sprintf "%s" (Invariants.string_of_invariant inv))) fail_result in ()

