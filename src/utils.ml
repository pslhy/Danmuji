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

exception BadTrace of string

let debug_out = ref stderr 
let _ = Random.init (int_of_float (Unix.time ()))

type variable = {
  name : string;
  typ : string;
}

let time_of_string _ = 
  let time = Unix.time () in
  let { 
    Unix.tm_sec=seconds; 
    tm_min=minutes; 
    tm_hour=hours;
    tm_mday=day_of_month;
    tm_mon=month; 
    tm_year=year;
    tm_wday=wday; 
    tm_yday=yday; 
    tm_isdst=isdst
  } = Unix.localtime time in
  Printf.sprintf "%04d-%02d-%02d %02d:%02d:%02d" (year + 1900) (month + 1) day_of_month hours minutes seconds
    
(** we copy all debugging output to a file and to stdout *)
let debug fmt = 
  let k result = begin
      output_string !debug_out ("[" ^ (time_of_string ()) ^ "] " ^ result) ; 
      (* output_string stdout result ;  *)
      (* flush stdout ;  *)
      flush !debug_out;
  end in
   if !Options.verbose then Printf.kprintf k fmt else Printf.kprintf (fun s -> ()) fmt

let error fmt =
  prerr_endline ("[" ^ (time_of_string ()) ^ "] " ^ (Printf.sprintf fmt))

let parse_decls f = 
  let lines = BatFile.lines_of f in 
  let rec aux current_var acc = function
    | None -> acc
    | Some line ->
      if BatString.starts_with (BatString.trim line) "variable " then
        let name = BatString.trim (BatString.tail (BatString.trim line) 9) in
        aux (Some name) acc (BatEnum.get lines)
      else if BatString.starts_with (BatString.trim line) "dec-type " then
        match current_var with
        | Some name ->
          let typ = BatString.trim (BatString.tail (BatString.trim line) 9) in
          aux None (BatMap.add name typ acc) (BatEnum.get lines)
        | None -> raise (BadTrace "Ill-formed trace file")
      else
        aux current_var acc (BatEnum.get lines)
  in
  aux None BatMap.empty (BatEnum.get lines)

let string_of_vars vs = 
  let rec aux acc = function
    | [] -> acc
    | (name, typ) :: vs -> aux (acc ^ name ^ " : " ^ typ ^ " | ") vs
  in
  aux "" (BatMap.bindings vs)

let parse_traces f decls = 
  let lines = BatFile.lines_of f in 
  let traces = ref [] in
  let rec aux current_var acc state trace = function
    | None -> acc
    | Some line ->
      if BatString.starts_with (BatString.trim line) "..fix_location():::EXIT" then (* Starts Parsing / End of trace *)
        if BatMap.is_empty trace then
          aux current_var acc 1 trace (BatEnum.get lines) 
        else
          let _ = traces := trace :: !traces in
          aux current_var acc 1 BatMap.empty (BatEnum.get lines) 
      else if BatString.starts_with (BatString.trim line) "..fix_location():::ENTER" || BatString.is_empty (BatString.trim line) then (* Continue *)
        aux current_var acc 0 trace (BatEnum.get lines) 
      else if state = 1 then (* Variable name *)
        let name = BatString.trim line in
        aux (Some name) acc 2 trace (BatEnum.get lines) 
      else if state = 2 then (* Variable value *)
        match current_var with
        | Some name ->
          let value = BatString.trim line in
          let _ = try BatMap.find name decls with Not_found -> raise (BadTrace ("Unknown variable: " ^ name)) in
          let trace' = BatMap.add name value trace in
          aux None acc 3 trace' (BatEnum.get lines) 
        | None -> raise (BadTrace "Ill-formed trace file")
      else if state = 3 then (* End of variable *)
        aux None acc 1 trace (BatEnum.get lines) 
      else
        aux current_var acc 0 trace (BatEnum.get lines)
  in
  let _ = aux None [] 0 BatMap.empty (BatEnum.get lines) in
  !traces

let string_of_trace trace = 
  let rec aux acc = function
    | [] -> acc
    | (name, value) :: trace -> aux (acc ^ name ^ " = " ^  value ^ " | ") trace
  in
  aux "" (BatMap.bindings trace)