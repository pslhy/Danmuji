exception InvalidInvariant of string
open Unsigned

type const = 
  | INT of int64
  | PTR of UInt64.t

type invariant = 
  | VAR of string
  | CONST of const
  | EQ of invariant * invariant
  | NE of invariant * invariant
  | GT of invariant * invariant
  | GE of invariant * invariant
  | LE of invariant * invariant
  | LT of invariant * invariant
  | ADD of invariant * invariant
  | SUB of invariant * invariant
  | MUL of invariant * invariant
  | DIV of invariant * invariant

let global_specials = [2L;4L;8L;16L;32L;64L;100L;128L;256L;512L;1024L;2048L;4096L;8192L;16384L;32767L;65535L;1048575L;2147483647L;4294967295L]

let build_int_list lb ub =
  let rec build_int_list_aux lb ub acc =
    if lb > ub then acc
    else build_int_list_aux lb (Int64.sub ub 1L) (ub :: acc)
  in
  build_int_list_aux lb ub []

(* var == const *)
let generate_OneOfScalar int_decls lb ub sps =
  let consts = (build_int_list lb ub) @ sps in 
  BatMap.foldi (fun k _ l -> (List.fold_left (fun invl c  -> EQ((VAR k),(CONST (INT c)))::invl ) [] consts) @ l) int_decls []

(* var != 0 *)
let generate_NonZero decls =
  BatMap.foldi (fun k _ l -> (NE((VAR k),(CONST (INT 0L))))::l) decls []

(* var >= const *)
let generate_LowerBound decls lb ub sps =
  let consts = (build_int_list lb ub) @ sps in 
  BatMap.foldi (fun k _ l -> (List.fold_left (fun invl c  -> GE((VAR k),(CONST (INT c)))::invl ) [] consts) @ l) decls []

(* var > var *)
let generate_IntGreaterThan decls =
  BatMap.foldi (fun k v l -> (BatMap.foldi (fun k' v' l' -> 
      if String.equal k k' || not (BatString.equal v v') then l'
      else (GT((VAR k),(VAR k')))::l') decls []
    ) @ l) decls []

(* var - var >= const *)
let generate_IntDiffLowerBound decls lb ub sps = 
  let consts = (build_int_list lb ub) @ sps in 
  BatMap.foldi (fun k v l -> (BatMap.foldi (fun k' v' l' -> 
      if String.equal k k' || not (BatString.equal v v') then l'
      else (List.fold_left (fun invl c  -> GE((SUB((VAR k),(VAR k'))),(CONST (INT c)))::invl ) [] consts) @ l') decls []
    ) @ l) decls []

(* var <= var / const *)
let generate_IntDivUpperBound decls lb ub = 
  let consts = build_int_list lb ub in 
  BatMap.foldi (fun k _ l -> (BatMap.foldi (fun k' _ l' -> 
      if String.equal k k' then l'
      else (List.fold_left (fun invl c  -> LE((VAR k'), (DIV((VAR k),(CONST (INT c)))))::invl ) [] consts) @ l') decls []
    ) @ l) decls []

let string_of_invariant inv =
  let rec internal_str inv' s =
    match inv' with
    | VAR v -> s ^ v
    | CONST c -> s ^ (match c with INT i -> Int64.to_string i | PTR p -> UInt64.to_string p)
    | EQ (i1, i2) -> internal_str i1 s ^ " == " ^ internal_str i2 s
    | NE (i1, i2) -> internal_str i1 s ^ " != " ^ internal_str i2 s
    | GT (i1, i2) -> internal_str i1 s ^ " > " ^ internal_str i2 s
    | GE (i1, i2) -> internal_str i1 s ^ " >= " ^ internal_str i2 s
    | LT (i1, i2) -> internal_str i1 s ^ " < " ^ internal_str i2 s
    | LE (i1, i2) -> internal_str i1 s ^ " <= " ^ internal_str i2 s
    | ADD (i1, i2) -> internal_str i1 s ^ " + " ^ internal_str i2 s
    | SUB (i1, i2) -> internal_str i1 s ^ " - " ^ internal_str i2 s
    | MUL (i1, i2) -> internal_str i1 s ^ " * " ^ internal_str i2 s
    | DIV (i1, i2) -> internal_str i1 s ^ " / " ^ internal_str i2 s
  in
  internal_str inv ""

let generate_invariants decls =
  let sps = global_specials in
  let int_decls = BatMap.filterv (fun v -> BatString.equal "int" v) decls in
  let one_of_scalar = generate_OneOfScalar int_decls (-10L) 100L sps in
  let non_zero = generate_NonZero decls in
  let lower_bound = generate_LowerBound int_decls (-10L) 10L sps in
  let int_greater_than = generate_IntGreaterThan decls in
  let int_diff_lower_bound = generate_IntDiffLowerBound decls 1L 10L sps in
  let int_div_upper_bound = generate_IntDivUpperBound int_decls 2L 10L in
  one_of_scalar @ non_zero @ lower_bound @ int_greater_than @ int_diff_lower_bound @ int_div_upper_bound

let rec evaluate inv trace  =
  let const_to_int c = match c with INT i -> i | PTR p -> UInt64.to_int64 p in
  match inv with 
  | VAR v -> 
    if BatString.starts_with (BatMap.find v trace) "-" then Int64.of_string (BatMap.find v trace)
    else UInt64.to_int64 (UInt64.of_string (BatMap.find v trace))
  | CONST c -> const_to_int c
  | EQ (i1, i2) -> if evaluate i1 trace = evaluate i2 trace then 1L else 0L
  | NE (i1, i2) -> if evaluate i1 trace != evaluate i2 trace then 1L else 0L
  | GT (i1, i2) -> if evaluate i1 trace > evaluate i2 trace then 1L else 0L
  | GE (i1, i2) -> if evaluate i1 trace >= evaluate i2 trace then 1L else 0L
  | LT (i1, i2) -> if evaluate i1 trace < evaluate i2 trace then 1L else 0L
  | LE (i1, i2) -> if evaluate i1 trace <= evaluate i2 trace then 1L else 0L
  | ADD (i1, i2) -> Int64.add (evaluate i1 trace) (evaluate i2 trace)
  | SUB (i1, i2) -> Int64.sub (evaluate i1 trace) (evaluate i2 trace)
  | MUL (i1, i2) -> Int64.mul (evaluate i1 trace) (evaluate i2 trace)
  | DIV (i1, i2) -> Int64.div (evaluate i1 trace) (evaluate i2 trace)

let validate invs traces is_pass =
  BatList.filter (fun inv -> 
    BatList.fold_left (fun acc trace -> acc && evaluate inv trace = (if is_pass then 1L else 0L)) true traces
  ) invs