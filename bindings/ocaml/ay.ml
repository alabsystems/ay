(* Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0 *)

(* OCaml binding for the AY SMT solver. Thin/sound wrapper over the C API:
   verdicts and models come from AY; this module only builds SMT-LIB text and
   marshals it across the FFI. *)

type result = Sat | Unsat | Unknown | Error

let string_of_result = function
  | Sat -> "sat"
  | Unsat -> "unsat"
  | Unknown -> "unknown"
  | Error -> "error"

(* C result codes mirror the #defines in ay.h:
   AY_SAT=1, AY_UNSAT=0, AY_UNKNOWN=-1, AY_ERROR=-2. *)
let result_of_code = function
  | 1 -> Sat
  | 0 -> Unsat
  | -1 -> Unknown
  | _ -> Error

(* ---- raw externals (implemented in ay_stubs.c) --------------------------- *)

type solver

external c_solver_new : unit -> solver = "ocaml_ay_solver_new"
external c_solver_free : solver -> unit = "ocaml_ay_solver_free"
external c_reset : solver -> unit = "ocaml_ay_reset"
external c_solve_smtlib : solver -> string -> int = "ocaml_ay_solve_smtlib"
external c_assert : solver -> string -> int = "ocaml_ay_assert"
external c_check_sat : solver -> int = "ocaml_ay_check_sat"
external c_push : solver -> unit = "ocaml_ay_push"
external c_pop : solver -> int -> int = "ocaml_ay_pop"
external c_get_model : solver -> string = "ocaml_ay_get_model"
external c_get_error : solver -> string = "ocaml_ay_get_error"
external c_version : unit -> string = "ocaml_ay_version"

(* ---- lifecycle ----------------------------------------------------------- *)

let version () = c_version ()
let free s = c_solver_free s
let reset s = c_reset s

let solve_smtlib s smt = result_of_code (c_solve_smtlib s smt)

let mk_solver ?logic () =
  let s = c_solver_new () in
  (match logic with
   | Some l ->
     let code = c_solve_smtlib s (Printf.sprintf "(set-logic %s)" l) in
     (* set-logic yields no check-sat output, so AY_UNKNOWN(-1) is expected;
        a real failure surfaces as AY_ERROR(-2). Fail closed if rejected. *)
     if code = -2 then
       failwith (Printf.sprintf "AY rejected (set-logic %s): %s"
                   l (c_get_error s))
   | None -> ());
  s

(* ---- term construction (SMT-LIB text builders) --------------------------- *)

type sort = Bool | Int | Real
type term = { sexpr : string }

let to_string t = t.sexpr
let mk s = { sexpr = s }

let sort_name = function Bool -> "Bool" | Int -> "Int" | Real -> "Real"

let declare_const s name sort =
  let code =
    c_solve_smtlib s (Printf.sprintf "(declare-const %s %s)" name (sort_name sort))
  in
  (* declare-const yields no check-sat output, so AY_UNKNOWN(-1) is expected;
     a real failure surfaces as AY_ERROR(-2). Fail closed if rejected. *)
  if code = -2 then
    failwith (Printf.sprintf "AY rejected (declare-const %s %s): %s"
                name (sort_name sort) (c_get_error s));
  mk name

let bool_const s n = declare_const s n Bool
let int_const s n = declare_const s n Int
let real_const s n = declare_const s n Real

let true_ = mk "true"
let false_ = mk "false"
let bool_lit b = if b then true_ else false_

let int_lit n =
  (* SMT-LIB numerals are non-negative; a negative integer is (- n). *)
  if n < 0 then mk (Printf.sprintf "(- %d)" (- n)) else mk (string_of_int n)

let app op args =
  mk (Printf.sprintf "(%s %s)" op (String.concat " " (List.map to_string args)))

let not_ a = app "not" [ a ]

(* n-ary connectives with the standard SMT-LIB identities for 0/1 args. *)
let and_ = function
  | [] -> true_
  | [ x ] -> x
  | xs -> app "and" xs

let or_ = function
  | [] -> false_
  | [ x ] -> x
  | xs -> app "or" xs

let implies a b = app "=>" [ a; b ]
let iff a b = app "=" [ a; b ]
let ite c t e = app "ite" [ c; t; e ]

let eq a b = app "=" [ a; b ]
let neq a b = not_ (eq a b)
let lt a b = app "<" [ a; b ]
let le a b = app "<=" [ a; b ]
let gt a b = app ">" [ a; b ]
let ge a b = app ">=" [ a; b ]

(* Arithmetic is untyped over Int/Real here, so an empty application has no
   sort-safe SMT-LIB identity (an integer numeral 0/1 could be sort-incorrect
   in a Real context). Fail fast instead of emitting malformed "(+ )". *)
let add = function
  | [] -> invalid_arg "Ay.add: empty list"
  | [ x ] -> x
  | xs -> app "+" xs

let sub = function
  | [] -> invalid_arg "Ay.sub: empty list"
  | [ x ] -> app "-" [ x ]
  | xs -> app "-" xs

let mul = function
  | [] -> invalid_arg "Ay.mul: empty list"
  | [ x ] -> x
  | xs -> app "*" xs
let neg a = app "-" [ a ]

(* ---- assertion / checking (delegated to AY) ------------------------------ *)

let assert_ s t =
  let code = c_assert s (to_string t) in
  if code <> 0 then
    failwith (Printf.sprintf "AY rejected assertion %s: %s"
                (to_string t) (c_get_error s))

let check_sat s = result_of_code (c_check_sat s)
let push s = c_push s

let pop s levels =
  let code = c_pop s levels in
  if code <> 0 then
    failwith (Printf.sprintf "AY pop %d failed: %s" levels (c_get_error s))

let none_if_empty str = if str = "" then None else Some str
let get_model s = none_if_empty (c_get_model s)
let last_error s = none_if_empty (c_get_error s)
