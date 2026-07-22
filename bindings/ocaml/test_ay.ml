(* Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0 *)

(* End-to-end test of the OCaml binding against libay_ffi.
   Verdicts asserted here are cross-checked against the z3 CLI (see run.sh).
   Exit code 0 iff every assertion holds. *)

let failures = ref 0

let check name got want =
  if got = want then
    Printf.printf "  PASS: %s -> %s\n" name (Ay.string_of_result got)
  else begin
    incr failures;
    Printf.printf "  FAIL: %s -> got %s, want %s\n"
      name (Ay.string_of_result got) (Ay.string_of_result want)
  end

let check_bool name cond =
  if cond then Printf.printf "  PASS: %s\n" name
  else begin incr failures; Printf.printf "  FAIL: %s\n" name end

(* (1) LIA SAT: 0 < x, x < 5, y = x + 1 -> SAT, model present. *)
let test_lia_sat () =
  let s = Ay.mk_solver ~logic:"QF_LIA" () in
  let x = Ay.int_const s "x" in
  let y = Ay.int_const s "y" in
  Ay.assert_ s (Ay.gt x (Ay.int_lit 0));
  Ay.assert_ s (Ay.lt x (Ay.int_lit 5));
  Ay.assert_ s (Ay.eq y (Ay.add [ x; Ay.int_lit 1 ]));
  check "lia_sat" (Ay.check_sat s) Ay.Sat;
  (match Ay.get_model s with
   | Some m -> check_bool "lia_sat:model_present" (String.length m > 0);
               Printf.printf "    model: %s\n"
                 (String.map (fun c -> if c = '\n' then ' ' else c) m)
   | None -> check_bool "lia_sat:model_present" false);
  Ay.free s

(* (2) LIA UNSAT: x > 10 and x < 3 -> UNSAT. *)
let test_lia_unsat () =
  let s = Ay.mk_solver ~logic:"QF_LIA" () in
  let x = Ay.int_const s "x" in
  Ay.assert_ s (Ay.gt x (Ay.int_lit 10));
  Ay.assert_ s (Ay.lt x (Ay.int_lit 3));
  check "lia_unsat" (Ay.check_sat s) Ay.Unsat;
  Ay.free s

(* (3) Boolean SAT: (a OR b) AND (NOT a) -> SAT (b true). *)
let test_bool_sat () =
  let s = Ay.mk_solver ~logic:"QF_UF" () in
  let a = Ay.bool_const s "a" in
  let b = Ay.bool_const s "b" in
  Ay.assert_ s (Ay.or_ [ a; b ]);
  Ay.assert_ s (Ay.not_ a);
  check "bool_sat" (Ay.check_sat s) Ay.Sat;
  Ay.free s

(* (4) Boolean UNSAT: a AND (NOT a) -> UNSAT. *)
let test_bool_unsat () =
  let s = Ay.mk_solver ~logic:"QF_UF" () in
  let a = Ay.bool_const s "a" in
  Ay.assert_ s (Ay.and_ [ a; Ay.not_ a ]);
  check "bool_unsat" (Ay.check_sat s) Ay.Unsat;
  Ay.free s

(* (5) implies/ite UNSAT: (=> p q) AND p AND (NOT q) -> UNSAT. *)
let test_implies_unsat () =
  let s = Ay.mk_solver ~logic:"QF_UF" () in
  let p = Ay.bool_const s "p" in
  let q = Ay.bool_const s "q" in
  Ay.assert_ s (Ay.implies p q);
  Ay.assert_ s p;
  Ay.assert_ s (Ay.not_ q);
  check "implies_unsat" (Ay.check_sat s) Ay.Unsat;
  Ay.free s

(* (6) push/pop incrementality: SAT, push a contradiction -> UNSAT,
   pop -> SAT again. Exercises scoped assertions. *)
let test_push_pop () =
  let s = Ay.mk_solver ~logic:"QF_LIA" () in
  let x = Ay.int_const s "x" in
  Ay.assert_ s (Ay.gt x (Ay.int_lit 0));
  check "push_pop:base_sat" (Ay.check_sat s) Ay.Sat;
  Ay.push s;
  Ay.assert_ s (Ay.lt x (Ay.int_lit 0));
  check "push_pop:scoped_unsat" (Ay.check_sat s) Ay.Unsat;
  Ay.pop s 1;
  check "push_pop:after_pop_sat" (Ay.check_sat s) Ay.Sat;
  Ay.free s

(* (7) mk_solver with a bogus logic must fail closed (Failure), not silently
   proceed with no logic set. *)
let test_bad_logic_rejected () =
  match Ay.mk_solver ~logic:"QF_NO_SUCH_LOGIC" () with
  | s -> Ay.free s; check_bool "bad_logic_rejected" false
  | exception Failure _ -> check_bool "bad_logic_rejected" true

(* (8) add/sub/mul on [] must raise Invalid_argument immediately instead of
   emitting malformed SMT-LIB like "(+ )" that only fails at assert time. *)
let test_empty_arith_rejected () =
  let raises_invalid name f =
    match f () with
    | (_ : Ay.term) -> check_bool name false
    | exception Invalid_argument _ -> check_bool name true
  in
  raises_invalid "empty_add_rejected" (fun () -> Ay.add []);
  raises_invalid "empty_sub_rejected" (fun () -> Ay.sub []);
  raises_invalid "empty_mul_rejected" (fun () -> Ay.mul [])

let () =
  Printf.printf "AY OCaml binding test\n";
  Printf.printf "  linked AY version: %s\n" (Ay.version ());
  test_lia_sat ();
  test_lia_unsat ();
  test_bool_sat ();
  test_bool_unsat ();
  test_implies_unsat ();
  test_push_pop ();
  test_bad_logic_rejected ();
  test_empty_arith_rejected ();
  if !failures = 0 then begin
    Printf.printf "All OCaml binding tests passed.\n";
    exit 0
  end else begin
    Printf.printf "%d OCaml binding test(s) FAILED.\n" !failures;
    exit 1
  end
