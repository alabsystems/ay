; Satisfiable QF_UFNIA problem on which AY main (b1c1f8f201 .. f399eca07a)
; answers `unsat` in both postures (default and --z3-mode). z3 5.1.0: sat.
; z3 model: a = c != b, f(a) = x = 2, y = 21, f(b) = w = 46, p = 1, q = 1.
;
; From the NIA decider-explanations verifier (2026-09-21, family `euf_div`,
; source `euf_div_026`). Mechanism: with `a = b` decided, EUF hands the NIA the
; shared equality f(a) = f(b) with reason (= a b); the inner LIA holds it as
; a row and refutes x = w > K >= x; the check loop returned the ASSERTED
; atoms alone as the conflict (z3-satisfiable without the shared equality),
; the learned clause was empty and the lane answered `unsat`. Fixed by
; `full_conflict_lits` (ay-nia/src/full_conflict.rs): every full-set NIA/NRA
; conflict also names the reasons of the shared equalities the inner solver
; held. `sat` or `unknown` is acceptable; `unsat` is the regression.
(set-logic QF_UFNIA)
(set-info :status sat)
(declare-sort U 0)
(declare-fun f (U) Int)
(declare-fun g (U) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const w Int)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const p Int)
(declare-const q Int)
(assert (= (* x y) 42))
(assert (>= x 1))
(assert (>= y 1))
(assert (= (f a) x))
(assert (= (f b) w))
(assert (>= w 46))
(assert (or (= a c) (= a b)))
(assert (= (f c) 2))
(assert (>= (* p q) 1))
(assert (<= p 9))
(assert (>= q 0))
(check-sat)
