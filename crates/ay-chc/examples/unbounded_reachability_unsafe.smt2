; Program: x starts at 0, increments, aborts when x > 10
; Expected: UNSAT (abort IS reachable - program is UNSAFE)
; Issue #19: Regression test from kani_fast soundness bug report (2026-01-02)
; The reported bug (AY returning SAT) is now fixed.

(set-logic HORN)
(declare-fun Inv (Int Int) Bool)

; Initial: x = 0, pc = 0
(assert (forall ((x Int) (pc Int))
  (=> (and (= x 0) (= pc 0)) (Inv x pc))))

; Loop: when x <= 10, increment x
(assert (forall ((x Int) (pc Int) (x_next Int) (pc_next Int))
  (=> (and (Inv x pc) (= pc 0) (<= x 10) (= x_next (+ x 1)) (= pc_next 0))
      (Inv x_next pc_next))))

; Exit: when x > 10, go to abort (pc = 1)
(assert (forall ((x Int) (pc Int) (x_next Int) (pc_next Int))
  (=> (and (Inv x pc) (= pc 0) (> x 10) (= x_next x) (= pc_next 1))
      (Inv x_next pc_next))))

; Safety: abort should NOT be reachable
(assert (forall ((x Int) (pc Int))
  (=> (and (Inv x pc) (= pc 1)) false)))

(check-sat)
