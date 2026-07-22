; two_phase_unsafe_000.smt2
; Reconstructed regression fixture for issue 7688 (the original instance was not
; vendored). A genuinely two-phase, genuinely UNSAFE linear-integer CHC system:
; phase one (P1) counts x up to 10 while accumulating y; control then transfers
; to phase two (P2), which keeps accumulating; the query y >= 100 is reachable,
; so the system is unsafe and must NOT be classified safe.
(set-logic HORN)
(declare-fun P1 (Int Int) Bool)
(declare-fun P2 (Int Int) Bool)

(assert (forall ((x Int) (y Int))
  (=> (and (= x 0) (= y 0)) (P1 x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
  (=> (and (P1 x y) (< x 10) (= x1 (+ x 1)) (= y1 (+ y x))) (P1 x1 y1))))
(assert (forall ((x Int) (y Int))
  (=> (and (P1 x y) (>= x 10)) (P2 x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
  (=> (and (P2 x y) (= x1 (+ x 1)) (= y1 (+ y x))) (P2 x1 y1))))
(assert (forall ((x Int) (y Int))
  (=> (and (P2 x y) (>= y 100)) false)))
(check-sat)
