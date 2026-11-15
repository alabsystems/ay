; Original derivation: P(0), then Q(2). Expected HORN check-sat: unsat.
; Separate rule-local square envelopes must not share one auxiliary variable.
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int))
  (=> (and (<= 0 x) (<= x 1) (= (mod (* x x) 5) 0)) (P x))))
(assert (forall ((x Int) (y Int))
  (=> (and (P x) (<= 2 y) (<= y 3) (= (mod (* y y) 5) 4)) (Q y))))
(assert (forall ((y Int)) (=> (Q y) false)))
(check-sat)
