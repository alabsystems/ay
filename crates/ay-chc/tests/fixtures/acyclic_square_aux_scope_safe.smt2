; Control: neither 2*2 nor 3*3 is 2 modulo 5. Expected HORN check-sat: sat.
; A fresh-square relaxation must not make an invalid SAT witness authoritative.
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int))
  (=> (and (<= 0 x) (<= x 1) (= (mod (* x x) 5) 0)) (P x))))
(assert (forall ((x Int) (y Int))
  (=> (and (P x) (<= 2 y) (<= y 3) (= (mod (* y y) 5) 2)) (Q y))))
(assert (forall ((y Int)) (=> (Q y) false)))
(check-sat)
