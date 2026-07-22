(set-info :status unsat)
(set-logic UFLIA)

; Strict-monotonicity pigeonhole: f strictly increasing on [0,25] forces
; f(25) >= f(0) + 25 = 27, contradicting f(25) = 26.
(declare-fun f (Int) Int)
(assert (forall ((x Int) (y Int))
  (=> (and (<= 0 x) (< x y) (<= y 25)) (< (f x) (f y)))))
(assert (= (f 0) 2))
(assert (= (f 25) 26))

(check-sat)
