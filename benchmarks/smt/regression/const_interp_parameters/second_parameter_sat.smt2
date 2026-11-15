; Expected: sat
; Ground literals must not starve the second parameter's y+3 witness.
(set-logic ALL)
(declare-fun f (Int Int) Int)
(assert (forall ((x Int) (y Int)) (> (f x y) y)))
(assert (not (= (f 0 3) 4)))
(check-sat)
