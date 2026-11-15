; Expected: sat
; Preserve the fourth legacy offset: interleaving parameters would lose x+3.
(set-logic ALL)
(declare-fun f (Int Int) Int)
(assert (forall ((x Int) (y Int)) (> (f x y) x)))
(assert (not (= (f 3 0) 4)))
(check-sat)
