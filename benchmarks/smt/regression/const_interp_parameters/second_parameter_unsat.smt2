; Expected: unsat
; More candidates cannot certify an inconsistent quantified/ground pair.
(set-logic ALL)
(declare-fun f (Int Int) Int)
(assert (forall ((x Int) (y Int)) (> (f x y) y)))
(assert (not (> (f 0 3) 3)))
(check-sat)
