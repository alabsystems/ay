; Expected: sat
; A widened radix must not replace the legacy 24-combination pass with >32.
(set-logic ALL)
(declare-fun f (Int Int) Int)
(declare-fun c () Int)
(assert (forall ((x Int) (y Int)) (> (f x y) x)))
(assert (not (= c 3)))
(assert (not (= c 4)))
(check-sat)
