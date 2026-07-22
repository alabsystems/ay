; expected: unsat
; A universally quantified fact contradicting an instance.
(set-logic LIA)
(set-info :status unsat)
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (not (p 7)))
(check-sat)
