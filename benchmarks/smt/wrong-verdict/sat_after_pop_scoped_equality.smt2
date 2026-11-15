;; D10(c): a scoped (= x 0) substituted into the base (> (* x y) 3) gave false,
;; activated permanently (--z3-mode unsat after the pop). z3 5.1.0: unsat sat.
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> (* x y) 3))
(push 1)
(assert (= x 0))
(check-sat)
(pop 1)
(check-sat)
