;; D10(c), 2026-09-23 linear hunt M5 (dzincr_31_00040): a scoped equality on a
;; symbolic-divisor quotient rewrote the base to false, activated at depth 0
;; (--z3-mode unsat after the pop). z3 5.1.0: unsat sat.
(set-logic ALL)
(declare-fun b () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (> (div b (- y z)) 2))
(assert (= y 0))
(push 1)
(assert (= (div b (- y z)) (- 1)))
(check-sat)
(pop 1)
(check-sat)
