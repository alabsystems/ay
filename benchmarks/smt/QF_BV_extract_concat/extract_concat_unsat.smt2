; Andrew Yates <andrewyates.name@gmail.com>
; Unsatisfiable due to extract/concat constraints
(set-logic QF_BV)
(set-info :status unsat)

(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))

; x[7:4] = y[7:4] and x[3:0] = y[3:0] implies x = y
(assert (= ((_ extract 7 4) x) ((_ extract 7 4) y)))
(assert (= ((_ extract 3 0) x) ((_ extract 3 0) y)))
; But x != y - contradiction
(assert (not (= x y)))

(check-sat)
(exit)
