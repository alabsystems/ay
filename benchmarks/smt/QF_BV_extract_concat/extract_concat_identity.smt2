; Andrew Yates <andrewyates.name@gmail.com>
; Identity: concat(extract[n-1:m], extract[m-1:0]) = x
(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 32))

; Split and rejoin: should equal original
(assert (= (concat ((_ extract 31 16) x) ((_ extract 15 0) x)) x))
(assert (= (concat ((_ extract 31 24) x) (concat ((_ extract 23 16) x) (concat ((_ extract 15 8) x) ((_ extract 7 0) x)))) x))

; Constrain x to verify
(assert (= x #xDEADBEEF))

(check-sat)
(exit)
