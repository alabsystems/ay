; Andrew Yates <andrewyates.name@gmail.com>
; Nested extract operations
(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 16))

; Extract from extract: (extract 1 0 (extract 7 0 x))
(assert (= ((_ extract 1 0) ((_ extract 7 0) x)) #b01))
(assert (= ((_ extract 7 4) ((_ extract 15 8) x)) #b1010))

(check-sat)
(exit)
