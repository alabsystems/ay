; Andrew Yates <andrewyates.name@gmail.com>
; Wide bitvector extract operations (64-bit)
(set-logic QF_BV)
(set-info :status sat)

(declare-fun x () (_ BitVec 64))

; Multiple overlapping extracts
(assert (= ((_ extract 63 32) x) #xCAFEBABE))
(assert (= ((_ extract 31 0) x) #xDEADBEEF))
(assert (= ((_ extract 47 16) x) #xBABEDEAD))

(check-sat)
(exit)
