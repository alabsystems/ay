; expected: sat
; QF_BV — 8-bit addition with a solution.
(set-logic QF_BV)
(set-info :status sat)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvadd x y) #x0a))
(assert (= x #x03))
(check-sat)
