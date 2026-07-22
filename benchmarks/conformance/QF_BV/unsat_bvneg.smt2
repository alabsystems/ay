(set-info :status unsat)
(set-logic QF_BV)
; For 8-bit, bvneg(x) + x = 0 always. Assert it equals non-zero.
(declare-const x (_ BitVec 8))
(assert (= x #x01))
(assert (distinct (bvadd (bvneg x) x) #x00))
(check-sat)
(exit)
