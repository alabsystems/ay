; expected: unsat
; QF_BV — a bit-vector cannot equal two distinct constants.
(set-logic QF_BV)
(set-info :status unsat)
(declare-const x (_ BitVec 8))
(assert (= x #x01))
(assert (= x #x02))
(check-sat)
