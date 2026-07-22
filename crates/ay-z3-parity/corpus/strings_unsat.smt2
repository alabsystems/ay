; expected: unsat
; QF_S — a length constraint incompatible with the concatenation.
(set-logic QF_S)
(set-info :status unsat)
(declare-const s String)
(assert (= (str.++ s "bar") "foobar"))
(assert (= (str.len s) 5))
(check-sat)
