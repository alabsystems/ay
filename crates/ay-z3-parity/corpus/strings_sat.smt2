; expected: sat
; QF_S — string concatenation with a solution.
(set-logic QF_S)
(set-info :status sat)
(declare-const s String)
(assert (= (str.++ s "bar") "foobar"))
(check-sat)
