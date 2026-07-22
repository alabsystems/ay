; Stage 2 regression (A3): regex witnesses for commuting variables —
; x ∈ (ab)+ and y = (ab)^2 commute as powers of "ab".
; before: unknown   after: sat   z3 4.16.0: sat
(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x y) (str.++ y x)))
(assert (str.in_re x (re.++ (str.to_re "ab") (re.* (str.to_re "ab")))))
(assert (str.in_re y ((_ re.loop 2 2) (str.to_re "ab"))))
(check-sat)
