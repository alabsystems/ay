; Stage 3a regression (A3): var-var propagation must not over-prune — the
; same shape as we29 with a compatible target regex stays sat (x = "ab").
; before: sat   after: sat   z3 4.16.0: sat
(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.+ (str.to_re "a"))))
(assert (str.in_re z (re.+ (str.to_re "b"))))
(assert (str.in_re x (re.* (str.to_re "ab"))))
(check-sat)
