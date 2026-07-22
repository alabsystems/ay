; Stage 2 regression (A3): regex-derivative pruning closes the Nielsen cycle.
; x·a = a·x forces x ∈ a*, but x ∈ a*·b must end in 'b'.
; before: unknown   after: unsat   z3 4.16.0: unsat
(set-logic QF_S)
(declare-const x String)
(assert (= (str.++ x "a") (str.++ "a" x)))
(assert (str.in_re x (re.++ (re.* (str.to_re "a")) (str.to_re "b"))))
(check-sat)
