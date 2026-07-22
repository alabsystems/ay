; Stage 2 regression (A3): negative membership filters the x = "" leaf; the
; bounded canonical-revisit search surfaces the x = "ab" solution.
; before: unknown   after: sat   z3 4.16.0: sat
(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x "ab") (str.++ "ab" x)))
(assert (not (str.in_re x (str.to_re ""))))
(assert (= y (str.++ x "b")))
(check-sat)
