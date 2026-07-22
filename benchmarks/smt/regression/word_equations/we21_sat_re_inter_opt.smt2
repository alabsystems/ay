; Stage 2 regression (A3): intersection derivatives guide the search to the
; unique non-empty witness x = "aa".
; before: unknown   after: sat   z3 4.16.0: sat
(set-logic QF_S)
(declare-const x String)
(assert (= (str.++ "a" x) (str.++ x "a")))
(assert (str.in_re x (re.inter (re.* (re.range "a" "b")) (re.opt (str.to_re "aa")))))
(assert (not (= x "")))
(check-sat)
