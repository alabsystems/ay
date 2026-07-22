; Stage 3a regression (A3): boundary-character pruning. x·y = y·x with both
; sides provably non-empty forces equal first characters, but x ∈ (ab)+
; starts with 'a' while y ∈ (ba)+ starts with 'b'.
; before: unknown   after: unsat   z3 4.16.0: unsat
(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x y) (str.++ y x)))
(assert (str.in_re x (re.+ (str.to_re "ab"))))
(assert (str.in_re y (re.+ (str.to_re "ba"))))
(check-sat)
