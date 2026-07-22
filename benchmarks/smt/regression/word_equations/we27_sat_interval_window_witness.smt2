; Stage 3b regression (A3): the window 9 ≤ |x| ≤ 11 defeats pivot
; enumeration (2^9+2^10+2^11 candidates), but interval-guided Nielsen
; search finds x = (ab)^5 directly.
; before: unknown   after: sat (x = "ababababab")   z3 4.16.0: sat
(set-logic QF_SLIA)
(declare-const x String)
(assert (= (str.++ x "ab") (str.++ "ab" x)))
(assert (>= (str.len x) 9))
(assert (<= (str.len x) 11))
(check-sat)
