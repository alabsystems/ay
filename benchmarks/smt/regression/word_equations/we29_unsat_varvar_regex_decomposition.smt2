; Stage 3a regression (A3): the var-var split x = y·z PROPAGATES x's
; membership onto the concatenation (previously dropped), and the leaf
; emptiness product refutes a+ · b+ ⊆ (aa)* (a 'b' can never appear).
; before: unknown   after: unsat
; z3 4.16.0: TIMEOUT (>55s) — verdict cross-checked with cvc5 1.x: unsat
(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (str.in_re y (re.+ (str.to_re "a"))))
(assert (str.in_re z (re.+ (str.to_re "b"))))
(assert (str.in_re x (re.* (str.to_re "aa"))))
(check-sat)
