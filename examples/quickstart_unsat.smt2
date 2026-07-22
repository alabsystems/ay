(set-info :status unsat)
(set-logic QF_LIA)

(declare-const x Int)
(declare-const y Int)

; x is strictly greater than y, yet x + 1 is claimed to be at most y:
; no integers can satisfy both, so the problem is unsatisfiable.
(assert (> x y))
(assert (<= (+ x 1) y))

(check-sat)
