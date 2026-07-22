; Stage 2 regression (A3): forced-length derivation (2|x| = 4) + re.loop
; unrolling — x must be "aa" but the loop demands at least 3 repetitions.
; before: unknown   after: unsat   z3 4.16.0: unsat
(set-logic QF_S)
(declare-const x String)
(assert (= (str.++ x x) "aaaa"))
(assert (str.in_re x ((_ re.loop 3 5) (str.to_re "a"))))
(check-sat)
