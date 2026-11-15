; Satisfiable QF_LIA problem on which AY main (.. 8b71d73999) answers `unsat`
; in both postures (default and --z3-mode). z3 5.1.0: sat, model
;   x0 = 20920221290197706900972355784227684355
;   x1 = -10209966466665546402323682051478709
;   x2 = -1267650600228229401496703205381
;   x3 = -19941340755306147535296091138889
;
; D3 of the 2026-09-23 hunt (linear/wit/pbig_21_00085/min.smt2, generator
; gen_planted.py pbig). Mechanism: expanding a Diophantine substitution walked
; the substitution DAG as a tree and stopped after 100 worklist pops,
; returning the PARTIAL sum as the expansion; the partial sum's coefficient
; GCD exceeded the true one (1), so the modular check derived a false
; `var = r (mod g)` and reported every asserted literal as a conflict. Fixed
; by an exact, memoized expansion that is complete or absent
; (ay-lia/src/dioph/expansion.rs). `sat` or `unknown` is acceptable; `unsat`
; is the regression.
(set-logic QF_LIA)
(set-info :status sat)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(assert (= (+ (* (- 4611686018427387903) x3) (* (- 18446744073709551615) x1) (* (- 9007199254740991) x0) (* (- 4294967295) x2)) 5905686471349737029546786948242595643392))
(assert (<= (- 1267650600228229401496703205381) x2))
(assert (<= x2 (- 1267650600228229401496703205377)))
(assert (= (+ (* 9007199254740993 x1) (* (- 4611686018427387903) x3) 0) 461168601842719447477662793894202441730))
(check-sat)
