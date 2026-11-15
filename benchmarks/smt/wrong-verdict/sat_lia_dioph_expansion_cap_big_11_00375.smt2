; Satisfiable QF_LIA problem on which AY main (.. 8b71d73999) answers `unsat`
; in both postures (default and --z3-mode). z3 5.1.0: sat, model
;   x0 = 27514168736550961562161003932001298170
;   x1 = -6406141616532337283524198406
;   x2 = 0
;
; D3 of the 2026-09-23 hunt (linear/wit/auto/big_11_00375/min.smt2, generator
; gen_sem.py big). Same mechanism as sat_lia_dioph_expansion_cap_pbig_21_00085:
; the 100-pop expansion cap returned a partial sum whose coefficient GCD gave
; a false modulus, here through the `mod` encoding's quotient and remainder
; variables. `sat` or `unknown` is acceptable; `unsat` is the regression.
(set-logic QF_LIA)
(set-info :status sat)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (= (+ (* 9223372036854775809 x1) (* 2147483648 x0) 10000000000000000004) 13835058055282163710))
(assert (= (mod (+ (* 10000000000000000004 x0) (* (- 7) x1) (- 13835058055282163709)) 9223372036854775810) 3))
(assert (<= (- 79228162514264337593543950343) x1))
(assert (<= x1 18446744073709551614))
(check-sat)
