; Satisfiable QF_NIA problem on which AY main b1c1f8f201 (build 10522) answers
; `unsat` in both postures (default and --z3-mode) at -T:5. z3 5.1.0: sat.
; z3 model: w = -8, x = -1, z = -25  (3w = -24 = z+1; 5x - 2z = 45; x*z = 25).
;
; sat_nia_sign_cut_3 with the wide range on x instead of z: here the tentative
; SIGN CUT alone produces the wrong verdict (with sign-cut injection disabled
; the file answers sat; with the rounding pin disabled it still answers
; unsat), reached at the "Only exact lemmas were used" site of
; nia/src/check_loop.rs at iteration 1 through `check_modular_for_var`
; reading the guessed bound on x as a fact.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const z Int)
(declare-const w Int)
(assert (= (* 3 w) (+ z 1)))
(assert (= (- (* 5 x) (* 2 z)) 45))
(assert (<= x 1))
(assert (>= x (- 1000)))
(assert (>= (* x z) 1))
(assert (<= (* x z) 400))
(check-sat)
