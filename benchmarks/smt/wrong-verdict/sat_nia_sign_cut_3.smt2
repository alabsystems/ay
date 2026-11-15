; Satisfiable QF_NIA problem on which AY main b1c1f8f201 (build 10522) answers
; `unsat` in both postures (default and --z3-mode) at -T:5. z3 5.1.0: sat.
; z3 model: w = -13, x = -7, z = -40  (3w = -39 = z+1; 5x - 2z = 45; x*z = 280).
;
; Same mechanism as sat_nia_sign_cut_1, reached after a branch-and-bound split
; on w: in the surviving branch the stale LRA model has x = 1/5, the NIA loop
; accumulates contradictory sign cuts x >= 0 (iteration 1) and x <= 0
; (iteration 2) in one tentative scope plus a rounding pin x = 0, and the LIA
; refutes x in [0, 0] against x = 5 (mod 6) in `check_modular_for_var`.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const z Int)
(declare-const w Int)
(assert (= (* 3 w) (+ z 1)))
(assert (= (- (* 5 x) (* 2 z)) 45))
(assert (<= x 1))
(assert (>= z (- 2000)))
(assert (>= (* x z) 1))
(assert (<= (* x z) 400))
(check-sat)
