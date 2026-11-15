; Satisfiable QF_NIA problem on which AY main b1c1f8f201 (build 10522) answers
; `unsat` in both postures (default and --z3-mode) at -T:5. z3 5.1.0: sat.
; z3 model: x = -1, w = -2, z = -7  (3w = -6 = z+1; 2x + z = -9; x*z = 7).
;
; Same mechanism as sat_nia_sign_cut_1: the LRA model after the LIA's
; direct-enumeration Sat is x = -9/2, z = 0; the NIA loop injects the sign cut
; x <= 0 and rounds x to the pin -5, McCormick rows are derived from those
; tentative bounds, and the next LIA check refutes x in [-5, -5] against the
; Diophantine congruence x = 2 (mod 3) in `check_modular_for_var` without
; checking that the bounds' reasons are asserted atoms.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const z Int)
(declare-const w Int)
(assert (= (* 3 w) (+ z 1)))
(assert (= (+ (* 2 x) z) (- 9)))
(assert (<= z 1))
(assert (>= z (- 2000)))
(assert (>= (* x z) 1))
(assert (<= (* x z) 400))
(check-sat)
