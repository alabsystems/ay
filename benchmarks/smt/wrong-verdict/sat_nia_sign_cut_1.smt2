; Satisfiable QF_NIA problem on which AY main b1c1f8f201 (build 10522) answers
; `unsat` in both postures (default and --z3-mode) at -T:5. z3 5.1.0: sat.
; z3 model: x = -23, y = -46, z = -15  (2x = y; 3z = -45 = y+1; x*z = 345).
;
; Mechanism (measured with an env-gated probe build, 2026-09-21): the LIA's
; direct enumeration answers Sat while leaving the LRA model fractional
; (x = 0, z = 1/3); the NIA refinement loop then injects a tentative sign cut
; z >= 0 and an integer-rounding pin z = 0 from that stale model, McCormick
; rows are built on those bounds (no tangent plane, so
; `used_tangent_approximation` stays false), and the next LIA check reads the
; tentative bounds z in [0, 0] as facts in `check_modular_for_var`
; (modular_bounds.rs) -- no integer in [0, 0] is odd, so it returns the full
; asserted set as a conflict. check_loop.rs then returns UNSAT at the
; "Only exact lemmas were used" site. Without the tentative scope the same
; LIA check is Sat (sign-cut/pin-dependent refutation).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (= (* 2 x) y))
(assert (= (* 3 z) (+ y 1)))
(assert (>= y (- 2000)))
(assert (<= y 1))
(assert (>= (* x z) 1))
(assert (<= (* x z) 400))
(check-sat)
