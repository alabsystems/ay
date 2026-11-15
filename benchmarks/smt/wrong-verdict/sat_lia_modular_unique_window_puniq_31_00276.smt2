; Satisfiable QF_LIA problem on which AY main 8b71d73999 answers `unsat` in
; both postures (main 6818b5d067: `sat` in --z3-mode, `unknown` default).
; z3 5.1.0: sat. Planted model: x0=162 x1=14 x2=-2 x3=8 x4=8.
;
; puniq_31_00276 of the 2026-09-23 linear hunt (gen_planted.py puniq, seed 31;
; also a full-budget file of the differential gate). Mechanism: the modular
; check's "unique value excluded by a disequality" conflict kept only the
; TRUE-valued asserted literals, but the bound window [148, 151] that made
; x0 = 150 the only residue came from the NEGATED atoms (not (<= x0 147)) and
; (not (>= x0 152)); the learned clause read "the equalities force x0 = 150",
; which is false. Fixed by citing every asserted literal, both polarities
; (ay-lia/src/modular_bounds.rs, modular.rs). `sat` or `unknown` is
; acceptable; `unsat` is the regression.
(set-logic QF_LIA)
(set-info :status sat)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(assert (or (> x0 151) (and (not (<= x0 147)) (not (>= x0 152)))))
(assert (= (* 2 x0) (+ (* 8 x3) (* 16 x1) (* (- 16) x2) 4)))
(assert (= (+ (* (- 4) x0) (* 9 x4) (* 9 x3) (* (- 2) x2) (- 8)) (- 508)))
(assert (<= x2 3))
(assert (distinct x0 150))
(assert (<= (- 3) x2))
(assert (<= x4 12))
(assert (not (< x0 145)))
(assert (<= x0 162))
(assert (<= 8 x4))
(check-sat)
