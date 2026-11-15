; Unsatisfiable QF_UFLIA problem on which AY main (.. 8b71d73999) PANICS in the
; default posture ("internal solver error", published `unknown`):
;   index out of bounds: the len is 55 but the index is 59
;   at TermStore::mk_eq_depth_mode <- mod_div_elim::eliminate_int_mod_div_impl
;   <- ... <- reconfirms_unsat_within <- discharge_trust_steps_for_certification
; z3 5.1.0: unsat; AY --z3-mode: unsat.
;
; A-UFA-g6-div0 of the 2026-09-23 hunt (uf-arith/witness/panic/g6_100000.min).
; Mechanism: the certification re-solve clones the context and compacts its
; term arena, relabelling every id; the zero-divisor variable
; `__ay_zerodiv_div_59` spells its dividend's OLD id in its name, which no
; relabelling reaches, and the nested solve's `collect_zero_divisor_vars`
; decoded it. Fixed by re-solving such an arena unpruned
; (ay-dpll/src/executor/unsat_cert.rs, the veto the checked-isolated probe
; already applies). `unsat` or `unknown` is acceptable; an abort or `sat` is
; the regression.
(set-logic QF_UFLIA)
(set-info :status unsat)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun f (Int) Int)
(assert (= x0 (abs (- 6))))
(assert (or (< (mod x1 1) (div (- 4) 0)) (distinct (mod x0 2) (- x1 x0)) (not (<= (+ 6 (- 7)) (abs x0)))))
(assert (or (not (= x0 (div (- 2) (- 2)))) (<= (- (+ x1 3) (f x1)) (- 1)) (not (< (ite (distinct x1 (- x1 x0)) x1 x0) (div (div x1 3) 0)))))
(assert (= (mod (f x0) (- 2)) x0))
(check-sat)
