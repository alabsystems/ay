; Unsatisfiable QF_UFLIA problem on which AY main (fbb541002a's successors
; from 80fe296b26 through b288f5e6f5) PANICS in the default posture
; ("internal solver error", published `unknown`):
;   index out of bounds: the len is 77 but the index is 80
;   at TermStore::mk_eq_depth_mode <- mod_div_elim::eliminate_int_mod_div_impl
;   <- ... <- check_sat_with_authority <- discharge_trust_steps_for_certification
; z3 5.1.0: unsat; AY --z3-mode: unsat. By hand: x0 = x1 - 7 and
; x0 = (mod x1 3) in {0,1,2} force x1 in {7,8,9}, where (mod x1 3) is
; 1, 2, 0 against x0 = 0, 1, 2 -- unsat whatever the zero divisors denote.
;
; The differential gate's uf-arith g6_100000/g6_100167 (full budget). Same
; hazard as A-UFA-g6-div0 (unsat_uflia_div0_reconfirm_g6_100000.smt2), a
; different certification leg: the forged-UNSAT guard's re-solve compacted
; its cloned arena, relabelling every held id but not the digits of the
; zero-divisor variable `__ay_zerodiv_div_80`, and the nested solve's
; `collect_zero_divisor_vars` decoded the stale index. Fixed where the ids
; are relabelled: `Context::compact_terms_for_derived_query` now refuses
; (untouched) an arena whose internal names spell term ids, for every caller.
; `unsat` or `unknown` is acceptable; an abort or `sat` is the regression.
(set-logic QF_UFLIA)
(set-info :status unsat)
(set-option :produce-models true)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun f (Int) Int)
(assert (= (mod x1 3) x0))
(assert (<= (div x1 0) (+ x1 (+ 1 x1))))
(assert (or (not (= (+ x0 (- 7)) (+ x1 1))) (<= (mod 3 0) (mod x1 (- 3))) (< (mod x1 (- 3)) (div x1 (- 3)))))
(assert (or (< x0 (ite (= (- 7) x0) x1 1)) (<= x1 x1)))
(assert (= x0 (ite (= (abs 1) 0) x1 (+ x1 (- 7)))))
(assert (= (div (mod x1 2) 0) x0))
(check-sat)
(exit)
