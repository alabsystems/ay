; #cause-b-parsed-gate regression (reduced from
; QF_DT/20230720-blocksworld/blocksworld_from_1_0_2_to_1_0_2_negated_goal_bmc_1.smt2).
;
; UNSAT: under `c` we get (top s)=A and (top t)=B; under (not c) we get
; (top s)=B and (top t)=A. Either way `(= (top s) (top t))` is false.
; Independently confirmed unsat by z3 4.x and cvc5 1.3.0.
;
; This shape combines BOTH producers of unauthorized proof leaves:
;   * the bool-ITE assertions are AUTHORED, but `rewrite_assertion_bool_ites`
;     replaces each in place with `(and (=> c t) (=> (not c) e))`, which
;     `FlattenAnd` then splits — so the proof assumes conjuncts the frozen
;     obligation never contained;
;   * the DT lazy lane appends selector/tester axioms over `top`/`rest`, which
;     no rewrite provenance can ever authorize.
;
; Before the gate split, with the parsed-assertion prefix dropped (`--z3-mode`,
; `--no-proof`, competition mode) AY computed the refutation and then discarded
; it: "step t0 assumes term t20 outside the supplied problem obligation" -> the
; published answer was `unknown`.
(set-logic QF_DT)
(set-info :status unsat)
(declare-datatypes ((E 0)) (((A) (B))))
(declare-datatypes ((T 0)) (((stack (top E) (rest T)) (empty))))
(declare-fun s () T)
(declare-fun t () T)
(declare-fun c () Bool)
(assert (ite c (= s (stack A empty)) (= s (stack B empty))))
(assert (ite c (= t (stack B empty)) (= t (stack A empty))))
(assert (= (top s) (top t)))
(check-sat)
