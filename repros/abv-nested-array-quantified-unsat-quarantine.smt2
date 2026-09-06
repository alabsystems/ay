; #nested-array-quarantine-quantified
;
; Unit-split form of
;   benchmarks/smtlib-all/ABV/non-incremental__ABV__20190429-
;   UltimateAutomizerSvcomp2019__standard_running_true-unreach-call.i_3.smt2
; (Ultimate Automizer, SV-COMP 2019; CC BY 4.0,
;  https://creativecommons.org/licenses/by/4.0/). The only change is that the
; two `(assert (and c1 .. cn))` assertions are written as bare conjunct
; asserts, which is an equivalent rewrite and is what makes AY's E-matching
; treat the negated `exists` as an entailed forall.
;
; z3 4.16.0: unsat. AY: finds the refutation
; (`CERT/classify: result=Unsat em_added=true`) and then withholds it, because
; the reconstructed proof is a bare `(step t0 (cl) :rule trust)` — no rung of
; `nested_array_unsat_has_current_authority` can back it, so
; `quarantine_unverified_nested_array_unsat` degrades to `unknown` with phase
; `array-combination-quarantine`. Pinned by
; `executor_tests::array_soundness::
;  test_nested_array_quantified_instance_unsat_without_authority_is_quarantined`.
(set-info :smt-lib-version 2.6)
(set-logic ABV)
(set-info :status unsat)
(declare-fun |c_#memory_int| () (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32))))
(declare-fun |c_main_#t~mem2_primed| () (_ BitVec 32))
(declare-fun |c_main_#t~short3| () Bool)
(declare-fun |c_main_#t~short3_primed| () Bool)
(declare-fun |c_main_~#a~0.base| () (_ BitVec 32))
(declare-fun |c_main_~#a~0.offset| () (_ BitVec 32))
(declare-fun |c_main_~#b~0.base| () (_ BitVec 32))
(declare-fun |c_main_~#b~0.offset| () (_ BitVec 32))
(declare-fun c_main_~i~0 () (_ BitVec 32))
(assert (let ((.cse0 (= |c_main_#t~mem2_primed| (_ bv0 32)))) (or (and |c_main_#t~short3_primed| .cse0) (and (not .cse0) (not |c_main_#t~short3_primed|)))))
(assert |c_main_#t~short3|)
(assert (= |c_main_#t~mem2_primed| (select (select |c_#memory_int| |c_main_~#b~0.base|) (bvadd (bvmul (_ bv4 32) c_main_~i~0) |c_main_~#b~0.offset|))))
(assert (not (= |c_main_~#b~0.base| |c_main_~#a~0.base|)))
(assert (= (bvadd (select (select |c_#memory_int| |c_main_~#b~0.base|) |c_main_~#b~0.offset|) (_ bv4294967295 32)) (_ bv0 32)))
(assert (= |c_main_~#a~0.offset| (_ bv0 32)))
(assert (bvsge (select (select |c_#memory_int| |c_main_~#a~0.base|) |c_main_~#a~0.offset|) (_ bv0 32)))
(assert (= c_main_~i~0 (_ bv0 32)))
(assert (not (and (exists ((main_~i~0 (_ BitVec 32)) (|main_~#b~0.base| (_ BitVec 32)) (|main_~#b~0.offset| (_ BitVec 32))) (let ((.cse0 (select |c_#memory_int| |main_~#b~0.base|))) (and (not (= |main_~#b~0.base| |c_main_~#a~0.base|)) (= (bvadd (select .cse0 |main_~#b~0.offset|) (_ bv4294967295 32)) (_ bv0 32)) (= (bvadd (select .cse0 (bvadd (bvmul (_ bv4 32) main_~i~0) |main_~#b~0.offset|)) (_ bv4294967295 32)) (_ bv0 32))))) (= |c_main_~#a~0.offset| (_ bv0 32)) (bvsge (select (select |c_#memory_int| |c_main_~#a~0.base|) |c_main_~#a~0.offset|) (_ bv0 32)))))
(check-sat)
(exit)
