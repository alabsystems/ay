; #nested-array-quarantine-datatype-fields
;
; Record-boxed twin of repros/abv-nested-array-quantified-unsat-quarantine.smt2
; (Ultimate Automizer, SV-COMP 2019; CC BY 4.0,
;  https://creativecommons.org/licenses/by/4.0/). The only change: the inner
; (Array (_ BitVec 32) (_ BitVec 32)) of |c_#memory_int| is the single field
; `cells` of the declared record `Row`, every inner read goes through that
; selector, and the logic is ALL because ABV has no datatypes. A one-field,
; one-constructor record is isomorphic to its field, so this is the same query.
;
; z3 4.8.12: unsat. AY at ad60a0707 published `unsat`
; (`unsat_admission=discharged-trust`, a fresh executor re-running the same
; combination) behind a bare `(step t0 (cl) :rule hole)`, while the directly
; nested original is withheld: `StaticFeatures::has_nested_arrays` read the
; declared carrier `Row` as an opaque sort. It now resolves declared fields, so
; both forms degrade to `unknown` with phase `array-combination-quarantine`.
; Pinned by `executor::check_sat::nested_array_quarantine::tests::
;  a_record_boxed_nested_array_unsat_without_authority_is_quarantined`.
(set-logic ALL)
(set-info :status unsat)
(declare-datatype Row ((mk_row (cells (Array (_ BitVec 32) (_ BitVec 32))))))
(declare-fun |c_#memory_int| () (Array (_ BitVec 32) Row))
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
(assert (= |c_main_#t~mem2_primed| (select (cells (select |c_#memory_int| |c_main_~#b~0.base|)) (bvadd (bvmul (_ bv4 32) c_main_~i~0) |c_main_~#b~0.offset|))))
(assert (not (= |c_main_~#b~0.base| |c_main_~#a~0.base|)))
(assert (= (bvadd (select (cells (select |c_#memory_int| |c_main_~#b~0.base|)) |c_main_~#b~0.offset|) (_ bv4294967295 32)) (_ bv0 32)))
(assert (= |c_main_~#a~0.offset| (_ bv0 32)))
(assert (bvsge (select (cells (select |c_#memory_int| |c_main_~#a~0.base|)) |c_main_~#a~0.offset|) (_ bv0 32)))
(assert (= c_main_~i~0 (_ bv0 32)))
(assert (not (and (exists ((main_~i~0 (_ BitVec 32)) (|main_~#b~0.base| (_ BitVec 32)) (|main_~#b~0.offset| (_ BitVec 32))) (let ((.cse0 (cells (select |c_#memory_int| |main_~#b~0.base|)))) (and (not (= |main_~#b~0.base| |c_main_~#a~0.base|)) (= (bvadd (select .cse0 |main_~#b~0.offset|) (_ bv4294967295 32)) (_ bv0 32)) (= (bvadd (select .cse0 (bvadd (bvmul (_ bv4 32) main_~i~0) |main_~#b~0.offset|)) (_ bv4294967295 32)) (_ bv0 32))))) (= |c_main_~#a~0.offset| (_ bv0 32)) (bvsge (select (cells (select |c_#memory_int| |c_main_~#a~0.base|)) |c_main_~#a~0.offset|) (_ bv0 32)))))
(check-sat)
(exit)
