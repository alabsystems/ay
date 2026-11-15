; Producer-derived authored control, NOT a captured MODEL_CHECKER_CONSUMER export.
; Producer: origin/main 22278991c4d8e73189117c1f601ca1f4a89d6054.
; Full CHC record shapes: model-checker-consumer-codegen-types/src/names/
; sort_constructors.rs:101-124; nested read: model-checker-consumer-compiler/src/codegen_ay/
; chc/stub_codegen/stubs_iterators_vec.rs:298-305.
; The outer array and conflicting assignments are authored W5 controls.
; Expected UNSAT: the exact parent Vec has len=65, not len=66.
; Completing an unpinned sibling must never replace this ancestor value.
(set-logic ALL)
(set-info :status unsat)
(declare-datatype Vec_bv8
  ((Vec_bv8_mk (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
    (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8))))))
(declare-datatype VecIntoIter_bv8
  ((VecIntoIter_bv8_mk (fld_vec Vec_bv8) (fld_pos (_ BitVec 64)))))
(declare-const a (Array (_ BitVec 64) VecIntoIter_bv8))
(assert (= (fld_vec (select a (_ bv64 64)))
           (Vec_bv8_mk (_ bv4096 64) (_ bv65 64) (_ bv65 64)
             ((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv7 8)))))
(assert (= (fld_len (fld_vec (select a (_ bv64 64)))) (_ bv66 64)))
(check-sat)
(exit)
