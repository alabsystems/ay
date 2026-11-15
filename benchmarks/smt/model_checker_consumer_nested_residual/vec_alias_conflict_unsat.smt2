; Producer-derived authored control, NOT a captured MODEL_CHECKER_CONSUMER export.
; Producer: origin/main 22278991c4d8e73189117c1f601ca1f4a89d6054.
; Full CHC record shapes: model-checker-consumer-codegen-types/src/names/
; sort_constructors.rs:101-124; nested read: model-checker-consumer-compiler/src/codegen_ay/
; chc/stub_codegen/stubs_iterators_vec.rs:298-305.
; Outer arrays, aliases and the arithmetic index are authored W5 controls.
; Expected UNSAT: aliases at equal evaluated indices denote the same whole
; record, so the same nested len cannot be both 65 and 66.
(set-logic ALL)
(set-info :status unsat)
(declare-datatype Vec_bv8
  ((Vec_bv8_mk (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
    (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8))))))
(declare-datatype VecIntoIter_bv8
  ((VecIntoIter_bv8_mk (fld_vec Vec_bv8) (fld_pos (_ BitVec 64)))))
(declare-const a (Array (_ BitVec 64) VecIntoIter_bv8))
(declare-const b (Array (_ BitVec 64) VecIntoIter_bv8))
(assert (= a b))
(assert (= (fld_len (fld_vec (select a (_ bv64 64)))) (_ bv65 64)))
(assert (= (fld_len (fld_vec (select b (bvadd (_ bv63 64) (_ bv1 64)))))
           (_ bv66 64)))
(check-sat)
(exit)
