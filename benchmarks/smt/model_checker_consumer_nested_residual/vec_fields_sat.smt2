; Producer-derived authored control, NOT a captured MODEL_CHECKER_CONSUMER export.
; Producer: origin/main 22278991c4d8e73189117c1f601ca1f4a89d6054.
; model-checker-consumer-codegen-types/src/names/sort_constructors.rs:101-124 defines
; full Vec(ptr,len,cap,data) and CHC VecIntoIter(vec,pos).
; model-checker-consumer-compiler/src/codegen_ay/chc/stub_codegen/stubs_iterators_vec.rs:
; 298-305 reads fld_len(fld_vec(iter)). types.rs:1367-1392 in
; model-checker-consumer-codegen-types retains array-carrying records as array elements.
; The outer array, values and alias below are authored to exercise W5.
; Expected SAT: one concrete record at each index satisfies all nested fields.
; No assertion about Rust iterator execution or AY's runtime result is made.
(set-logic ALL)
(set-info :status sat)
(declare-datatype Vec_bv8
  ((Vec_bv8_mk (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
    (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8))))))
(declare-datatype VecIntoIter_bv8
  ((VecIntoIter_bv8_mk (fld_vec Vec_bv8) (fld_pos (_ BitVec 64)))))
(declare-const a (Array (_ BitVec 64) VecIntoIter_bv8))
(declare-const b (Array (_ BitVec 64) VecIntoIter_bv8))
(assert (= a b))
(assert (= (fld_len (fld_vec (select a (_ bv64 64)))) (_ bv65 64)))
(assert (= (fld_cap (fld_vec (select b (bvadd (_ bv63 64) (_ bv1 64)))))
           (_ bv65 64)))
(assert (= (fld_pos (select a (_ bv64 64))) (_ bv33 64)))
(assert (= (fld_len (fld_vec (select b (_ bv65 64)))) (_ bv9 64)))
(check-sat)
(exit)
