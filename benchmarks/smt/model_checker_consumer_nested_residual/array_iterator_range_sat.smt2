; Producer-derived authored control, NOT a captured MODEL_CHECKER_CONSUMER export.
; Producer: origin/main 22278991c4d8e73189117c1f601ca1f4a89d6054.
; model-checker-consumer-compiler/src/codegen_ay/chc/decl/codegen_types_adt_sort.rs:
; 140-156 constructs IntoIter(inner: PolymorphicIter(alive: IndexRange,data)).
; model-checker-consumer-codegen-types/src/names/sort_constructors.rs:155-159 gives
; IndexRange(start:BV64,end:BV64). Actual nested field projections are in
; chc/stub_codegen/stubs_iterators_vec_array.rs:126-139 under codegen_ay.
; The outer array and endpoint assignments below are authored W5 controls.
; Expected SAT: start/end share one nested IndexRange; different cells may
; contain different ranges. This is not an iterator-implementation proof.
(set-logic ALL)
(set-info :status sat)
(declare-datatype IndexRange
  ((IndexRange_mk (fld_start (_ BitVec 64)) (fld_end (_ BitVec 64)))))
(declare-datatype PolymorphicIter
  ((PolymorphicIter_mk (fld_alive IndexRange)
    (fld_data (Array (_ BitVec 64) (_ BitVec 8))))))
(declare-datatype IntoIter ((IntoIter_mk (fld_inner PolymorphicIter))))
(declare-const a (Array (_ BitVec 64) IntoIter))
(assert (= (fld_start (fld_alive (fld_inner (select a (_ bv64 64)))))
           (_ bv33 64)))
(assert (= (fld_end (fld_alive (fld_inner (select a (_ bv64 64)))))
           (_ bv65 64)))
(assert (= (fld_start (fld_alive (fld_inner (select a (_ bv65 64)))))
           (_ bv9 64)))
(assert (= (fld_end (fld_alive (fld_inner (select a (_ bv65 64)))))
           (_ bv12 64)))
(check-sat)
(exit)
