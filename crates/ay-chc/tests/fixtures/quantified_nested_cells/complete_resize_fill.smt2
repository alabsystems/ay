; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; AUTHORED SOURCE COMPOSITION, NOT A COMPILER-EXPORTED HARNESS.
; Source: MODEL_CHECKER_CONSUMER origin/main 22278991c4d8e73189117c1f601ca1f4a89d6054.
; types.rs::flatten_dt_array_element preserves a Vec cell's inner data array.
; names/sort_constructors.rs::vec_fields supplies ptr,len,cap,data.
; chc/call/codegen_call_vec_ops/resize.rs::quantified_resize_growth_array
; supplies each prefix/suffix relation and the growth ITE below. The entailed
; 32 low-index ground hints are omitted; both queried indices exceed that range.
; This composes inner scalar resize with outer record-cell resize. It asserts
; a bad read, not an AY proof result. Expected reference verdict: unsat.
(set-logic ALL)
(declare-datatypes ((Inner 0) (Outer 0))
  (((mk_inner (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
                   (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8)))))
   ((mk_outer (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
                   (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) Inner))))))
(declare-const inner_before (Array (_ BitVec 64) (_ BitVec 8)))
(declare-const inner_fresh (Array (_ BitVec 64) (_ BitVec 8)))
(declare-const outer_before (Array (_ BitVec 64) Inner))
(declare-const outer_fresh (Array (_ BitVec 64) Inner))
(declare-const inner_old (_ BitVec 64))
(declare-const inner_new (_ BitVec 64))
(declare-const outer_old (_ BitVec 64))
(declare-const outer_new (_ BitVec 64))
(declare-const fill (_ BitVec 8))
(declare-const cell Inner)
(declare-const result Outer)
(declare-const outer_index (_ BitVec 64))
(declare-const inner_index (_ BitVec 64))
(assert (= inner_old (_ bv2 64)))
(assert (= inner_new (_ bv68 64)))
(assert (= outer_old (_ bv2 64)))
(assert (= outer_new (_ bv65 64)))
(assert (= fill #x07))
(assert (forall ((j (_ BitVec 64)))
  (and (=> (bvult j inner_old) (= (select inner_fresh j) (select inner_before j)))
       (=> (and (bvuge j inner_old) (bvult j inner_new))
           (= (select inner_fresh j) fill)))))
(assert (= cell (mk_inner (_ bv101 64) inner_new inner_new
  (ite (bvult inner_old inner_new) inner_fresh inner_before))))
(assert (forall ((i (_ BitVec 64)))
  (and (=> (bvult i outer_old) (= (select outer_fresh i) (select outer_before i)))
       (=> (and (bvuge i outer_old) (bvult i outer_new))
           (= (select outer_fresh i) cell)))))
(assert (= result (mk_outer (_ bv202 64) outer_new outer_new
  (ite (bvult outer_old outer_new) outer_fresh outer_before))))
(assert (= outer_index (_ bv33 64)))
(assert (= inner_index (_ bv64 64)))
(assert (and (bvuge outer_index outer_old) (bvult outer_index (fld_len result))
             (bvuge inner_index inner_old)
             (bvult inner_index (fld_len (select (fld_data result) outer_index)))))
(assert (not (= (select (fld_data (select (fld_data result) outer_index)) inner_index) fill)))
(check-sat)
