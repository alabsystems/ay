; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; AUTHORED SOURCE COMPOSITION, NOT A COMPILER-EXPORTED HARNESS.
; MODEL_CHECKER_CONSUMER 22278991c4d8e73189117c1f601ca1f4a89d6054:
; chc/call/codegen_call_virtual_inline/projected_assign_helpers.rs::
; update_inline_value_expr recursively selects a field/cell, updates it, then
; rebuilds the record or stores the updated cell back into the original array.
; Update (outer,inner)=(33,64); read the off-diagonal (64,33). The complete
; outer store preserves that other row, including all its inner-array cells.
; Expected reference verdict: unsat. No claim about AY runtime behavior.
(set-logic ALL)
(declare-datatypes ((Inner 0) (Outer 0))
  (((mk_inner (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
                   (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8)))))
   ((mk_outer (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
                   (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) Inner))))))
(declare-const before Outer)
(declare-const after Outer)
(declare-const old_cell Inner)
(declare-const new_cell Inner)
(declare-const after_cells (Array (_ BitVec 64) Inner))
(assert (= old_cell (select (fld_data before) (_ bv33 64))))
(assert (= new_cell
  (mk_inner (fld_ptr old_cell) (fld_len old_cell) (fld_cap old_cell)
            (store (fld_data old_cell) (_ bv64 64) #x09))))
(assert (= after_cells (store (fld_data before) (_ bv33 64) new_cell)))
(assert (= after (mk_outer (fld_ptr before) (fld_len before) (fld_cap before) after_cells)))
(assert (= (select (fld_data (select (fld_data before) (_ bv64 64))) (_ bv33 64)) #x07))
(assert (not (= (select (fld_data (select (fld_data after) (_ bv64 64))) (_ bv33 64)) #x07)))
(check-sat)
