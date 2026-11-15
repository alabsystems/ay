; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; AUTHORED METAMORPHIC CONTROL, NOT A COMPILER-EXPORTED HARNESS.
; Paired with complete_outer_frame.smt2, using the same source provenance.
; Deliberately replace after_cells=store(before_cells,33,new_cell) by only
; select(after_cells,33)=new_cell. This loses the frame at every other row.
; Metadata preservation and the updated inner cell are otherwise unchanged.
; The bad read at (64,33) is now possible. Expected reference verdict: sat.
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
(assert (= (select after_cells (_ bv33 64)) new_cell))
(assert (= after (mk_outer (fld_ptr before) (fld_len before) (fld_cap before) after_cells)))
(assert (= (select (fld_data (select (fld_data before) (_ bv64 64))) (_ bv33 64)) #x07))
(assert (not (= (select (fld_data (select (fld_data after) (_ bv64 64))) (_ bv33 64)) #x07)))
(check-sat)
