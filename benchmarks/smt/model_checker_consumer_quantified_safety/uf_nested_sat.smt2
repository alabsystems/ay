; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; Authored full-source safety obligation, not AY output or captured MC export.
; Global functions remain uninterpreted: no selected function model is pinned.
; Expected SAT: independent functions supplies fill and all cells.
(set-logic ALL)
(declare-datatype Inner ((mkInner (inner_len (_ BitVec 64)) (inner_data (Array (_ BitVec 64) (_ BitVec 8))))))
(declare-datatype Outer ((mkOuter (outer_len (_ BitVec 64)) (outer_data (Array (_ BitVec 64) Inner)))))
(declare-fun f (Bool (_ BitVec 8)) (_ BitVec 8))
(declare-fun g (Bool (_ BitVec 8)) (_ BitVec 8))
(declare-fun unused ((_ BitVec 136)) (_ BitVec 136))
(declare-const x (_ BitVec 8))
(declare-const fill (_ BitVec 8))
(declare-const k (_ BitVec 64))
(assert (= fill (f true x)))
(assert (bvuge k (_ bv32 64)))
(declare-const v Outer)
(declare-const column (_ BitVec 64))
(assert (= (outer_len v) (_ bv65 64)))
(assert (= (inner_len (select (outer_data v) k)) (_ bv65 64)))
(assert (bvult k (outer_len v)))
(assert (bvuge column (_ bv32 64)))
(assert (bvult column (inner_len (select (outer_data v) k))))
(assert (forall ((i (_ BitVec 64)) (j (_ BitVec 64)))
  (=> (and (bvult i (outer_len v))
           (bvult j (inner_len (select (outer_data v) i))))
      (= (select (inner_data (select (outer_data v) i)) j) (g true x)))))
(assert (distinct (select (inner_data (select (outer_data v) k)) column) fill))
(check-sat)
