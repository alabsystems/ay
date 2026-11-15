; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; Authored full-source safety obligation, not AY output or captured MC export.
; Global functions remain uninterpreted: no selected function model is pinned.
; Expected SAT: independent functions supplies fill and all cells.
(set-logic ALL)
(declare-datatype Vec ((mkVec (ptr (_ BitVec 64)) (len (_ BitVec 64)) (cap (_ BitVec 64)) (data (Array (_ BitVec 64) (_ BitVec 8))))))
(declare-fun f (Bool (_ BitVec 8)) (_ BitVec 8))
(declare-fun g (Bool (_ BitVec 8)) (_ BitVec 8))
(declare-fun unused ((_ BitVec 136)) (_ BitVec 136))
(declare-const x (_ BitVec 8))
(declare-const fill (_ BitVec 8))
(declare-const k (_ BitVec 64))
(assert (= fill (f true x)))
(assert (bvuge k (_ bv32 64)))
(declare-const v Vec)
(assert (= (len v) (_ bv65 64)))
(assert (bvult k (len v)))
(assert (forall ((i (_ BitVec 64)))
  (=> (bvult i (len v)) (= (select (data v) i) (g true x)))))
(assert (distinct (select (data v) k) fill))
(check-sat)
