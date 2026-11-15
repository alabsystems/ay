; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; Authored full-source safety obligation, not AY output or captured MC export.
; Global functions remain uninterpreted: no selected function model is pinned.
; Expected SAT: independent functions supplies fill and all cells.
(set-logic ALL)
(declare-fun f (Bool (_ BitVec 8)) (_ BitVec 8))
(declare-fun g (Bool (_ BitVec 8)) (_ BitVec 8))
(declare-fun unused ((_ BitVec 136)) (_ BitVec 136))
(declare-const x (_ BitVec 8))
(declare-const fill (_ BitVec 8))
(declare-const k (_ BitVec 64))
(assert (= fill (f true x)))
(assert (bvuge k (_ bv32 64)))
(declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
(assert (bvult k (_ bv65 64)))
(assert (forall ((i (_ BitVec 64)))
  (=> (bvult i (_ bv65 64)) (= (select a i) (g true x)))))
(assert (distinct (select a k) fill))
(check-sat)
