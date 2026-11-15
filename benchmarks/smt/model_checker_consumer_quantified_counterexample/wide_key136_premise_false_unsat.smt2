; Copyright 2026 Andrew Yates
; SPDX-License-Identifier: Apache-2.0
; Independently authored two-occurrence original-source conjunction, not AY output.
; Expected UNSAT; exact 136-bit frozen-table keys with complete BV64 fill premise.
; Table interpretations are not IEEE execution or external-call purity evidence.
; Live float-key shape: tag8 ++ lhs ++ rhs; high key uses operation tag4.
(set-logic ALL)
(declare-const table0 (Array (_ BitVec 136) (_ BitVec 8)))
(declare-const low0 (_ BitVec 136))
(declare-const high0 (_ BitVec 136))
(declare-const data0 (Array (_ BitVec 64) (_ BitVec 8)))
(declare-const table1 (Array (_ BitVec 136) (_ BitVec 8)))
(declare-const low1 (_ BitVec 136))
(declare-const high1 (_ BitVec 136))
(declare-const data1 (Array (_ BitVec 64) (_ BitVec 8)))
(assert (= low0 (concat (_ bv0 8) (concat (_ bv9223372036854775811 64) (_ bv9 64)))))
(assert (= high0 (concat (_ bv4 8) (concat (_ bv9223372036854775811 64) (_ bv9 64)))))
(assert (= table0 (store (store ((as const (Array (_ BitVec 136) (_ BitVec 8)))
  (_ bv0 8)) low0 (_ bv7 8)) high0 (_ bv9 8))))
(assert (= data0 (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv7 8)) (_ bv64 64) (_ bv8 8))))
(assert (forall ((i (_ BitVec 64)))
  (=> (bvult i (_ bv65 64)) (= (select data0 i) (_ bv7 8)))))
(assert (= table1 table0))
(assert (= low1 low0))
(assert (= high1 high0))
(assert (= data1 data0))
(assert (= (select table1 low1) (_ bv7 8)))
(assert (= (select table1 high1) (_ bv9 8)))
(assert (distinct (select table1 low1) (select table1 high1)))
(check-sat)
