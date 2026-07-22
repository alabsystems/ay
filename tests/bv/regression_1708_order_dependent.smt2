; Regression test for issue #1708 - order-dependent SAT/UNSAT
; This test exposes a bug where different operand orderings in bvadd
; produce different results (SAT vs UNSAT) despite all being UNSAT.
;
; Expected: UNSAT
; Bug: the legacy solver returned SAT for certain orderings (op4+op3+op2+op1)
;      but UNSAT for others (op1+op3+op2+op4)
;
; The bug involves:
; 1. Mode-dependent ITE with Bool result (decode_1 = ..., decode_2 = ...)
; 2. 49-bit bitvectors with different bit layouts between processors
; 3. 4-operand bvadd chains with certain orderings

(set-logic QF_BV)

(declare-fun operator1 () (_ BitVec 8))
(declare-fun operator2 () (_ BitVec 8))
(declare-fun operator3 () (_ BitVec 8))
(declare-fun operator4 () (_ BitVec 8))

(declare-fun mode_1 () (_ BitVec 1))
(declare-fun mode_2 () (_ BitVec 1))

(declare-fun decode_1 () (_ BitVec 49))
(declare-fun decode_2 () (_ BitVec 49))

(declare-fun op1_1 () (_ BitVec 8))
(declare-fun op2_1 () (_ BitVec 8))
(declare-fun op3_1 () (_ BitVec 8))
(declare-fun op4_1 () (_ BitVec 8))
(declare-fun op1_2 () (_ BitVec 8))
(declare-fun op2_2 () (_ BitVec 8))
(declare-fun op3_2 () (_ BitVec 8))
(declare-fun op4_2 () (_ BitVec 8))

; Mode constraint - modes must be equal
(assert (= mode_1 mode_2))

; Decode - processor 1: marker bit at position 48
(assert (ite (= mode_1 #b0)
  (= decode_1 (concat #b1 (concat operator1 (concat operator2 (concat operator3 (concat operator4 #x0000))))))
  (= decode_1 (concat #b1 (concat operator4 (concat operator3 (concat operator2 (concat operator1 #x0000))))))))

; Decode - processor 2: marker bit at position 40 (different layout!)
(assert (ite (= mode_2 #b0)
  (= decode_2 (concat operator1 (concat #b1 (concat operator2 (concat operator3 (concat operator4 #x0000))))))
  (= decode_2 (concat operator4 (concat #b1 (concat operator3 (concat operator2 (concat operator1 #x0000))))))))

; Read decode - processor 1
(assert (ite (= mode_1 #b0)
  (and (= op1_1 ((_ extract 47 40) decode_1))
       (= op2_1 ((_ extract 39 32) decode_1))
       (= op3_1 ((_ extract 31 24) decode_1))
       (= op4_1 ((_ extract 23 16) decode_1)))
  (and (= op4_1 ((_ extract 47 40) decode_1))
       (= op3_1 ((_ extract 39 32) decode_1))
       (= op2_1 ((_ extract 31 24) decode_1))
       (= op1_1 ((_ extract 23 16) decode_1)))))

; Read decode - processor 2 (note: extract 48 41 instead of 47 40)
(assert (ite (= mode_2 #b0)
  (and (= op1_2 ((_ extract 48 41) decode_2))
       (= op2_2 ((_ extract 39 32) decode_2))
       (= op3_2 ((_ extract 31 24) decode_2))
       (= op4_2 ((_ extract 23 16) decode_2)))
  (and (= op4_2 ((_ extract 48 41) decode_2))
       (= op3_2 ((_ extract 39 32) decode_2))
       (= op2_2 ((_ extract 31 24) decode_2))
       (= op1_2 ((_ extract 23 16) decode_2)))))

; Compare sum with order op4+op3+op2+op1 - this ordering triggers the bug
(assert (not (= (bvadd (bvadd (bvadd op4_1 op3_1) op2_1) op1_1)
                (bvadd (bvadd (bvadd op4_2 op3_2) op2_2) op1_2))))

(check-sat)
(exit)
