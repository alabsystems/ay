; Historical reproducer for BV soundness bug #1708
; Current AY and Z3 both return UNSAT; retained as a regression.
;
; The bug triggers when:
; 1. Two decode bitvectors share operand variables (a, b, c, d, f)
; 2. Mode-based ITE selects between layouts
; 3. Extracts from the decode bitvectors should recover the operands
; 4. Outputs computed from extracted ops should be equal
;
; Root cause: ITE with BV equality constraints not properly handled
; when multiple terms share variables.
;
; Issue: #1708

(set-logic QF_BV)
(set-info :status unsat)

; Shared operands
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(declare-fun d () (_ BitVec 8))
(declare-fun f () (_ BitVec 1))

; Processor 1
(declare-fun x1 () (_ BitVec 33))
(declare-fun op1_1 () (_ BitVec 8))
(declare-fun op2_1 () (_ BitVec 8))
(declare-fun op3_1 () (_ BitVec 8))
(declare-fun op4_1 () (_ BitVec 8))
(declare-fun func_1 () (_ BitVec 1))
(declare-fun mode_1 () (_ BitVec 1))

; Processor 2
(declare-fun x2 () (_ BitVec 33))
(declare-fun op1_2 () (_ BitVec 8))
(declare-fun op2_2 () (_ BitVec 8))
(declare-fun op3_2 () (_ BitVec 8))
(declare-fun op4_2 () (_ BitVec 8))
(declare-fun func_2 () (_ BitVec 1))
(declare-fun mode_2 () (_ BitVec 1))

(define-fun m1 () Bool (= mode_1 (_ bv0 1)))
(define-fun m2 () Bool (= mode_2 (_ bv0 1)))

; Processor 1 layout: [f|a|b|c|d] when mode=0, [f|d|c|b|a] when mode=1
(assert (ite m1
  (= x1 (concat (concat (concat (concat f a) b) c) d))
  (= x1 (concat (concat (concat (concat f d) c) b) a))))

(define-fun e32 () (_ BitVec 1) ((_ extract 32 32) x1))
(define-fun e31_24 () (_ BitVec 8) ((_ extract 31 24) x1))
(define-fun e23_16 () (_ BitVec 8) ((_ extract 23 16) x1))
(define-fun e15_8 () (_ BitVec 8) ((_ extract 15 8) x1))
(define-fun e7_0 () (_ BitVec 8) ((_ extract 7 0) x1))

(assert (ite m1
  (and (= func_1 e32) (= op1_1 e31_24) (= op2_1 e23_16) (= op3_1 e15_8) (= op4_1 e7_0))
  (and (= func_1 e32) (= op4_1 e31_24) (= op3_1 e23_16) (= op2_1 e15_8) (= op1_1 e7_0))))

; Processor 2 layout: [a|f|b|c|d] when mode=0 (different!)
(assert (ite m2
  (= x2 (concat (concat (concat (concat a f) b) c) d))
  (= x2 (concat (concat (concat (concat d f) c) b) a))))

(define-fun f32_25 () (_ BitVec 8) ((_ extract 32 25) x2))
(define-fun f24 () (_ BitVec 1) ((_ extract 24 24) x2))
(define-fun f23_16 () (_ BitVec 8) ((_ extract 23 16) x2))
(define-fun f15_8 () (_ BitVec 8) ((_ extract 15 8) x2))
(define-fun f7_0 () (_ BitVec 8) ((_ extract 7 0) x2))

(assert (ite m2
  (and (= op1_2 f32_25) (= func_2 f24) (= op2_2 f23_16) (= op3_2 f15_8) (= op4_2 f7_0))
  (and (= op4_2 f32_25) (= func_2 f24) (= op3_2 f23_16) (= op2_2 f15_8) (= op1_2 f7_0))))

; Output computation
(declare-fun out_1 () (_ BitVec 8))
(declare-fun out_2 () (_ BitVec 8))
(assert (ite (= func_1 (_ bv1 1))
  (= out_1 (bvadd (bvadd (bvadd op1_1 op2_1) op3_1) op4_1))
  (= out_1 (bvor (bvor (bvor op1_1 op2_1) op3_1) op4_1))))
(assert (ite (= func_2 (_ bv1 1))
  (= out_2 (bvadd (bvadd (bvadd op1_2 op2_2) op3_2) op4_2))
  (= out_2 (bvor (bvor (bvor op1_2 op2_2) op3_2) op4_2))))

; Same mode for both
(assert (= mode_1 mode_2))

; Question: can outputs differ? Should be UNSAT.
(assert (not (= out_1 out_2)))

(check-sat)
