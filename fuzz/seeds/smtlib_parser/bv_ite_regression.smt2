; Minimal reproducer for #1708 - BV soundness bug with 5+ Bool ITEs
;
; Bug pattern: 5+ Bool ITEs sharing condition `(= mode #b0)` with func bit in decode.
; AY incorrectly returns SAT when Z3 returns UNSAT (expected).
;
; Key observation: 4 ITEs (1 decode + 3 extracts) works, 5 ITEs fails.
; The decode constraint is violated in the model.

(set-logic QF_BV)
(set-option :produce-models true)

(declare-fun mode () (_ BitVec 1))
(declare-fun func () (_ BitVec 1))
(declare-fun op1 () (_ BitVec 8))
(declare-fun op2 () (_ BitVec 8))
(declare-fun op3 () (_ BitVec 8))
(declare-fun op4 () (_ BitVec 8))
(declare-fun decode () (_ BitVec 33))
(declare-fun x1 () (_ BitVec 8))
(declare-fun x2 () (_ BitVec 8))
(declare-fun x3 () (_ BitVec 8))
(declare-fun x4 () (_ BitVec 8))

; Decode
(assert (ite (= mode #b0)
             (= decode (concat (concat (concat (concat func op1) op2) op3) op4))
             (= decode (concat (concat (concat (concat func op4) op3) op2) op1))))

; Extract (4 separate ITEs)
(assert (ite (= mode #b0)
             (= x1 ((_ extract 31 24) decode))
             (= x1 ((_ extract 7 0) decode))))
(assert (ite (= mode #b0)
             (= x2 ((_ extract 23 16) decode))
             (= x2 ((_ extract 15 8) decode))))
(assert (ite (= mode #b0)
             (= x3 ((_ extract 15 8) decode))
             (= x3 ((_ extract 23 16) decode))))
(assert (ite (= mode #b0)
             (= x4 ((_ extract 7 0) decode))
             (= x4 ((_ extract 31 24) decode))))

; Sum should equal op1+op2+op3+op4
(assert (not (= (bvadd (bvadd (bvadd x1 x2) x3) x4) (bvadd (bvadd (bvadd op1 op2) op3) op4))))

(check-sat)
