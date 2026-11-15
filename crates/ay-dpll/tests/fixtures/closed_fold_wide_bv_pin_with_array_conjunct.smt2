; Reduced (delta-debugged, renamed) from a validation query of model-checker-consumer's ask
; 2026-10-14-realloc-grow-pre-discharge-chc-undecided.
; The 128-bit pin `(= w ...)` is substituted into itself and folds to `true`;
; the array conjunct, unrelated to the contradiction, routes the query through
; the `PropagateValues` replay that must close that fold. The query is UNSAT
; propositionally: every conjunct of the negated `and` is asserted.
(set-logic ALL)
(declare-fun w () (_ BitVec 128))
(declare-fun b45 () (_ BitVec 64))
(declare-fun b46 () (_ BitVec 64))
(declare-fun b51 () (_ BitVec 64))
(declare-fun b67 () (_ BitVec 64))
(declare-fun b68 () (_ BitVec 64))
(declare-fun b8 () (_ BitVec 64))
(declare-fun a () (Array (_ BitVec 32) Bool))
(assert (and (= w (_ bv147573952589676412932 128)) (= a (store ((as const (Array (_ BitVec 32) Bool)) true) (_ bv66 32) true)) (not (= b68 (_ bv0 64))) (or (bvule (bvadd b8 (_ bv16 64)) b45) (bvule (bvadd b45 (_ bv16 64)) b8)) (or (bvule (bvadd b8 (_ bv16 64)) b46) (bvule (bvadd b46 (_ bv16 64)) b8)) (or (bvule (bvadd b8 (_ bv16 64)) b51) (bvule (bvadd b51 (_ bv32 64)) b8)) (or (bvule (bvadd b8 (_ bv16 64)) b67) (bvule (bvadd b67 (_ bv16 64)) b8)) (or (bvule (bvadd b8 (_ bv16 64)) b68) (bvule (bvadd b68 (_ bv24 64)) b8)) (or (bvule (bvadd b45 (_ bv16 64)) b46) (bvule (bvadd b46 (_ bv16 64)) b45)) (or (bvule (bvadd b45 (_ bv16 64)) b51) (bvule (bvadd b51 (_ bv32 64)) b45)) (or (bvule (bvadd b45 (_ bv16 64)) b67) (bvule (bvadd b67 (_ bv16 64)) b45)) (or (bvule (bvadd b45 (_ bv16 64)) b68) (bvule (bvadd b68 (_ bv24 64)) b45)) (or (bvule (bvadd b46 (_ bv16 64)) b51) (bvule (bvadd b51 (_ bv32 64)) b46)) (or (bvule (bvadd b46 (_ bv16 64)) b67) (bvule (bvadd b67 (_ bv16 64)) b46)) (or (bvule (bvadd b46 (_ bv16 64)) b68) (bvule (bvadd b68 (_ bv24 64)) b46)) (or (bvule (bvadd b51 (_ bv32 64)) b67) (bvule (bvadd b67 (_ bv16 64)) b51)) (not (and (not (= b68 (_ bv0 64))) (or (bvule (bvadd b8 (_ bv16 64)) b45) (bvule (bvadd b45 (_ bv16 64)) b8)) (or (bvule (bvadd b8 (_ bv16 64)) b51) (bvule (bvadd b51 (_ bv32 64)) b8)) (or (bvule (bvadd b8 (_ bv16 64)) b67) (bvule (bvadd b67 (_ bv16 64)) b8)) (or (bvule (bvadd b8 (_ bv16 64)) b68) (bvule (bvadd b68 (_ bv24 64)) b8)) (or (bvule (bvadd b45 (_ bv16 64)) b46) (bvule (bvadd b46 (_ bv16 64)) b45)) (or (bvule (bvadd b45 (_ bv16 64)) b51) (bvule (bvadd b51 (_ bv32 64)) b45)) (or (bvule (bvadd b45 (_ bv16 64)) b67) (bvule (bvadd b67 (_ bv16 64)) b45)) (or (bvule (bvadd b45 (_ bv16 64)) b68) (bvule (bvadd b68 (_ bv24 64)) b45)) (or (bvule (bvadd b46 (_ bv16 64)) b51) (bvule (bvadd b51 (_ bv32 64)) b46)) (or (bvule (bvadd b46 (_ bv16 64)) b67) (bvule (bvadd b67 (_ bv16 64)) b46)) (or (bvule (bvadd b46 (_ bv16 64)) b68) (bvule (bvadd b68 (_ bv24 64)) b46)) (or (bvule (bvadd b51 (_ bv32 64)) b67) (bvule (bvadd b67 (_ bv16 64)) b51))))))
(check-sat)
