; Fuzzed QF_BV (review of DR-30, 2026-10-08). UNSAT because (bvsub v1 v1) = 2
; is false; preprocessing folds the second assertion to false. With proofs
; observable, the wire-gap repair asks the complete bit-blast to print the
; first assertion alone, a FALSE lemma over a 64-bit divider and multiplier,
; and its sweep spent the whole :timeout before the monolithic search said so.
(set-option :produce-proofs true)
(set-option :timeout 60000)
(set-logic QF_BV)
(declare-const v0 (_ BitVec 64))
(declare-const v1 (_ BitVec 64))
(declare-const v2 (_ BitVec 64))
(assert (= (bvneg v2) (bvadd (bvneg v0) (bvudiv v1 v2) v0 (_ bv18446744073709551614 64))))
(assert (not (=> (= (bvsub v1 v1) (bvneg (_ bv18446744073709551614 64))) (distinct (bvadd v0 (bvadd (_ bv9223372036854775809 64) v0 v1 (bvsub (_ bv16 64) v0) (bvneg v0))) (bvadd (_ bv9223372036854775808 64) (bvmul v1 v2))))))
(check-sat)
