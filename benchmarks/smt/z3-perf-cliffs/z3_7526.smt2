; Reproducer for Z3 issue #7526 — QF_BV: slow unsat on multiplication overflow.
; Source: https://github.com/Z3Prover/z3/issues/7526
; Symptom: Proving that a product fits in a bounded-width multiplier without
; overflow is slow because the bit-blasted encoding must rule out a large
; carry-chain space. Minimized here to a 32-bit overflow check.
; Expected: unsat (no x,y below 2^16 multiply to a large value).
; Theory: QF_BV.
;
; Author: Andrew Yates <andrewyates.name@gmail.com>
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(assert (bvult x (_ bv65536 32)))
(assert (bvult y (_ bv65536 32)))
; (x * y) must fit in 32 bits since both operands < 2^16. Assert it does NOT —
; this is unsatisfiable but requires reasoning over all bit positions.
(assert (not (= (bvmul x y) ((_ extract 31 0) (bvmul ((_ zero_extend 32) x)
                                                     ((_ zero_extend 32) y))))))
(check-sat)
