; Reproducer for Z3 issue #7038 — QF_BV: Python BV perf cliff.
; Source: https://github.com/Z3Prover/z3/issues/7038
; Symptom: Wide bitvector arithmetic with nested shifts and multiplications
; triggers a large blowup during bit-blasting. Minimized scaffold exercises the
; same pattern.
; Expected: sat/unsat decidable within 30s (but slow on Z3).
; Theory: QF_BV.
;
; Author: Andrew Yates <andrewyates.name@gmail.com>
(set-logic QF_BV)
(declare-const x (_ BitVec 64))
(declare-const y (_ BitVec 64))
(declare-const z (_ BitVec 64))
(assert (= (bvmul x y) (bvshl z (_ bv3 64))))
(assert (= (bvmul y z) (bvshl x (_ bv5 64))))
(assert (= (bvand x y) (_ bv0 64)))
(assert (bvult x (_ bv1048576 64)))
(assert (bvult y (_ bv1048576 64)))
(assert (bvult z (_ bv1048576 64)))
(assert (not (= x (_ bv0 64))))
(assert (not (= y (_ bv0 64))))
(check-sat)
