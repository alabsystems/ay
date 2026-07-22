; Reproducer for Z3 issue #7825 — arrays query perf profile.
; Source: https://github.com/Z3Prover/z3/issues/7825
; This is a perf stress, not a soundness bug. Added as a slow-path eval.
; Duplicated from crates/ay-theories/arrays/tests/z3_soundness/z3_7825.smt2
; so that the z3-perf-cliffs eval bundles all 9 inputs in one directory.
; Expected: sat for this minimized scaffold.
; Theory: QF_AX.
;
; Author: Andrew Yates <andrewyates.name@gmail.com>
(set-logic QF_AX)
(declare-sort E 0)
(declare-fun a () (Array E E))
(declare-fun i1 () E)
(declare-fun i2 () E)
(declare-fun i3 () E)
(declare-fun i4 () E)
(declare-fun v1 () E)
(declare-fun v2 () E)
(declare-fun v3 () E)
(declare-fun v4 () E)
(assert (= (select (store (store (store (store a i1 v1) i2 v2) i3 v3) i4 v4) i1) v1))
(assert (distinct i1 i2))
(assert (distinct i1 i3))
(assert (distinct i1 i4))
(check-sat)
