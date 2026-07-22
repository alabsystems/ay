; Reproducer for Z3 issue #2364 — QF_S: long strings timeout.
; Source: https://github.com/Z3Prover/z3/issues/2364
; Symptom: Constructing a long string from concatenations of short atoms and
; constraining its length triggers a combinatorial blowup in the string
; solver. Minimized here to a concatenation-with-length-bound scaffold.
; Expected: sat (with x = "abcabcabcabc").
; Theory: QF_S.
;
; Author: Andrew Yates <andrewyates.name@gmail.com>
(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (= y "abc"))
(assert (= x (str.++ y y y y y y y y y y y y)))
(assert (>= (str.len x) 30))
(assert (<= (str.len x) 40))
(assert (str.contains x "abcabc"))
(check-sat)
