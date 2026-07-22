; Reproducer for Z3 issue #2575 — reasoning with regex.
; Source: https://github.com/Z3Prover/z3/issues/2575
; Symptom: Reasoning about string membership in a complex regex combined with
; string length and contains constraints produces a hard case for the regex
; solver. Minimized scaffold below.
; Expected: sat.
; Theory: QF_S + regex.
;
; Author: Andrew Yates <andrewyates.name@gmail.com>
(set-logic QF_S)
(declare-const s String)
(assert (str.in_re s
  (re.++
    (re.* (str.to_re "a"))
    (re.++ (str.to_re "b")
           (re.* (re.union (str.to_re "c") (str.to_re "d")))))))
(assert (>= (str.len s) 4))
(assert (<= (str.len s) 8))
(assert (str.contains s "ab"))
(assert (or (str.contains s "c") (str.contains s "d")))
(check-sat)
