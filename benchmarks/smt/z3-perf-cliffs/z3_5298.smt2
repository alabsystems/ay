; Reproducer for Z3 issue #5298 — regex performance.
; Source: https://github.com/Z3Prover/z3/issues/5298
; Symptom: A regex with repeated concatenation of character classes plus a
; length constraint is very slow in Z3's regex solver. Minimized scaffold.
; Expected: sat (any digit-string of length 6).
; Theory: QF_S + regex.
;
; Author: Andrew Yates <andrewyates.name@gmail.com>
(set-logic QF_S)
(declare-const x String)
(assert (str.in_re x
  (re.++ (re.range "0" "9")
         (re.++ (re.range "0" "9")
                (re.++ (re.range "0" "9")
                       (re.++ (re.range "0" "9")
                              (re.++ (re.range "0" "9")
                                     (re.range "0" "9"))))))))
(assert (= (str.len x) 6))
(assert (str.contains x "5"))
(check-sat)
