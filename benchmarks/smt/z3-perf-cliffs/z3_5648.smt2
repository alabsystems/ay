; Reproducer for Z3 issue #5648 — regex InRe performance cliff.
; Source: https://github.com/Z3Prover/z3/issues/5648
; Symptom: Nested `str.in_re` over a union of regexes with Kleene star causes
; a performance cliff in the regex-to-automaton translation. Minimized here
; to a union-of-concatenations scaffold.
; Expected: sat ("ab" matches the first alternative).
; Theory: QF_S + regex.
;
; Author: Andrew Yates <andrewyates.name@gmail.com>
(set-logic QF_S)
(declare-const x String)
(assert (str.in_re x
  (re.union
    (re.++ (str.to_re "a") (re.* (str.to_re "b")))
    (re.++ (str.to_re "c") (re.* (str.to_re "d"))))))
(assert (>= (str.len x) 2))
(assert (<= (str.len x) 10))
(assert (str.contains x "b"))
(check-sat)
