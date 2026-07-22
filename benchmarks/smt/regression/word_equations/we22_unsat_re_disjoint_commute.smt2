; Stage 2 regression (A3): Lyndon–Schützenberger — commuting non-empty words
; share a primitive root, impossible for disjoint alphabets a+ vs b+.
; before: unknown   after: unsat   z3 4.16.0: unsat
(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x y) (str.++ y x)))
(assert (str.in_re x (re.+ (str.to_re "a"))))
(assert (str.in_re y (re.+ (str.to_re "b"))))
(check-sat)
