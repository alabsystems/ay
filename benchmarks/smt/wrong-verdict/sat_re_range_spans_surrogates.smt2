; D8 (2026-09-23 hunt, witness w03). z3 5.1.0: sat (x = U+D800). main f399eca07a: unsat.
; (re.range "\u{d7ff}" "\u{e000}") has 2,050 members: the 2,048 surrogates lie
; between its endpoints. AY's alphabet skipped them, so the range minus its
; endpoints was empty to AY.
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.in_re x (re.diff (re.range "\u{d7ff}" "\u{e000}") (re.union (str.to_re "\u{d7ff}") (str.to_re "\u{e000}")))))
(check-sat)
