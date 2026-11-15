; D8 (2026-09-23 hunt, witness w05, plus the order the carrier must keep).
; z3 5.1.0: sat. main f399eca07a: unsat (both from_code folded to "").
; str.< is code-point order: U+D7FF < U+DAC0 < U+DAC1 < U+E000 < U+2FFFF.
(set-logic QF_SLIA)
(assert (str.< (str.from_code 56000) (str.from_code 56001)))
(assert (str.< "\u{d7ff}" (str.from_code 56000)))
(assert (str.< (str.from_code 56001) "\u{e000}"))
(assert (str.< "\u{dfff}" "\u{2ffff}"))
(check-sat)
