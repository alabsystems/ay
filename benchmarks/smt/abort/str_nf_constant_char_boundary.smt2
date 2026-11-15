; Caught-panic reproducer (2026-09-23 hunt, witness p01). z3 5.1.0: sat.
; On main f399eca07a both postures printed
;   panicked at crates/ay-theories/strings/src/core/nf_equality.rs:334:47:
;   end byte index 2 is not a char boundary; it is inside '٣' (bytes 1..3 of string)
; and answered unknown: `process_nf_against_constant` sliced the constant as a
; `str` at BYTE offsets, and a one-byte component ended inside U+0663.
(set-logic QF_SLIA)
(declare-const x0 String)
(declare-const x2 String)
(assert (= (str.len x0) 2))
(assert (= (str.len x2) 4))
(assert (not (= (str.replace x0 "\u{663}" x2) "00")))
(check-sat)
