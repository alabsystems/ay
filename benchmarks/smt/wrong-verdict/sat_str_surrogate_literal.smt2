; D8 (2026-09-23 hunt, g3 shape `lit`). z3 5.1.0: sat. main f399eca07a:
; `(error "... surrogate code point U+D800, which is not representable as a
; Rust char")` then `unknown` -- a surrogate escape is a legal SMT-LIB
; character and must read as ONE character with that code point.
(set-logic QF_SLIA)
(declare-const x String)
(assert (= x "\u{d800}"))
(assert (= (str.len x) 1))
(assert (= (str.to_code x) 55296))
(assert (= (str.to_code "\udfff") 57343))
(assert (str.in_re x (re.range "\u{d800}" "\u{dfff}")))
(check-sat)
