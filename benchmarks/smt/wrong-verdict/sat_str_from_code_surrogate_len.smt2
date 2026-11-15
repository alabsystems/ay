; D8 (2026-09-23 hunt, witness w01). z3 5.1.0: sat. main f399eca07a: unsat.
; SMT-LIB strings range over code points 0..0x2FFFF INCLUDING the surrogates
; U+D800..U+DFFF, so (str.from_code 55296) is one character. AY folded it to
; "" (char::from_u32 has no surrogates) and refuted the query.
(set-logic ALL)
(assert (= (str.len (str.from_code 55296)) 1))
(check-sat)
