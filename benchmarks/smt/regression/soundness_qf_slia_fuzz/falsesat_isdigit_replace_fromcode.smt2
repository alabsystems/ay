; QF_SLIA FALSE-SAT (found by diff_fuzz multi-theory fan-out). str.from_code(-2)=""
; (invalid code point), empty-needle str.replace inserts at front -> multi-char
; string, str.is_digit of a multi-char string is false -> the conjunct is UNSAT
; (z3=unsat). AY rubber-stamps a wrong model on the monolithic top-level (and ...).
; FRAGILE: splitting the (and ...) or removing the ite flips AY to safe unknown ->
; the bug is in AY's monolithic-conjunction model-validation/SAT-fallback path
; (same family as false_sat_str_code_6263). NOT yet fixed.
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun s () String)(declare-fun t () String)(declare-fun u () String)
(declare-fun w () String)(declare-fun m () Int)(declare-fun r () Bool)
(assert (= s " "))(assert (= t "9"))(assert (= w "a"))(assert (= m -2))
(assert (and (ite (str.< w (str.++ s "b" w)) (not (str.<= t "a")) (ite (distinct s u) r r)) (str.is_digit (str.replace (str.++ " " "ab") (str.from_code m) (str.replace "12" t s)))))
(check-sat)
