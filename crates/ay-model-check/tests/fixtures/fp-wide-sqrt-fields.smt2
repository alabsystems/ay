; Diagnostic twin of fp-wide-sqrt.smt2. Preserve both forms: rounded Real
; conversion is an independent compatibility obligation, not an input rewrite.
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 200))
(assert (= x (fp #b0 #x81 (_ bv0 199))))
(assert (fp.eq (fp.sqrt RNE x) (fp #b0 #x80 (_ bv0 199))))
(check-sat)
(get-info :reason-unknown)
