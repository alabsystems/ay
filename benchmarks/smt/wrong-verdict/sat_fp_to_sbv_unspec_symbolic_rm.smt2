; D7 through the RoundingMode expansion lane (2026-09-23 hunt, g9_00071).
; z3 5.1.0: sat (r1 = anything but RTN). main f399eca07a: unsat, admitted as
; `checked-exact-rm-domain-expansion` -- a "checked" lane whose branch
; refutations were the D7 bit-blaster's wrong unsats, published on
; discharged-trust.
(set-logic ALL)
(declare-const x (_ FloatingPoint 4 4))
(declare-const y (_ FloatingPoint 4 4))
(declare-const r1 RoundingMode)
(assert (= x (_ +oo 4 4)))
(assert (= y (_ +oo 4 4)))
(assert (not (= ((_ fp.to_sbv 2) RTN x) ((_ fp.to_sbv 2) r1 y))))
(check-sat)
