; QF_UFLIA shared-window modular-premise regression candidate.
; Expected Z3 5.1.0 answers: unsat, sat, sat, sat.
; The valid branch is a=c, with y=38, f(a)=f(c)=154, and f(b)=151.
;
; f(a)=4y+2 makes f(a) congruent to 2 mod 4. Under a=b, congruence
; forces f(b) outside [151,152], so that branch is UNSAT. Under a=c,
; f(a)=154 is valid. A modular conflict learned from the a=b branch must
; cite the shared-equality premise (= a b); the LIA asserted arithmetic
; atoms alone admit the a=c model. This file pins the expected semantics;
; it is not yet claimed to reproduce an AY wrong verdict.
(set-logic QF_UFLIA)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-fun f (U) Int)
(declare-const y Int)

(assert (= (f a) (+ (* 4 y) 2)))
(assert (>= (f b) 151))
(assert (<= (f b) 152))
(assert (= (f c) 154))

(push 1)
(assert (= a b))
(check-sat) ; unsat
(pop 1)

(push 1)
(assert (= a c))
(check-sat) ; sat
(pop 1)

(push 1)
(assert (or (= a b) (= a c)))
(check-sat) ; sat
(pop 1)

(push 1)
(assert (or (= a c) (= a b)))
(check-sat) ; sat
(pop 1)
