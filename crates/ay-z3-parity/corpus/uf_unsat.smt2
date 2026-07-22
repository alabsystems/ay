; expected: unsat
; QF_UF — congruence forces f(a)=f(b), contradicting the inequality.
(set-logic QF_UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const a U)
(declare-const b U)
(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)
