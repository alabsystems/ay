(set-logic QF_ALIA)
; Array value with conflicting LIA constraints: UNSAT
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (>= (select a i) 0))
(assert (<= (select a i) 10))
(assert (= (+ (select a i) 5) 20))
(check-sat)
(exit)
