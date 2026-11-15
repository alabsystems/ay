; 2026-09-23 differential hunt, D4-c (storeeq_41_0883.min). z3 5.1.0: sat (its model re-checks sat).
; main f399eca07a answered unsat here; a sat file must never become unsat.
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(assert (= b ((as const (Array Int Int)) 1)))
(assert (= (store (store b 2 (select (store a0 5 2) (+ i 1))) i (select a0 (+ i 1))) (store (store b (+ i 2) i) i 1)))
(check-sat)
