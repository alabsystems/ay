; 2026-09-23 differential hunt, D4-b (storeeq_41_0293.min; the checked-sat-refutation lane admitted the original). z3 5.1.0: sat (its model re-checks sat).
; main f399eca07a answered unsat here; a sat file must never become unsat.
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(assert (= (store (store (store b j 1) i (select a0 2)) 2 j) (store (store (store ((as const (Array Int Int)) 0) 0 k) j 2) 2 5)))
(check-sat)
