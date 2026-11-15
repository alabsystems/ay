; 2026-09-23 differential hunt, D4-b, hand variant with free bases. z3 5.1.0: sat (its model re-checks sat).
; main f399eca07a answered unsat here; a sat file must never become unsat.
(set-logic QF_ALIA)
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v () Int)
(assert (= (store (store (store b j 1) i v) 2 j) (store (store c j 2) 2 5)))
(check-sat)
