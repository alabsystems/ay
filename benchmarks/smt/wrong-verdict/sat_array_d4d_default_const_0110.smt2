; 2026-09-23 differential hunt, D4-d (const_11_0110.min, --z3-mode). z3 5.1.0: sat (its model re-checks sat).
; main f399eca07a answered unsat here; a sat file must never become unsat.
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun i0 () Int)
(declare-fun v0 () Int)
(assert (=> (= (select (store (store ((as const (Array Int Int)) 1) 2 0) 1 (select (store a1 i0 i0) i0)) i0) v0) (not (< (select (store ((as const (Array Int Int)) v0) i0 i0) i0) v0))))
(assert (or (= (store (store ((as const (Array Int Int)) v0) 2 i0) i0 (select a1 (+ i0 1))) a0) (not (= i0 1))))
(assert (or (not (= ((as const (Array Int Int)) 1) (store ((as const (Array Int Int)) 0) i0 v0))) (> (select a2 (+ i0 1)) v0)))
(check-sat)
