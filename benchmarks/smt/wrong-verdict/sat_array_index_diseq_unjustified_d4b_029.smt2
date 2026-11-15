; 2026-09-28 arrays fix-up (#index-diseq-justified): the verifier's
; variants2/d4b/d4b_029. z3 5.1.0: sat (i = j = 5, a0[2] = 2), model re-checks.
; On a branch tip that reported the written indices of store-chain equalities
; to the array index-pair path, that path asserted i != j from a pinned j = 5
; and a FREE i under j's bound reasons alone, and the array lane answered unsat
; in 0.01 s (both postures). sat or unknown, never unsat.
(set-logic QF_ALIA)
(declare-fun a0 () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(assert (= (store (store (store b j 1) i (select a0 2)) 2 j) (store (store (store ((as const (Array Int Int)) 0) 0 k) j 2) 2 5)))
(assert (>= i -3))
(check-sat)
