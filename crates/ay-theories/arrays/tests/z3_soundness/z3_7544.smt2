; Reproducer for Z3 issue #7544 — wrong solution for subset / Bool Set.
; Source: https://github.com/Z3Prover/z3/issues/7544
; Encoded via characteristic function over arrays: S ⊆ T iff
;     forall x. (select S x) => (select T x).
; Here: a ⊆ b and b ⊆ a imply a = b, so (distinct a b) is unsat.
(set-logic ALL)
(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(assert (forall ((x Int)) (=> (select a x) (select b x))))
(assert (forall ((x Int)) (=> (select b x) (select a x))))
(assert (distinct a b))
(check-sat)
