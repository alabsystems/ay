; Reproducer for Z3 issue #6303 — unknown/unsat switch based on array range sort.
; Source: https://github.com/Z3Prover/z3/issues/6303
; Case 1: range = BV32. Expected: unsat.
(set-logic ALL)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 32)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 32)))
(assert (forall ((fqv (Array (_ BitVec 32) (_ BitVec 8))))
  (= (select a (concat (select fqv #x00000003) (concat (select fqv #x00000002)
              (concat (select fqv #x00000001) (select fqv #x00000000)))))
     (select b (concat (select fqv #x00000003) (concat (select fqv #x00000002)
              (concat (select fqv #x00000001) (select fqv #x00000000))))))))
(assert (= false (= (select a #x00000000) (select b #x00000000))))
(check-sat)
