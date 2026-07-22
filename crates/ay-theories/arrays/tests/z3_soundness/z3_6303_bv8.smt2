; Reproducer for Z3 issue #6303 — unknown/unsat switch based on array range sort.
; Source: https://github.com/Z3Prover/z3/issues/6303
; Case 2: range = BV8. Expected: same answer (unsat) as the BV32 case.
; Original Z3 returned unknown here.
(set-logic ALL)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (forall ((fqv (Array (_ BitVec 32) (_ BitVec 8))))
  (= (select a (concat (select fqv #x00000003) (concat (select fqv #x00000002)
              (concat (select fqv #x00000001) (select fqv #x00000000)))))
     (select b (concat (select fqv #x00000003) (concat (select fqv #x00000002)
              (concat (select fqv #x00000001) (select fqv #x00000000))))))))
(assert (= false (= (select a #x00000000) (select b #x00000000))))
(check-sat)
