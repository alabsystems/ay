; storeinv nf size=2: cross-swap at 2 indices using nested let
; Using (not (= a1 a2)) instead of Skolem function
; Expected: unsat
(set-logic QF_AUFLIA)
(set-info :status unsat)
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(assert (let ((?v_0 (store a2 i1 (select a1 i1)))
              (?v_1 (store a1 i1 (select a2 i1))))
          (= (store ?v_1 i2 (select ?v_0 i2))
             (store ?v_0 i2 (select ?v_1 i2)))))
(assert (not (= a1 a2)))
(check-sat)
(exit)
