; Authored signed-index model-validation control, not captured MODEL_CHECKER_CONSUMER output.
; The two's-complement interval [-2, 2) includes the array key -1.
; Expected unsat. This tests source semantics, not an AY verdict or proof.
(set-logic ALL)
(declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
(assert (forall ((i (_ BitVec 64)))
  (=> (and (bvsge i #xfffffffffffffffe) (bvslt i #x0000000000000002))
      (= (select a i) #x07))))
(assert (distinct (select a #xffffffffffffffff) #x07))
(check-sat)
