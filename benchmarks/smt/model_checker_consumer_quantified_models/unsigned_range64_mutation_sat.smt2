; Close mutation of signed_range64_fill_unsat: unsigned [-2, 2) is empty.
; Expected sat. Treating signed guards as unsigned would miss the original bug.
(set-logic ALL)
(declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
(assert (forall ((i (_ BitVec 64)))
  (=> (and (bvuge i #xfffffffffffffffe) (bvult i #x0000000000000002))
      (= (select a i) #x07))))
(assert (distinct (select a #xffffffffffffffff) #x07))
(check-sat)
