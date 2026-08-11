; The refutation direction at a width enumeration cannot cover: no `a` bounds
; every 32-bit x from above, so the forall is false and the problem UNSAT.
(set-logic BV)
(declare-fun a () (_ BitVec 32))
(assert (bvugt a #x00000005))
(assert (forall ((x (_ BitVec 32))) (bvult x a)))
(check-sat)
