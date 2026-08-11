; #bug04. UNSAT: `bvneg q2` reaches the signed minimum, so no q0 is < all of it.
; A heuristic boundary sample MISSED that witness and answered sat. Any change
; that lets a NON-exhaustive pass conclude Sat regresses this to a WRONG ANSWER.
(set-logic BV)
(assert (exists ((q0 (_ BitVec 4))) (forall ((q2 (_ BitVec 4))) (bvslt q0 (bvneg q2)))))
(check-sat)
