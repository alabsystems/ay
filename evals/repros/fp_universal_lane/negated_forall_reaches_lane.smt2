; THE WRONG-UNSAT SHAPE. The problem asserts NOT (forall x . P), so no
; instance P[v] is a consequence. On the pre-fix lane this `forall` was marked
; conjunctive, so a `Refine` instance could be asserted and a resulting UNSAT
; published as a definite refutation.
;
; Ground truth: SAT. Pick c = 0; then x = 1.0 is a non-NaN with NOT (fp.leq x c),
; so the inner universal is genuinely false and its negation genuinely holds.
(set-logic ALL)
(declare-fun c () Float32)
(assert (not (forall ((x Float32)) (or (fp.isNaN x) (fp.leq x c)))))
(check-sat)
