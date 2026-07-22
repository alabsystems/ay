; Minimization of z3_7526.smt2 for issue #8698 (ay Phase 2).
; The identity (bvmul w x y) = extract[w-1..0](bvmul 2w (zx x) (zx y)) holds
; for all BV values, so its negation is UNSAT. At width 12 and below ay
; bit-blasts the multiplier eagerly and returns UNSAT quickly. At width 16+
; the delayed-internalization path kicks in (Z3's should_bit_blast port) and
; this was where the soundness bug lived: circuit clauses added in earlier
; re-check iterations were being dropped on subsequent fresh-solver rebuilds,
; letting the SAT solver return a model that violates a "built" circuit.
;
; Expected: unsat.
; Theory: QF_BV.
;
; Author: Andrew Yates <andrewyates.name@gmail.com>
(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(assert (not (= (bvmul x y)
                ((_ extract 15 0)
                 (bvmul ((_ zero_extend 16) x)
                        ((_ zero_extend 16) y))))))
(check-sat)
