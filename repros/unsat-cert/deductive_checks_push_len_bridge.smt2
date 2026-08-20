; deductive-checks PUSH-transition length companion: an Int `len` bridged to a 64-bit
; BV `lenbv`, advanced by one on both sides. UNSAT.
;
; MEASURED 2026-08-19 at 120192833, `ay solve --probe-cert-reject --no-proof`:
; the verdict is correct and published, but ONLY through step (4) of
; `discharge_trust_steps_for_certification` — the whole-problem re-solve whose
; acceptance the source itself documents as machine-load sensitive.
;
; Step (3) declines because it is ALL-OR-NOTHING over the collected trust
; clauses, and one of the three is context-dependent:
;   t7  (<= 0 (bv2nat (bvadd lenbv 1)))                      standalone valid
;   t8  (or (= (bv2nat (bvadd lenbv 1)) (+ (bv2nat lenbv) 1))
;           (= (bv2nat (bvadd lenbv 1)) (+ (bv2nat lenbv) (- 18446744073709551615))))
;                                                            standalone valid
;                                                            (Schema A, bv_int_bridge_schema)
;   t6  (not (= (bv2nat (bvadd lenbv 1)) (+ (bv2nat lenbv) 1)))
;                     NOT standalone valid — it is the authored negated goal
;                     after VariableSubstitution folded `len2`/`len2bv` away,
;                     so it is entailed by the problem, not by itself.
; Two checked tautologies are therefore discarded because a third clause needs
; the context, and the family lands on the budgeted re-solve.
(set-logic ALL)
(declare-const len Int)
(declare-const lenbv (_ BitVec 64))
(declare-const len2 Int)
(declare-const len2bv (_ BitVec 64))
(assert (= len (bv2nat lenbv)))
(assert (= len2 (+ len 1)))
(assert (= len2bv (bvadd lenbv (_ bv1 64))))
(assert (<= len 100))
(assert (>= len 0))
(assert (not (= len2 (bv2nat len2bv))))
(check-sat)
