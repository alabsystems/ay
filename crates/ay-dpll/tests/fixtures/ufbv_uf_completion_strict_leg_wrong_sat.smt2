; Copyright 2026 Andrew Yates
; Licensed under the Apache License, Version 2.0
;
; MINIMAL reproduction of the quantified-UFBV wrong `sat`
; (#ufbv-strict-uf-completion-no-coverage). Hand-authored, not derived from any
; benchmark — three lines of content, one binder, one function.
;
; THIS PROBLEM IS UNSATISFIABLE, and the refutation needs no solver:
;   instantiate the universal at x = #x00000001. The two conjuncts then demand
;   f(1) = 0 and 1 = f(1), hence 1 = 0. False. So the universal is false and the
;   assertion set is unsatisfiable. z3 4.15.4 agrees (`unsat`).
;
; AY answers `sat` in default mode with `:conflicts 0 :decisions 0
; :ematching-instances-created 0` and an EMPTY model — it never instantiates the
; one quantifier. `--self-check` returns `unknown` with
; `(:reason-unknown incomplete)`, so only default mode is unsound here.
;
; ROOT CAUSE (traced with AY_DEBUG_CERT=1): the STRICT UF-completion certificate
; grants the `sat`.
;   * `quantifiers_supported_by_uf_completion` (quantifier_loop/mod.rs:746) is a
;     conjunction with NO coverage term — not `has_uninstantiated`, not
;     `ematching_instances_created`, not `full_ematching_coverage`. With a single
;     assertion there are no ground assertions, so its other conjuncts are
;     vacuously true.
;   * Its sibling `..._given_sat` leg IS gated on
;     `!has_uninstantiated && !reached_limit && !deferred_exists`
;     (mod.rs:937) and correctly declines here. Only one of the two legs ever
;     received the coverage discipline; that asymmetry is the defect.
;   * `term_supported_by_uf_completion`'s `and` arm (mbqi.rs:1339) accepts each
;     conjunct INDEPENDENTLY, and `uf_definition_supported_by_completion`
;     (mbqi.rs:2608) does not require a defined head to be defined only ONCE. So
;     `(= (f x) 0)` and `(= x (f x))` are both certified as freely completable
;     even though they are contradictory. The pairwise-distinct-head discipline
;     that would catch this exists — but only on the `given_sat` leg
;     (mod.rs:816), which is disabled here by its coverage gate.
;
; The load-bearing shape is a conjunct equating the UF application to a BARE
; BOUND VARIABLE alongside a constant-valued definition of the same head. That is
; the reduced form of the corpus instances' `(= (f0 x⃗) 0)` + `(= v (f0 x⃗))`.
; Variants whose second conjunct is a computed term (`(= (bvadd x 1) (f x))`), or
; where two DISTINCT heads clash, still set `strict=true` but get refuted earlier
; by ground preprocessing — so the bare-bound-var form is the tight witness.
;
; NOT fixed by the multi-point `premise_forced_binder_refutation` probe: that
; probe requires a `(=> premise conclusion)` body to extract binder values from,
; and this body is a bare conjunction with no premise, so the probe declines by
; construction. Fixing this one needs the coverage premise on the strict leg.
(set-logic UFBV)
(set-info :status unsat)
(declare-fun f ((_ BitVec 32)) (_ BitVec 32))
(assert (forall ((x (_ BitVec 32))) (and (= (f x) (_ bv0 32)) (= x (f x)))))
(check-sat)
