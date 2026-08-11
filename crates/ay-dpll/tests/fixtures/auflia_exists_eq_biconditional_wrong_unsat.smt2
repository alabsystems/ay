; Copyright 2026 Andrew Yates
; Licensed under the Apache License, Version 2.0
;
; Hand-authored minimal reproduction of a WRONG REFUTATION in quantified AUFLIA
; (#auflia-exists-eq-false-unsat). Not copied from any benchmark: the symbols,
; sorts and phrasing are original. The defect was first observed on the SMT-LIB
; AUFLIA `20170829-Rodin` family (whose files are CC BY-NC and therefore not
; vendored here); this file was reconstructed from an analysis of the failing
; structure so the workspace has a license-clean guard.
;
; THIS PROBLEM IS SATISFIABLE, and the witness needs no solver:
;   interpret act, live, mem, step, tab as UNIVERSALLY FALSE.
;     * (act i) is false      -> assertions 1 and 2 are vacuously true;
;     * (mem u v base) false  -> assertion 3 is vacuously true;
;     * (tab e0 i) false      -> assertion 4's negated existential holds.
;   So `sat` is correct, `unknown` is a sound incompleteness, and `unsat` is a
;   wrong refutation.
;
; Ingredients, each necessary (removing any one turns AY's answer into a sound
; `unknown`):
;   1. the one-point idiom  (exists ((j Idx)) (and (= j i) (tab u j)))  -- which
;      is logically just (tab u i); inlining it by hand makes the bug vanish;
;   2. a biconditional body under a universal guarded by a predicate;
;   3. a vacuous guard axiom (act -> live) whose consequent occurs nowhere else.
;
; Two further measurements that narrow it (2026-07-26, 0.4.0+build.5825):
;   * Rewriting the `(= A B)` below as the LOGICALLY IDENTICAL
;     `(and (=> A B) (=> B A))` changes AY's answer from `unsat` to `unknown`.
;     So the defect is sensitive to the Boolean-equality (iff) form itself, and
;     the dual-polarity normalization of the existentials inside it is the prime
;     suspect.
;   * `-st` on this file reports `:conflicts 0 :decisions 0 :propagations 7`
;     with `:ematching-instances-created 9`. An `unsat` with ZERO conflicts is
;     not a search result: some E-matching instance is being emitted that is not
;     a consequence of the assertion, and unit propagation then closes it. Look
;     at instance generation, not the SAT core.
(set-logic AUFLIA)
(set-info :status sat)
(declare-sort Elt 0)
(declare-sort Rel 0)
(declare-sort Idx 0)
(declare-fun act (Idx) Bool)
(declare-fun live (Idx) Bool)
(declare-fun mem (Elt Elt Rel) Bool)
(declare-fun step (Idx Rel) Bool)
(declare-fun tab (Elt Idx) Bool)
(declare-fun base () Rel)
(declare-fun e0 () Elt)
(assert (forall ((i Idx)) (=> (act i) (live i))))
(assert (forall ((i Idx))
  (=> (act i)
      (forall ((u Elt) (v Elt))
        (= (and (exists ((w Rel)) (and (step i w) (mem u v w)))
                (exists ((j Idx)) (and (= j i) (tab u j))))
           (and (mem u v base)
                (exists ((k Idx)) (and (= k i) (tab u k)))))))))
(assert (forall ((u Elt) (v Elt))
  (=> (mem u v base)
      (exists ((i Idx) (w Rel)) (and (step i w) (mem u v w))))))
(assert (not (exists ((i Idx)) (tab e0 i))))
(check-sat)
