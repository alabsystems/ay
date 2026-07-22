; Reproducer for Z3 issue #7167 — TransitiveClosure + quantifiers extremely slow.
; Source: https://github.com/Z3Prover/z3/issues/7167
; Symptom: Combining sequences and quantified axioms over a binary relation's
; transitive closure causes Z3 to loop or become extremely slow. This is a
; minimized scaffold: a reachability-style axiom over an uninterpreted binary
; relation R with a universally-quantified transitivity rule.
; Expected: sat is acceptable; soundness-only baseline.
; Theory: UF + quantifiers.
;
; Author: Andrew Yates <andrewyates.name@gmail.com>
(set-logic UF)
(declare-sort N 0)
(declare-fun R (N N) Bool)
(declare-fun TC (N N) Bool)
(declare-const a N)
(declare-const b N)
(declare-const c N)
(declare-const d N)
(assert (forall ((x N) (y N)) (=> (R x y) (TC x y))))
(assert (forall ((x N) (y N) (z N)) (=> (and (TC x y) (TC y z)) (TC x z))))
(assert (R a b))
(assert (R b c))
(assert (R c d))
(assert (distinct a b c d))
(assert (TC a d))
(check-sat)
