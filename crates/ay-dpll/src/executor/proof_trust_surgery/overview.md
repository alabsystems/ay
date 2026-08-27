Insert-and-remap surgery for proofs whose resolution skeleton is sound.
Instead of re-proving the contradiction, this pass replaces each defective
site with a certified derivation and remaps its downstream consumers.

Representative repaired site classes include the "n-ary distinct + Int
trichotomy" trust class and normalized-assume print defects. The latter need
no trust anchor: a proof whose every step is checkable can still be invalid
because a preprocessing-normalized `assume` prints unlike the problem
premise. The planners also cover the bounded derived forms documented by
their private modules.

1. **Int trichotomy trust steps** — `(cl (or (= x y) (<= x (+ y (- 1)))
   (<= (+ y 1) x))) :rule trust` plus its `or`-split consumer. Replaced by
   `la_disequality ⊢ (cl (or (= x y) (not (<= x y)) (not (<= y x))))`, an
   `or` split, and two `[1, 1]` `la_generic` Int-strengthening bridges
   (each independently re-verified by `verify_farkas_conflict_lits_full`,
   fail-closed), closed by a resolution chain that reproduces the
   3-literal strengthened clause. The trust step's unit `(cl (or ...))`
   conclusion is not re-derived: the `or`-split consumer is rewired to
   consume the derived 3-literal clause directly, and the trust step and
   split are dropped.

2. **N-ary `distinct` assumes** — the exported proof assumes the expanded
   `(and (not (= x1 x2)) ...)` form, which no checker can match to the
   problem's `(distinct x1 .. xn)` premise. Replaced by an assume of the
   raw n-ary `distinct` bridged via `distinct_elim` (pairwise `i < j`
   conjunct order), `equiv_pos2`, and resolution down to the conjunction,
   with each downstream `and_pos` or resolution unit extraction re-derived
   against the bridged conjunction.

3. **Arithmetic-normalized `and` assumes** — a bounds assertion like
   `(and .. (>= a 0) ..)` is exported with normalized conjuncts
   (`(<= 0 a)`), again unmatchable to the problem premise. Replaced by an
   assume of the raw surface conjunction, with each unit extraction
   re-derived from the raw conjunct and bridged to the canonical literal
   by a re-verified `[1, 1]` `la_generic` orientation lemma (the class-2
   raw-assume pattern).

4. **Arithmetic-normalized bound-literal assumes** — a plain bound like
   `(> a 5)` exported as the canonical `(< 5 a)`. Replaced by an assume of
   the raw surface literal bridged to the canonical unit by a re-verified
   `[1, 1]` `la_generic` orientation lemma, with every consumer remapped
   onto the derived unit. Skipped when the surviving surface overrides
   (ite-lift class) already print the literal like the file.

5. **Substituted-away equality collapses** — `substitute-and-simplify`
   eliminates a defined constant (`(assert (= v0 t))` to `v0 := t`), so the
   assertions justifying an entailed equality never reach the exported
   proof as `assume` steps and the equality itself is exported as a
   premiseless unproved unit. Repaired by re-introducing exactly those
   original assertions into the assumption prologue and closing the unit
   against them with a certified EUF recipe plus one resolution per
   premise; no assertion is invented.

A `trust`-kind theory lemma that a later, idempotent export stage certifies
in place (an array read-over-write schema re-tag, or a Skolemized
extensionality axiom's provenance promotion) is not a defect this pass may
touch. It is copied through verbatim, and the acceptance gate re-checks it
with the same predicate those stages use, on a copy with those stages
already applied. This prevents one array backbone leaf from vetoing repairs
of genuinely defective leaves elsewhere in the proof.

The pass hoists assumptions, rebuilds and remaps the step list in one pass,
and leaves the proof byte-identical on any unrecognized or unverifiable site.
