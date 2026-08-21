# The finite-model FP lane's universal branch: what actually reaches it

Two one-line fixtures that settle a question the adversarial review of
`inc-fp-no-complete-lane-for-a` got wrong, and that the branch's measured
number does not answer.

Reproduce with a `--debug-cert` build; the lane prints
`FMQ leaf-census: total=N universal=N refinable=N` once per classification
pass (`executor/finite_model_mbqi.rs`).

    ay --z3-mode --debug-cert -T:60 <file>

## `positive_forall_never_reaches_lane.smt2`

A top-level `(forall ((x Float32)) ...)`. **The lane never runs** — zero `FMQ`
lines. An authored assertion containing a literal FP `forall` sets
`has_unsafe_partial_quantifiers` (`quantifier_loop/mod.rs`) and the query fails
closed upstream. Answer: `unknown`.

This is the shape the review probed, four times, which is why it concluded the
wrong-UNSAT below was untriggerable.

## `negated_forall_reaches_lane.smt2`

The same universal under a `not`. **The lane DOES run**, and the leaf is
classified `universal=1` — the upstream guard is polarity-sensitive and does
not block this spelling. Answer: `sat`, which is correct (`c = 0`, `x = 1.0`
falsifies the inner universal).

The `refinable` flag on that leaf is the whole safety margin:

| binary | census |
|---|---|
| pre-fix | `total=1 universal=1 refinable=1` |
| post-fix | `total=1 universal=1 refinable=0` |

Pre-fix, this leaf was eligible to have a ground instance `body[v]` ASSERTED
and a resulting UNSAT published as a definite refutation — of a problem that
asserts `¬∀x.body` and entails no instance of `body` at all. So the defect's
precondition is reachable from the CLI on an ordinary input, not gated behind
an unrelated guard as the review believed.

What still has to line up for an end-to-end wrong `unsat` is
`TruthOutcome::Refine`, which needs a sub-solve to come back INCONCLUSIVE
rather than refuting. With a total pin set and a ground matrix, that
refutation normally succeeds inside the 2 s budget and the value is
`Determined` instead — which is why no end-to-end wrong `unsat` was produced
here, and why the branch's own corpus never exercised the branch (see below).
It is a timing margin, not a guard.

## The measured corpus does not touch any of this

All ten SMT-COMP 2025 Incremental FPArith files contain **1,152 `(exists` and
zero `(forall`**. A census over all ten (`--debug-cert`, `-T:45`) recorded
**280 classification passes with `universal=0` and `refinable=0` in every
one**. The universal branch, the refinement loop, and the lane's only
definite-UNSAT return are entirely unexercised by that corpus; the measured
gain comes solely from the existential path.


## Corrected 2026-08-20 after review

Two fixture names asserted a mechanism the code refutes:

- `negated_exists_disjunctive_now_decides.smt2` was named for a change it does
  NOT demonstrate — it already decides on main, via the
  `independent_gate.rs:4302` producer (main's trace shows
  `FMQ gate-hook: installed=true` with no `last-chance` line). Renamed to
  `..._decides_on_main_too.smt2`.
- `positive_forall_never_reaches_lane.smt2` — "never reaches the lane" is false
  on the gained population: 8 of 8 sampled gained indices print `FMQ enter`.
  Renamed to `positive_forall_declines.smt2`, which is what it actually shows.

None of these four fixtures discriminates the last-chance hook: all four are
answer-identical on main and branch. The discriminating case is the rlim slice
at index 103 (main `unknown`, branch `sat`, both oracles `sat`), and a
hand-minimised 8-line variant does NOT discriminate — the surrounding assertion
stack is load-bearing, so do not trust a shrunk version without re-running the
pre-hook binary on it.
