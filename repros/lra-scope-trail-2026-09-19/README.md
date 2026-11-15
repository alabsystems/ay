# LRA scope-trail: BCP-batching window, end-to-end attempts (2026-09-19)

Companion to the development design notes §2. The deterministic repro of the window is
the extension-level test `crates/ay-dpll/src/extension/tests_lra_scope_trail.rs` on branch
`lra-scope-trail-fix`; these files document the end-to-end attempt against the release binary.

## Files

| file | what it shows |
|---|---|
| `batching_engages_fillers_only_n1300.smt2` | 1,300 independent `f_i >= 0 xor g_i <= 0` pairs: a conflict-free descent of 1,300 decisions. `ay --competition --stats-full` reports `dpll.eager.batch_defers 139` (phase-2 batching, streak ≥ 1024): the production path that applies a round's atoms one theory scope too high IS reached on real runs. z3/ay: `sat`. |
| `gen_batching_gadget.py N m` | fillers + the UNSAT gadget `x >= 0` forced (via `k >= 0` / `not (k >= 0)`), `f_m >= 0 → x <= -1`, `not (f_m >= 0) → x < 0`. Wrong `sat`/`unknown` needs: `x >= 0` decided in a round smaller than the batch target after ≥ 512 checked rounds, its partner `f_m` decided later, and the learned clause `¬(x>=0) ∨ ¬f_m` backjumping into `x >= 0`'s level. |

## What was observed

`ay` (a release build of commit `25e6683cf`) and z3 5.1.0 agree (`unsat`) on every generated
variant (N 1,000..3,120, TermId padding 0..120, `(set-option :random-seed ..)` 1..12 — no effect
on this lane). `dpll.eager.batch_defers` ranged 0..788 depending on where the hash-ordered
theory-decision walk (`decision_index`, `theory_solver/mod.rs:844-861`) and VSIDS placed the
gadget: whenever it was placed early (decisions 2..60) the gadget was resolved before batching
armed; when placed late (decisions 1,300..3,600, defers 155..788) the gadget's atoms were decided
in an order that did not produce the backjump-into-deferred-level shape.

Not a proof of absence: the extension-level test shows the production sequence loses the bound
whenever the shape occurs; the model gate (always on, every rigor level) would publish `unknown`
for the resulting wrong theory model.
