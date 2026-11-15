# Persistent SAT solver: a refutation flag that outlived its scope (found 2026-09-23)

Differential fuzzing of random incremental (push/pop) QF_NIA and QF_LRA scripts found one
family of defects in the `has_empty_clause` state machine of the session-persistent SAT
solver (`ay-sat`), reached from two ay-dpll lanes. Reproduced on ay `387b3c1cf`, debug CLI,
`--competition`:

```
nia_stale_depth_min.smt2           unsat unsat unknown   BUG: persistent SAT solver has_empty_clause=true BEFORE solve() in split loop
nia_base_level_min.smt2            unsat unknown         (the same assertion)
lra_attach_refutation_min.smt2     sat unknown           BUG: propagate_bcp_unsafe called with has_empty_clause=true
lra_retracted_refutation_min.smt2  unsat unknown         BUG [#8078]: BCP missed conflict!
```

The panic is caught per command, and every later check-sat of the script answers `unknown`
too. With the fix, every script here answers without a debug assertion and without
`unknown`, in both the `--competition` and the default posture.

## Files

| file | what it shows |
|---|---|
| `nia_stale_depth_min.smt2` | ddmin of `corpus/nia_split_loop_seed3.smt2`: a stale refutation. The refutation of the second check-sat is derived in the split loop's private frame (depth 2) but recorded at depth 1, the depth an earlier, already-retracted refutation left behind; the frame's own `pop()` does not retract it and the third check-sat trips the assertion. Proof-free posture only. |
| `nia_base_level_min.smt2` | ddmin of `corpus/nia_split_loop_seed0.smt2`: a legitimate base-level refutation. Check-sat 1 refutes the shared persistent solver at depth 0 (permanent by design); check-sat 2 enters the NIA split loop with it and the assertion forbade that state. Both postures. |
| `nia_stale_depth_sat_base.smt2` | the stale-depth shape with satisfiable check-sats around every refuting scope. Answered correctly before the fix too; it pins the retraction contract. |
| `lra_attach_refutation_min.smt2` | ddmin of `corpus/lra_bcp_seed5.smt2`: the incremental QF_LRA engine lane's state-preserving reset attaches `(= c 6)` against the level-0 bound `c < 5/4`, refuting the database during the attach; the extension solve then ran BCP on a refuted database. |
| `lra_retracted_refutation_min.smt2` | ddmin of the planted-model script `corpus/lra_finalize_seed193.smt2`: `(or p q) (not p) (not q)` is refuted while one scope is live, `pop()` retracts the refutation, and the next solve resumed from the level-0 trail that had already consumed the conflict. |
| `lra_retracted_refutation_deep.smt2` | the same across several scopes, with satisfiable check-sats before the contradiction. |
| `corpus/nia_split_loop_seed*.smt2` | 15 random QF_NIA scripts (generator seeds in the names) that trip the split-loop assertion under `--competition`. |
| `corpus/lra_bcp_seed*.smt2` | 17 random QF_LRA scripts that reach `propagate_bcp_unsafe` with `has_empty_clause=true`. |
| `corpus/lra_finalize_seed*.smt2` | 10 planted-model QF_LRA scripts (a satisfiable prefix, then one depth-0 contradiction) that reach the retracted-refutation path. In `lra_finalize_seed3028.smt2` the lane's fallback does not rescue the verdict (see Release effect). |

41 of the corpus scripts were found on `b26f916e0` among 200, 200 and 300 scripts from
scratch generators that are not in the tree, and `lra_finalize_seed3028.smt2` on
`d7042cc5b` among 100 more planted-model scripts (seeds 3000-3099). Each declares three
constants (plus two Booleans in the planted-model ones) and has 31 commands after its
declarations (33 to 40 in the planted-model ones). On `387b3c1cf` (debug CLI) the 41 trip
their signature under `--competition`; in the default posture all 17 `lra_bcp`, 7 of the 10
`lra_finalize` and 2 of the 15 `nia_split_loop` scripts do. Seed 3028 trips none of the
three assertions; it prints `FINALIZE_SAT_FAIL` and answers `unknown` at its last
check-sat, in debug and release builds and in both postures.

## Root cause (ay-sat)

`Solver::pop()` retracts the refutation when the scope depth recorded for it exceeds the
depth being popped to, and a depth-0 refutation is permanent. Three things broke that:

1. Not every raise of the flag recorded the depth it happened at. The proof-free level-0
   conflict path (`record_level0_conflict_chain`) used `empty_clause_scope_depth == 0` as
   its first-occurrence test, and `pop()` never reset that field after a retraction, so a
   later refutation inherited the depth of an earlier, retracted one; `reduce_db`'s
   out-of-order-unit propagation raised the flag without recording a depth at all, and
   `clone_for_incremental` copied the flag but reset its depth to 0. Every raise now goes
   through `raise_empty_clause_flag` (records the depth on the false -> true transition)
   and every retraction through `lower_empty_clause_flag`.
2. A retraction relied on the next solve deriving the refutation again, but the
   state-preserving incremental reset (the inc-engine lane: `set_ic3_mode` +
   `set_inc_engine_reset_mode`) resumed from the level-0 trail whose conflict had already
   been consumed. A retraction now forces the next reset to be a full one, with a full
   watch rebuild.
3. `attach_new_clauses_incremental` stopped at the first falsified clause while recording
   every new clause as attached, so the rest were missing from the arena until a full
   reset's clause census noticed the difference. It now keeps the arena complete, and the
   assumption and extension solves answer `unsat` right after an incremental reset whose
   attach refuted the database, instead of running BCP on it (the IC3 query loop and its
   incremental inprocessing already check the flag before they propagate).

The split-loop assertion in ay-dpll (`pipeline_incremental_split_lazy_macros.rs`) forbade
any refutation, including a legitimate base-level one; it now rejects only a refutation
recorded at the loop's own frame depth or deeper, which `pop()` retracts. Everything the
loop adds inside its frame carries the frame's selector, so a refutation at that depth can
only be one a `pop()` failed to retract.

## Release effect

In the proof-free posture the flag is raised only by a level-0 conflict, and no clause
guarded by a live scope's selector can be falsified at level 0, where that selector is
never false (it enters the search only as an assumption); a flag that outlives its scope
there still describes a refutation of the live formula. Measured on `387b3c1cf`, and again
with the same counts on `75e539df0` (release CLI), over the 42 corpus scripts and the 6
minimized ones, 505 check-sats per posture: in both postures 504 have a definite verdict,
every one of them agrees with a fresh non-incremental solve of that check-sat's live
assertions (by the same release build), and 189 of them also have a witness on a small grid
(they are `sat`). The release harm is on the retraction path: `FINALIZE_SAT_FAIL` (the SAT
core returned an assignment violating an original clause, which the finalize check turns
into `unknown`) in 12 files under `--competition` (all 10 `lra_finalize` scripts and both
`lra_retracted_refutation` ones) and in 10 in the default posture. The lane then fell back
to the standalone solver, which answered correctly, except at the last check-sat of
`lra_finalize_seed3028.smt2`: the solver's `FINALIZE_SAT_FAIL` count is sticky across
solves, and after the earlier failures in that script it downgraded the depth-0 `unsat` to
`unknown` (`FINALIZE_SAT_FAIL_POISON`), which is what the CLI printed. On the 300 scratch
scripts of seeds 3000-3099, `FINALIZE_SAT_FAIL` appears in 2 files per posture. No
reference solver (z3, cvc5) is installed on the machine these numbers come from, which is
why the comparison is against a fresh solve and a solver-independent grid.

At the SAT-solver API the defects are directly observable in release (on `387b3c1cf` and on
`75e539df0`, 7 of the 8 tests of `empty_clause_scope_lifecycle.rs` fail): the flag survives
the pop of the scope it was derived in, a base-level refutation is retracted by an
unrelated pop, a clone of a proof-producing solver answers `unsat` for a satisfiable
formula after the pop, and an unsatisfiable formula answers `unknown` after a retraction.

With the fix (release CLI, on `75e539df0`), over the same 48 scripts in both postures: no
`FINALIZE_SAT_FAIL`, no `unknown`, and all 505 check-sats agree with the fresh solve (by
the `75e539df0` release build); the one verdict that changes is the last check-sat of seed
3028, `unknown` -> `unsat`. The debug-build replays of these scripts (the ay-dpll tests
below) trip no assertion. On the 300 scratch scripts (release, 60 s per script, on a
machine at load 60-80) none of the check-sats both builds answered `sat` or `unsat` (3217
under `--competition`, 3203 in the default posture) changed between the two,
`FINALIZE_SAT_FAIL` is gone, and the one `unknown` that became `unsat` is seed 3028's. The
only other differences are in scripts that hit the 60 s limit (NIA seed 3011 under
`--competition`, 3095 in the default posture), where one build got further than the other;
replayed with 600 s, each gives the same verdict sequence in both builds (3011: nine `sat`;
3095: `sat sat sat unknown unknown`, then the 600 s limit, in both).

## Not covered

With a proof manager attached (`Solver::with_proof_output`, DRAT or LRAT), proof
finalization marks the empty clause for an UNSAT under *user* assumptions too, and that
flag has no scope to be retracted with: after `solve_with_assumptions(&[!x, !y])` on
`(x | y)`, a plain `solve()` answers `unsat` with DRAT output, and after a `push()` so does
an assumption solve with `[x]` alone; with LRAT text output the assumption solve and the
plain solve both answer `unknown`. Measured in release on `387b3c1cf`, on `75e539df0` and
with this fix. No non-test code in ay's crates combines proof output with assumptions on a
solver (the BV lane refuses DRAT output with check-sat-assuming, on a fresh solver); it is
reported separately, because the fix needs a decision about the proof stream (what an
assumption UNSAT terminates in, and how it is retracted), not only about the flag.

## Regression tests

- `crates/ay-sat/tests/group_incremental/empty_clause_scope_lifecycle.rs`: the SAT-level
  contract, on verdicts and the public flag; on `387b3c1cf` and on `75e539df0` 7 of its 8
  tests fail in release and all 8 in debug (the eighth, the attach refutation in an
  extension solve, is the debug-only `propagate_bcp_unsafe` assertion).
- `crates/ay-sat/src/solver/tests/incremental_attach_refutation.rs`: the attach keeps every
  clause it records as attached; both tests fail on `387b3c1cf` and on `75e539df0`.
- `crates/ay-dpll/tests/group_nonlinear/nia_split_loop_empty_clause_scope.rs` and
  `crates/ay-dpll/tests/group_lra/lra_inc_engine_empty_clause_scope.rs`: the minimized
  scripts and the whole corpus, every `sat` checked against its model and every `unsat`
  against a fresh non-incremental solve (`tests/common/incremental_script.rs`). On
  `387b3c1cf` and on `75e539df0` 8 of their 9 tests fail in debug (the ninth pins
  `nia_stale_depth_sat_base.smt2`, which was answered correctly before); in release the
  finalize-corpus replay fails, on seed 3028's `unknown`.

Each part of the ay-sat fix is load-bearing. With the rest of the fix in place over
`75e539df0` and one part removed at a time (release builds unless noted): the old depth
bookkeeping fails the retraction and base-level-survival tests; the clone's depth reset
fails both clone tests (the clone answers `unsat` for an empty formula); dropping the
forced full reset fails the three inc-engine re-derivation tests (`unknown`); the attach's
early stop fails both attach unit tests (the lifecycle tests still pass, because the full
reset that follows a retraction counts the arena's clauses and rebuilds it); dropping the
early `unsat` after an incremental reset fails the extension attach-refutation test, in a
debug build only.
