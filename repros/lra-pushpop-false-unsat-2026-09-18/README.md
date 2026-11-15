# Incremental QF_LRA push/pop: false `unsat` under `--competition` / `--no-proof` (found 2026-09-18)

Discovered by the CHC campaign's query-replay microbenchmark
(the development design notes): replaying AY's own PDR
query stream for `sally-chc-benchmarks/oral_messages/om1_with_relays_agreement_000` as ONE
push/pop session, `ay` answered `unsat` on 16/442 (and 6/275) scopes that z3 and a fresh `ay`
per query both answer `sat`.

```
ay 0.27.0+build.10305 @ 25e6683cf (release):
  ay --competition <file>   -> sat sat unsat unsat unsat unsat     # WRONG on scope 6
  ay <file>                 -> sat sat unsat unsat unsat unknown   # self-check demotes ("forged UNSAT")
  z3 5.1.0 <file>           -> sat sat unsat unsat unsat sat
  last scope alone (fresh)  -> sat
```

## Files (every one reproduces on 25e6683cf; all-`sat` where z3 says `sat` after the fix)

| file | scopes | what it shows |
|---|---|---|
| `om1_pushpop_wrong_unsat_min_small.smt2` | 6 | original 5.9 KB extract of the PDR query stream: `sat sat unsat unsat unsat unsat` (z3: `... sat`) |
| `om1_pushpop_wrong_unsat_ddmin_6scopes.smt2` | 6 | ddmin over assertions: `sat sat sat sat sat unsat` (z3: all `sat`); scope 3 is EMPTY |
| `pushpop_selector_alias_min_3vars_6scopes.smt2` | 6 | 3 reals: `(not (= O1 P1))`+`(<= 3 S1)`, `S1=0`, empty, `S1=0`, `S1=0`, `(not (= O1 P1))`+`(<= 3 S1)` -> last is `unsat` |
| `pushpop_selector_alias_no_empty_scope.smt2` | 6 | same with the empty scope replaced by a 4th `S1=0` scope: the empty scope is NOT essential |
| `pushpop_selector_alias_7scopes.smt2` | 7 | one more `S1=0` scope: still wrong (the count of DEAD selectors is what matters) |

Dropping ONE of the `S1=0` scopes, dropping scope 1, or dropping the disequality makes every
variant answer correctly -- by luck, see below.

## Root cause (established 2026-09-18, see the development design notes)

The `#lra-inc-engine` lane runs the split loop on a SESSION-persistent SAT solver whose SMT
push/pop is mirrored as SAT scope selectors. Every `Solver::push()` mints a selector variable
through `new_var_internal`, which does NOT advance `user_num_vars`; `pop()` never frees it and
adds the unit `[+selector]`, so a popped ("dead") selector is a variable forced TRUE at level 0.

The split loop seeded its fresh-variable cursor as
`local_next_var = solver.user_num_vars() + solver.scope_depth()` — which counts only the LIVE
selectors. After enough pops without a new Tseitin allocation, the dead selectors sit above
`user_num_vars`, and the disequality split `(not (= O1 P1))` -> `O1<P1 \/ O1>P1` minted its two
new atoms onto two dead selectors: both TRUE at level 0, the LRA theory sees `O1<P1 /\ O1>P1`,
reports a conflict, and the lane publishes `unsat`. With fewer dead selectors one atom aliases
the LIVE selector (assumed false) and the check happens to come out `sat`.

Fix: seed and re-floor the cursor at `solver.total_num_vars()` at every minting site
(`crates/ay-dpll/src/executor/theories/split_incremental.rs::fresh_sat_var_floor`), which by
construction can never alias an existing variable. Regression:
`crates/ay-dpll/tests/group_lra/lra_inc_engine_pushpop_selector_alias.rs`.
