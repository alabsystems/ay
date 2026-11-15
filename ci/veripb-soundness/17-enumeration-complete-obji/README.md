# 17 — `ENUMERATION_COMPLETE` trusts a contradiction of any provenance (FIXED in the fork)

Six proof lines certify "this formula has **0** solutions" for a formula with three.

|                                |                                                                        |
| ------------------------------ | ---------------------------------------------------------------------- |
| formula                        | `enum.opb` — `min: x1 + x2`, `preserved: x1 x2`, the clause `x1 ∨ x2` |
| proof                          | `enum.pbp` (six lines)                                                 |
| **unfixed verdict**            | `s VERIFIED COMPLETE ENUMERATION OF 0 SOLUTIONS`, exit 0                |
| **truth**                      | **3 solutions** over the preserved set: `11`, `10`, `01`               |
| present in stock upstream `4bb10c2c` | yes                                                                    |
| present with `0001` only       | **yes**                                                                |
| present with the pinned patch | no — rejected, no `s` line                                             |

## The bug

`conclusion ENUMERATION_COMPLETE n` claims the problem has **exactly** the `n` solutions
the proof excluded. Its two checks (`veripb-checker/src/rules/conclusion.rs`) are:

```rust
let actual_sol = BigInt::from(context.num_excluded_solutions);
if expected_sol != actual_sol { return Err(MismatchEnumeratedSolutions(…)); }
self.inner.constraint_id_hint = Some(check_contradiction(self.inner.constraint_id_hint, database)?);
```

`num_excluded_solutions` counts **only** `solx` exclusions
(`veripb-checker/src/rules/solution_logging.rs`), and `check_contradiction` accepts **any**
contradicting constraint with no test of where it came from.

The argument the rule is making is "the original constraints plus the exclusions are
contradictory, therefore the exclusions were all the solutions". That needs the
contradiction to come from the originals and the exclusions **and nothing else**. An
*objective-restricting* constraint breaks it: `obji v` installs `objective ≤ v-1`, which
removes every solution that is not strictly better than `v`, and it is not counted. Pick
`v` at or below the optimum and the database is contradictory on its own — with all three
solutions still sitting there, un-excluded and un-counted.

## Evidence chain

```
f 1 ;                                   % min: x1 + x2 ;  preserved: x1 x2 ;  x1 v x2
obji 1 ;                                % installs "objective <= 0", i.e. ~x1 and ~x2
rup >= 1 ;                              % which contradicts the clause. 0 exclusions logged.
conclusion ENUMERATION_COMPLETE 0 : 3 ; % 0 == num_excluded_solutions, and 3 contradicts
```

## The pair that needs no external oracle

`truth.pbp` is the same formula and the same binary, enumerating the three solutions
honestly with `solx` and concluding `COMPLETE ENUMERATION OF 3 SOLUTIONS`, exit 0, before
and after. One checker, one formula, "0 solutions" and "3 solutions".

```bash
veripb --opb enum.opb enum.pbp    # rejected (unfixed: COMPLETE ENUMERATION OF 0 SOLUTIONS)
veripb --opb enum.opb truth.pbp   # COMPLETE ENUMERATION OF 3 SOLUTIONS, before and after
```

## `variants/`

| variant | reach path / knob | unfixed | fixed |
| --- | --- | --- | --- |
| `soli-route/soli.pbp` | the same forgery through `soli … : 1;`, which installs the same constraint *and* logs a solution — five lines, on a formula with no preserved set at all | `COMPLETE ENUMERATION OF 0 SOLUTIONS` | rejected |
| `controls/obji.pbp` | the same forgery on a one-variable formula (the base for the two knobs below) | `COMPLETE ENUMERATION OF 0 SOLUTIONS` | rejected |
| `controls/no-obji.pbp` | **one knob**: drop the `obji`, keep the `rup` and the conclusion | rejected | rejected |
| `controls/count-1.pbp` | **one knob**: keep the `obji`, claim `1` instead of `0` | rejected | rejected |

`controls/no-obji.pbp` is the causation argument: without the objective-restricting
constraint there is no contradiction to point at and the **unfixed** checker refuses the
identical proof, so the forgery is `obji`'s constraint and not "`ENUMERATION_COMPLETE` is
broken". `controls/count-1.pbp` shows the count check itself works — it is the
*provenance* of the contradiction that was never tested.

The positive control lives at the top level: `truth.pbp` is a legitimate
`ENUMERATION_COMPLETE` that must keep verifying, and it does. Upstream's
`correct/version3/solution_logging_excluding.*` and `.../solution_checking_solx.*` are two
more.

## The fix (now in the fork; formerly ay patch `0002`)

`solx` marks the constraint it installs `is_solution_excluding` and `soli`/`obji` mark
theirs `is_objective_restricting` (`veripb-formula/src/db_constraint.rs`). The
`EnumerationComplete` arm refuses when
`Database::first_objective_restricting()` finds one still in the database.

Provenance on the **constraint** rather than in a checker-wide flag is the point: a proof
that installs an objective-restricting constraint, uses it, and deletes it again is back to
reasoning about the original solution set, and `first_objective_restricting()` returns
`None` for it. A sticky "an `obji` happened" flag could not express that.

`ENUMERATION_PARTIAL` is deliberately **not** gated, and the code says why: it rests on no
database contradiction at all. Its count is `num_excluded_solutions`, and every solution
counted there was checked against the database at the moment it was logged, so restricting
the objective can only ever make that count *smaller*. Gating it would be an over-broad
restriction with no wrong verdict behind it.

The instance pairs
`tests/instances/incorrect/version3/enumeration_complete_objective_improving.*` and
`.../enumeration_complete_solution_improving.*` ride in the patch.
