# 19 — `conclusion BOUNDS` trusts a contradiction built from `solx` (FIXED in the fork)

|                                |                                                                          |
| ------------------------------ | ------------------------------------------------------------------------ |
| formula                        | `bounds.opb` — `min: 7 z1 + 3 z2`, `preserved: p1 p2`, three clauses     |
| proof                          | `bounds.pbp` (four `solx`, two `rup`, a conclusion)                       |
| **unfixed verdict**            | `s VERIFIED BOUNDS 10 <= obj <= 10`, exit 0                              |
| **truth**                      | the optimum is **0** — `~p1 ~p2 q1 ~z1 ~z2` satisfies every clause at cost 0 |
| present in stock upstream `4bb10c2c` | yes                                                                      |
| present with `0001` only       | **yes**                                                                  |
| present with the pinned patch | no — rejected, no `s` line                                               |

## The bug

The lower-bound branch of `conclusion BOUNDS`
(`veripb-checker/src/rules/conclusion.rs`) short-circuits:

```rust
if context.best_objective_value.as_ref().is_some_and(|best| bound > best) {
    return Err(ConclusionBoundsLBLargerBestSolution);
}
…
if let Some(contradicting_id) = database.contains_contradiction() {
    self.inner.constraint_id_hint = Some(contradicting_id as isize);   // <- granted
} else {
    … check_implication(…)
}
```

So any lower bound not better than the best **logged** objective value is granted the moment
the database contains **any** contradiction. That is right for the ordinary
branch-and-bound argument, where the contradiction comes from an objective-improving
constraint `objective ≤ best-1` and really does say "nothing better than `best` exists".

It is wrong for a contradiction assembled out of `solx` exclusions. Those **remove
solutions**; they do not follow from the problem. Log the four settings of the preserved
pair `{p1,p2}` with `solx`, and the exclusions alone are contradictory — while the best
value *logged* is 10, because every logged solution was one of those four, and the cost-0
solution was never logged and has just been excluded.

Note that deleting the short-circuit does **not** fix this. With a contradicting database
the fallback `check_implication` succeeds by propagation for any target at all. It is the
exclusions that must not be live.

## Evidence chain

```
f 3 ;
solx p1  p2  q1 z1 z2 ;   % four solx lines exclude all four settings of {p1,p2},
solx p1 ~p2  q1 z1 z2 ;   % each logging objective value 7+3 = 10
solx ~p1 p2  q1 z1 z2 ;
solx ~p1 ~p2 q1 z1 z2 ;
rup 1 ~p1 >= 1 ;          % the exclusions alone now propagate to conflict
rup >= 1 ;
conclusion BOUNDS 10 10 ; % 10 <= best logged (10), and the database contradicts
```

## The pair that needs no external oracle

`truth.pbp` is the same formula and the same binary, logging the cost-0 solution and
certifying `s VERIFIED BOUNDS 0 <= obj <= 0`, exit 0, before and after. One checker, one
formula, `10` and `0`.

```bash
veripb --opb bounds.opb bounds.pbp   # rejected (unfixed: s VERIFIED BOUNDS 10 <= obj <= 10)
veripb --opb bounds.opb truth.pbp    # s VERIFIED BOUNDS 0 <= obj <= 0, before and after
```

## `variants/`

| variant | reach path / knob | unfixed | fixed |
| --- | --- | --- | --- |
| `large-bound/big.pbp` | the same construction with a bound of `7000003`, to show the number is free | `VERIFIED BOUNDS 7000003 <= obj <= 7000003` | rejected |
| `controls/fourth-solx-is-sol.pbp` | **one knob**: the fourth `solx` becomes a plain `sol`, so three exclusions remain and the database no longer contradicts | rejected | rejected |
| `controls/no-rup.pbp` | **one knob**: drop the final `rup >= 1;` | rejected | rejected |
| `branch-and-bound/bnb.pbp` | **POSITIVE**: the ordinary optimisation argument — `soli` logs the value-1 solution, installs `objective ≤ 0`, that contradicts the formula, `conclusion BOUNDS 1 1` | `VERIFIED BOUNDS 1 <= obj <= 1` | `VERIFIED BOUNDS 1 <= obj <= 1` |

`controls/fourth-solx-is-sol.pbp` is the causation argument: one exclusion fewer and there
is no contradiction to short-circuit on, so the **unfixed** checker refuses the identical
proof. The forgery is the exclusions, not `conclusion BOUNDS` and not `rup`.

`branch-and-bound/` is the over-fixing guard, and it is the shape the entire optimisation
track rests on. A fix that refused a database contradiction whenever *any* solution had
been logged — which is what the `EQUIENUMERABLE` guard next door used to do — would reject
it and every `s VERIFIED BOUNDS` AY has ever emitted.

## The fix (now in the fork; formerly ay patch `0002`)

`solx` marks the constraint it installs `is_solution_excluding`
(`veripb-formula/src/db_constraint.rs`), and the `Bounds` arm refuses when
`Database::first_solution_excluding()` finds one still in the database. Objective-restricting
constraints (`soli`, `obji`) are untouched — they are what the legitimate argument uses.

"Still in the database" is load-bearing: a proof that derives exclusions, uses them, and
deletes them again is back to reasoning about the original solution set, and this check
returns `None` for it. `num_excluded_solutions` is a counter that never decreases and could
not express that.

Marking travels with the constraint through `Database::update_unique_index`'s duplicate
merge (`DBHeader::absorb_provenance`), so an exclusion that happens to coincide with a
constraint already in the database does not lose its provenance.

The instance pair
`tests/instances/incorrect/version3/conclusion_bounds_solution_excluding.*` and the positive
`tests/instances/correct/version3/conclusion_bounds_solution_improving.*` ride in the patch.
