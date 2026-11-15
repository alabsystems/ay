# 11 — propagation slack computed in the row's own width (FIXED in the fork)

The most severe of the ten defects. While it was open, **no `s VERIFIED UNSATISFIABLE`
from this checker was evidence of anything, for any formula**: the poison rides entirely
in the proof, so a three-line derivation forges the verdict against an ordinary
satisfiable clause. Every RUP-backed auto-discharge — `pbc`, redundancy proof goals,
checked deletion — was granted for free by the same mechanism.

|                                |                                                                     |
| ------------------------------ | ------------------------------------------------------------------- |
| formula                        | `plain.opb` — `1 x1 1 x2 >= 1 ;`, i.e. the clause `x1 ∨ x2`          |
| proof                          | `plain.pbp` (4 rule lines)                                          |
| **unfixed verdict**            | `s VERIFIED UNSATISFIABLE`, exit 0, with default flags               |
| **truth**                      | **SATISFIABLE** — three of the four assignments are models           |
| present in stock upstream `4bb10c2c` | yes                                                                 |
| present with `0001` only       | **yes**                                                             |
| present with the pinned patch | no — rejected, no `s` line                                          |

## The bug

`veripb-propagator/src/general_pb_watcher.rs`, three sites — the level-0 propagation scan
(`get_assignment_independent_propagations`), the watch-elision test (`no_watches_required`)
and the level-0 propagation test (`is_propagating_independent_of_assignment`) — each did:

```rust
let slack = pb_constraint.get_coeff_sum() - pb_constraint.get_degree();
```

Both operands fit the row's integer type `N`. Their **difference need not**. For
`2 x1 >= -9223372036854775806` the true slack is `2 + 9223372036854775806 = 2^63`, one past
`i64::MAX`, and the release profile disables overflow checks, so it became `i64::MIN`.

Every coefficient is then "greater than the slack", which is the propagator's test for
*this term propagates regardless of the assignment*. So a **trivially true** row was
reported to propagate **all** of its literals unconditionally.

## Evidence chain

`plain.opb` is `x1 ∨ x2`. The proof:

```
f 1 ;
rup 2 x1  >= -9223372036854775806 ;   % trivially true, so RUP accepts it — legitimately
rup 2 ~x1 >= -9223372036854775806 ;   % likewise
rup >= 1 ;                            % the empty contradiction
conclusion UNSAT : 4 ;
```

Lines 2 and 3 are **honest**: a trivial conclusion is a valid RUP conclusion, and the
database after them is still equivalent to the formula. Nothing is forged yet. But with the
wrapped slack, row 2 asserts `x1` and row 3 asserts `~x1` at level 0, so the trail is in
conflict before line 4 starts — and a trail in conflict RUPs *anything*, including the
empty constraint.

## The pair that needs no external oracle

`sat.pbp` is the same formula and the same binary with a logged model. It answers
`s VERIFIED SATISFIABLE`, exit 0. One checker, one formula, both verdicts — so the false
`s VERIFIED UNSATISFIABLE` is visibly false without trusting any second tool.

That half is also the guard against a bogus fix: a "fix" that simply made the propagator
refuse rows with extreme degrees would satisfy the negative test and break this one.

```bash
veripb --opb plain.opb plain.pbp   # rejected (unfixed: s VERIFIED UNSATISFIABLE)
veripb --opb plain.opb sat.pbp     # s VERIFIED SATISFIABLE, before and after
```

## `variants/`

Not rows — `expected.tsv` carries one pair per row and `plain` is the universal form — but
they are what makes the diagnosis exact.

| variant | what it is | unfixed | fixed |
| --- | --- | --- | --- |
| `formula-borne/` | the same defect reached straight from the formula: two trivially true rows, one over `x1` and one over `~x1`, so `rup >= 1 ;` on line 2 suffices | `VERIFIED UNSATISFIABLE` | rejected |
| `formula-borne/sat.pbp` | the same formula and binary with a model | `VERIFIED SATISFIABLE` | `VERIFIED SATISFIABLE` |
| `boundary-control/` | **one off the boundary**: every degree raised by 1, so the slack is exactly `i64::MAX` and nothing wraps | rejected | rejected |

`boundary-control/` is the causation argument. It is the identical proof shape against a
formula one unit away, and it is refused by the unfixed checker too — so the forgery is the
**wrap**, not "large numbers confuse the checker".

## The fix (now in the fork; formerly ay patch `0002`)

`Slack` (`veripb-formula/src/pb_constraint.rs`) computes `coeff_sum - degree` with
`checked_sub` and falls back to `BigInt` when the difference leaves `N`, then answers the
only two questions the propagator asks of a slack — *is it positive* and *does this
coefficient exceed it* — against the exact value. The hot path keeps machine arithmetic and
gains one branch; the wide path is unreachable from any solver-emitted degree.

The comparisons are exact rather than clamped, so a legitimately propagating constraint is
unaffected: `veripb-propagator/tests/general_pb.rs` carries that control
(`ordinary_slack_still_propagates`) alongside the overflow cases, and the whole
i64/i128 boundary was swept — `i64::MIN`, `i64::MIN + 1`, `i64::MIN + 2`, the exact-`i64::MAX`
slack, and the same four one width up — with every wrapping case closed and every
non-wrapping case unchanged.
