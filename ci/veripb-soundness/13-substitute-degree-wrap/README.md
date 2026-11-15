# 13 — `substitute` lowers the degree in the row's own width (FIXED in the fork)

|                                |                                                                     |
| ------------------------------ | ------------------------------------------------------------------- |
| formula                        | `sub.opb` — `1 x1 >= 1 ; 1 x2 >= 1 ;`                               |
| proof                          | `sub.pbp` (4 rule lines)                                            |
| **unfixed verdict**            | `s VERIFIED UNSATISFIABLE`, exit 0, with default flags               |
| **truth**                      | **SATISFIABLE** — `x1 = x2 = 1` is a model                          |
| present in stock upstream `4bb10c2c` | yes                                                                 |
| present with `0001` only       | **yes**                                                             |
| present with the pinned patch | no — rejected, no `s` line                                          |

## The bug

`GeneralPBConstraint::substitute` (`veripb-formula/src/general_pb_constraint.rs`) and
`Cardinality::substitute` (`veripb-formula/src/cardinality.rs`) move the coefficient of every
literal mapped to the constant TRUE from the left-hand side to the right:

```rust
Some(SubstitutionValue::TRUE) => {
    substituted_degree -= &term.coeff;      // GeneralPBConstraint
    substituted_coeff_sum -= &term.coeff;
}
Some(SubstitutionValue::TRUE) => substituted_degree -= 1,   // Cardinality
```

Both operands fit the row's integer type. Their **difference need not**. `1 x2 >= i64::MIN`
is trivially true and is accepted by both parsers; under `x2 -> 1` its true degree is
`i64::MIN - 1`, and with overflow checks off in release that became `i64::MAX` over an
**empty** left-hand side — which is exactly `degree > coeff_sum`, the empty contradiction.

The consumer is what makes this fatal. `PBConstraintGetter::implies`
(`veripb-formula/src/pb_constraint.rs`) short-circuits:

```rust
// If source constraint is a contradiction, then the target is always implied.
if self.is_contradicting() {
    return true;
}
```

That is **correct** for a genuinely contradicting row — ex falso — so the fix belongs
upstream of it: what must not exist is a row that merely *looks* contradicting. With one in
the database, `check_substituted_implication` (`veripb-checker/src/utils.rs`) reports
"implied" for every target it is asked about, and `Proofgoal::autoprove` discharges **any**
proof goal as `DBImpliesSubstituted`. The `red` step below therefore introduces `1 ~x1 >= 1`
with nothing proved at all.

Note where the extreme number lives: the poisoned row is introduced by `rup`, which accepts
it **honestly** because it really is trivially true. The formula is ordinary, so no
formula-level sanity check can catch this.

## Evidence chain

```
f 2;
rup 1 x2 >= -9223372036854775808 ;   % honest: trivially true. Stored fine.
red 1 ~x1 >= 1 : x1 -> 1 ;           % x2 propagates TRUE at level 0; substituting it into
                                     % row 3 wraps it into the empty contradiction, which
                                     % then "implies" every goal of this red step
pol 1 4 +;                           % (1 x1 >= 1) + (1 ~x1 >= 1) = the empty contradiction
conclusion UNSAT : 5;
```

## The pair that needs no external oracle

`sat.pbp` is the same formula and the same binary with a logged model, answering
`s VERIFIED SATISFIABLE`, exit 0.

```bash
veripb --opb sub.opb sub.pbp   # rejected (unfixed: s VERIFIED UNSATISFIABLE)
veripb --opb sub.opb sat.pbp   # s VERIFIED SATISFIABLE, before and after
```

## `variants/`

| variant | code path / knob | unfixed | fixed |
| --- | --- | --- | --- |
| `cardinality/card.pbp` | `Cardinality::substitute` (`1 x1 1 x2 >= i64::MIN` has all coefficients one, so `into_smallest_type()` stores it as a cardinality) | `VERIFIED UNSATISFIABLE` | rejected |
| `cardinality/card-boundary-control.pbp` | the cardinality boundary is one further out — the `-= 1` is per literal, so with two TRUE-mapped literals `i64::MIN + 1` still wraps and `i64::MIN + 2` does not | rejected | rejected |
| `general-i128/gen128.pbp` | `GeneralPBConstraint::<i128>::substitute`, degree `i128::MIN` | `VERIFIED UNSATISFIABLE` | rejected |
| `general-i128/gen128-boundary-control.pbp` | `i128::MIN + 1` | rejected | rejected |
| `order-spec/spec.pbp` | the order-SPECIFICATION surface: no `rup` at all, the poisoned row is a `spec` row and the `leq` scope substitutes the order's left variables into it | `VERIFIED UNSATISFIABLE` | rejected |
| `order-spec/sat.pbp` | the model for that variant's formula | `VERIFIED SATISFIABLE` | `VERIFIED SATISFIABLE` |
| `order-spec/control-plus1.pbp` | the same, spec degree `i64::MIN + 1` | rejected | rejected |
| `boundary-control/control.pbp` | **one knob**: `sub.pbp` with degree `i64::MIN + 1` | rejected | rejected |
| `honest-substitution/honest.pbp` | **not a forgery**: an honest `red` whose witness touches a degree-`i64::MIN` row | `VERIFIED NO CONCLUSION` | `VERIFIED NO CONCLUSION` |

`general-i128/` matters on its own: it shows the defect is a property of the **narrow-width**
code, so widening the type would move the threshold rather than close the hole.
`order-spec/` shows the wrap is not confined to `rup`-introduced rows.
`boundary-control/` is the causation argument — one unit away nothing wraps and the unfixed
checker refuses the identical proof shape.

`honest-substitution/` is the over-fixing guard: refusing rows with extreme degrees, or
clamping the substituted degree to the type's range, would satisfy every negative case above
and break this one. A clamp is not a fix; it silently replaces the constraint the proof asked
for with a different one, which is a different unsoundness.

`Clause::substitute` needs no change and got none: a clause has degree 1 and mapping a
literal to TRUE sets the degree to `0` outright, with no arithmetic to wrap.

## The fix (now in the fork; formerly ay patch `0002`)

Both implementations use `checked_sub` on the degree **and** on the coefficient sum, and on
failure redo the whole substitution in `BigInt` (`GeneralPBConstraint::substitute_widened`,
`GeneralPBConstraint::<BigInt>::from(&Cardinality)`), narrowing the result again with
`into_smallest_type()`. It escalates; it does not clamp, so what is stored is the true
mathematical degree `i64::MIN - 1` and the row stays trivially true.

The `implies()` early exit was deliberately left alone — see above.

The whole `i64`/`i128` boundary was swept: `i64::MIN`, `i64::MIN + 1`, `i64::MIN + 2`, exact
`i64::MAX`, the same four one width up, and the multi-literal cardinality case where the
boundary shifts by the number of TRUE-mapped literals. Every wrapping case is closed and
every non-wrapping case is unchanged. Six unit cases in
`veripb-formula/tests/unchecked_arithmetic.rs` and the instance pairs
`tests/instances/incorrect/version3/substitute_degree_underflow*` plus the positive
`tests/instances/correct/version3/substitute_degree_minimal_goal_stays_trivial.*` ride in the
patch.
