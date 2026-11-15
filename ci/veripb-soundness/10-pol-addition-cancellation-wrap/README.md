# 10 — `pol` addition: the cancellation subtraction wraps (FIXED in the fork)

**Status: CLOSED.** The pinned patch (the fork's `alab-main` delta) fixes this;
stock upstream does not. This defect and the other twelve post-fork ones were
fixed here as ay patch `0002` and later reconciled into the fork, so the fix now
lives in the pinned patch itself. The headline pair is a gated row in
`expected.tsv`, so both gates (`scripts/ci/pb_certified_gate.sh` phase 4 and
`crates/ay-pb/tests/veripb_pin_gate.rs`) run it on every push and a checker that
accepts it again cannot be pinned.

|                            |                                                                      |
| -------------------------- | -------------------------------------------------------------------- |
| formula                    | `add.opb` — `1 x1 1 x2 >= 1 ;`, i.e. the clause `x1 ∨ x2`            |
| proof                      | `add.pbp` (4 rule lines)                                             |
| **unfixed verdict**        | `s VERIFIED UNSATISFIABLE`, exit 0, with default flags                |
| **truth**                  | **SATISFIABLE** — `x1 = 1, x2 = 0` satisfies the single constraint    |
| present in stock upstream `4bb10c2c` | yes                                                              |
| present with `0001` only       | **yes**                                                          |
| present with the pinned patch | no — rejected: "The constraint with ID 3 is not contradicting"    |

## The bug

Constraint addition (`+` in a `pol` line) sums the two degrees in `BigInt`,
checks that the sum fits the narrow integer type `N` of the result, and *then*
subtracts the cancellation constant produced by merging opposite literals of the
same variable **in `N`, unchecked**:

```rust
// veripb-formula/src/general_pb_constraint.rs, GeneralPBConstraint::<N>::add
let degree_sum = self.get_degree().clone().into() + summand.get_degree().clone().into();
if let (Ok(coeff_sum), Ok(degree_sum)) = (
    TryInto::<N>::try_into(coeff_sum.clone()),
    TryInto::<N>::try_into(degree_sum.clone()),      // <-- only the SUM is range-checked
) {
    let cancellation = self.merge_terms(summand);
    self.set_degree(degree_sum - &cancellation);     // <-- this may underflow N
    ...
```

`cancellation` is always ≥ 0 (it is `min(a_i, b_i)` summed over the literal pairs
`a_i·L` / `b_i·¬L` that collapse to a constant), so the subtraction can only
*underflow*. The release profile has overflow checks off, so `i64::MIN - 1`
silently becomes `i64::MAX`: a degree that should be even further below zero —
a **trivially true** row — is stored as the largest representable degree, which
makes `is_contradicting()` (`degree > coeff_sum`) true. `conclusion UNSAT` then
finds its contradiction.

This is the *same class* as defects 3 and 7a (an unchecked `-=` on a degree near
`i64::MIN` turning a trivially true row into the empty contradiction), in a rule
the first patch did not touch. Its `finish_weakening` /
`normalization_fits_in_type` guards cover `weaken`, `weaken_all` and
normalization; `add` had no equivalent until the post-fork fix (ay patch `0002`, now in the fork) added
`checked_addition_totals()` / `addition_widened_to_bigint()`.

`11-propagation-slack-overflow/` is the other defect that audit found, in the
same patch — and the more severe one, because it needs nothing from the formula
at all.

## Evidence chain

`x1 ∨ x2` is satisfiable (`x1 = 1`). The proof:

```
f 1 ;
rup 1 x1 1 x2 >= -9223372036854775808 ;   % trivially true, so RUP accepts it
pol 2 ~x1 + ;                             % (2) + the literal axiom `1 ~x1 >= 0`
conclusion UNSAT : 3 ;
```

Step 3 is arithmetic, hand-checkable in one line:

```
  1 x1 + 1 x2 >= -9223372036854775808
+ 1 ~x1       >= 0
= 1 x1 + 1 x2 + 1 ~x1 >= -9223372036854775808        (1·x1 + 1·~x1 = 1)
= 1 x2 >= -9223372036854775809                       <-- trivially true
```

`veripb -t --trace-pol` prints what it actually derived. Before the fix:

```
    1      2        1 x1 1 x2 >= -9223372036854775808
    2      ~x1      1 ~x1 >= 0
    1      +        1 x2 >= 9223372036854775807       <-- off by 2^64
  ConstraintId 3: 1 x2 >= 9223372036854775807
s VERIFIED UNSATISFIABLE
```

`1 x2 >= 9223372036854775807` has `degree > coeff_sum`, so it is the empty
contradiction as far as the checker is concerned. Every extreme number lives in
the **proof**, not the formula: the input is an ordinary two-literal clause, so
no formula-level sanity check can catch this.

After the fix the same trace shows the true degree, and the conclusion is
refused rather than the constraint being clamped:

```
    1      +        1 x2 >= -9223372036854775809
  ConstraintId 3: 1 x2 >= -9223372036854775809
Error: ... The constraint with ID 3 is not contradicting, as specified by the hint.
```

## Reproduce

```bash
cd ci/veripb-soundness/10-pol-addition-cancellation-wrap
veripb --opb add.opb add.pbp        # pinned build: exit 1, no `s` line
veripb --opb add.opb add.pbp -t --trace-pol
```

## `sat.pbp` — the same formula, the same binary, the opposite verdict

```bash
veripb --opb add.opb sat.pbp        # s VERIFIED SATISFIABLE, before AND after
```

One checker, one formula, both verdicts, so `add.pbp`'s claim is visibly false
without trusting a second tool. It is also the guard against a bogus fix: a "fix"
that refused rows with extreme degrees outright would pass the negative test and
break this one.

## `variants/` — the same defect on every constraint representation

`add`/`+` is implemented four times, once per stored constraint type, and every
narrow-width copy repeated the unchecked subtraction. None of these is a row in
`expected.tsv` — the schema is one pair per row — so they are here as the
evidence that the fix closes all of them. The pinned patch rejects every one.

| variant | code path | line of the unchecked subtraction | unfixed verdict | truth |
| --- | --- | --- | --- | --- |
| `cardinality/` | `Cardinality::add` | `cardinality.rs:402` (`degree_sum - cancel`) | `VERIFIED UNSATISFIABLE` | SATISFIABLE |
| `general-i64/` | `GeneralPBConstraint::<i64>::add` | `general_pb_constraint.rs:418` | `VERIFIED UNSATISFIABLE` | SATISFIABLE |
| `general-i128/` | `GeneralPBConstraint::<i128>::add` | `general_pb_constraint.rs:442` | `VERIFIED UNSATISFIABLE` | SATISFIABLE |
| `clause/` | `Clause::add` | `clause.rs:361` (`degree_sum - cancel`) | `VERIFIED UNSATISFIABLE` | SATISFIABLE |
| `bounds/` | as `cardinality/`, optimisation surface | — | `VERIFIED BOUNDS INF <= obj <= INF` | optimum is 0 |
| `boundary-control/` | — | — | **rejected** (unfixed too) | SATISFIABLE |

`boundary-control/` is the causation argument: `add.pbp` with the rup'd degree
raised by ONE, so the addition's true degree is exactly `i64::MIN` and nothing
wraps. It is refused by the unfixed checker as well, which pins the forgery to
the **wrap** rather than to "large numbers confuse the checker".

`general-i128/` matters on its own: it shows the bug is not "an `i64` edge case"
but a property of the *narrow-width* code, so widening `i64` to `i128` would move
the threshold rather than close the hole. `bounds/` shows the forgery is not
confined to the `UNSAT` verdict — the same wrapped row makes the checker certify
that a satisfiable optimisation problem is infeasible.

Every variant is `--opb` and takes the usual two arguments:

```bash
veripb --opb variants/general-i128/gen128.opb variants/general-i128/gen128.pbp
```

## The fix (now in the fork; formerly ay patch `0002`)

It mirrors what the first patch already does elsewhere (`finish_weakening`,
`lower_rhs`): subtract with `checked_sub` and escalate the whole constraint to
`BigInt` when it does not fit. Because `cancellation` is only known *after* the
terms have been merged, the range test cannot be moved earlier without redoing
the merge, so the merge is left where it is and the totals are recomputed
afterwards with two new helpers in `veripb-formula/src/pb_constraint.rs`:

* `checked_addition_totals()` — `(coeff_sum, degree)` in `N` with `checked_sub` /
  `checked_add`, `None` when either total leaves `N`;
* `addition_widened_to_bigint()` — the escalation for the `None` case, which
  reuses the already-merged terms, redoes the cancellation in `BigInt`, and
  narrows again with `into_smallest_type()`.

The result is that the stored degree is the **true** mathematical degree in every
case. It is not clamped: clamping would silently substitute a different
constraint for the one the proof asked for, which is a different unsoundness.
Both narrow branches of all four `add` implementations use the helpers, so the
`i128` route is closed along with the `i64` one.

## Additional recovered width and representation regressions

Three variants recovered from `a43ded6140` exercise paths distinct from the
headline fixture: `cardinality-two-rows/` adds opposite unit rows near the i64
boundary; `cardinality-i128/` adds a literal axiom through the i128 branch of
`Cardinality::add`; `general-i64-shared-literal/` retains a shared literal while
canceling its opposite pair. Each directory includes a `sat.pbp` control for
the same formula. These are additional manifestations of defect 10, so the
defect and headline-fixture counts stay unchanged.

Run the named formula against the proof with the same stem (the pinned checker
must reject it), then against `sat.pbp` (it must verify SATISFIABLE):

| directory | formula | invalid proof |
| --- | --- | --- |
| `cardinality-two-rows/` | `card.opb` | `card.pbp` |
| `cardinality-i128/` | `wide.opb` | `wide.pbp` |
| `general-i64-shared-literal/` | `gen.opb` | `gen.pbp` |
