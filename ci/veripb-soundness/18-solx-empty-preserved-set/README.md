# 18 — `solx` with an empty preserved set installs the empty contradiction (FIXED in the fork)

Two proof lines forge an arbitrary optimality bound, and two more make a satisfiable
formula "equisatisfiable" to anything at all.

|                                |                                                                     |
| ------------------------------ | ------------------------------------------------------------------- |
| formula                        | `empty.opb` — `min: 1000 x1`, `preserved: ;`, the clause `x1 ∨ x2` |
| proof                          | `empty.pbp` (two rules)                                             |
| **unfixed verdict**            | `s VERIFIED BOUNDS 1000 <= obj <= 1000`, exit 0                     |
| **truth**                      | the optimum is **0** — `x1=0, x2=1` satisfies the formula           |
| present in stock upstream `4bb10c2c` | yes                                                                 |
| present with `0001` only       | **yes**                                                             |
| present with the pinned patch | no — rejected, no `s` line                                          |

## The bug

`solx` excludes a logged solution by asserting that the preserved variables are not all as
they were (`veripb-checker/src/rules/solution_logging.rs`):

```rust
let terms = if let Some(preserved_vars) = &context.preserved_variables {
    let mut terms = Vec::with_capacity(preserved_vars.len());
    for &var in preserved_vars { … terms.push(GeneralPBTerm::new(1, …)); }
    terms
} else { return Err(NoPreservedForSolutionExcluding); };
let coeff_sum = terms.len() as i64;
let constraint = constraint_from_terms_and_coeff_sum(terms, 1_i64, coeff_sum);
```

An **empty** preserved set is legal — `preserved: ;` parses to an empty set — and it takes
the `Some` branch. `terms` is empty, `coeff_sum` is 0, and the constraint built is

```
>= 1        over no literals at all
```

which is the **empty contradiction**. `SolutionChecker::add_constraints_to_core` returns
`true`, so it goes into the database *and the core*.

An empty exclusion excludes nothing: the preserved set is what "a solution" is projected
onto, and with no preserved variables every solution is the same solution. Recording that
as `>= 1` is not a weaker claim than intended, it is the strongest constraint there is.

## Evidence chain

```
* #variable= 2 #constraint= 1
min: 1000 x1 ;
preserved: ;                    % legal, and empty
1 x1 1 x2 >= 1 ;

f 1;
solx x1 x2;                     % installs the empty  >= 1  in the core
conclusion BOUNDS 1000 1000 ;   % granted: 1000 <= best logged (1000), and the DB contradicts
```

## The pair that needs no external oracle

`bounds.pbp` is the same formula and the same binary, certifying the real optimum with a
solution hint: `s VERIFIED BOUNDS 0 <= obj <= 0`, exit 0, before and after. One checker,
one formula, `1000` and `0`.

```bash
veripb --opb empty.opb empty.pbp    # rejected (unfixed: s VERIFIED BOUNDS 1000 <= obj <= 1000)
veripb --opb empty.opb bounds.pbp   # s VERIFIED BOUNDS 0 <= obj <= 0, before and after
```

## `variants/`

| variant | reach path / knob | unfixed | fixed |
| --- | --- | --- | --- |
| `equisatisfiable/equisat.pbp` | the same two lines with `output EQUISATISFIABLE FILE`: a **satisfiable** formula certified equisatisfiable to an output formula that contains the empty `>= 1` | `VERIFIED OUTPUT EQUISATISFIABLE` | rejected |
| `equisatisfiable/in-is-sat.pbp` | the link: the input really is SATISFIABLE | `VERIFIED SATISFIABLE` | `VERIFIED SATISFIABLE` |
| `equisatisfiable/out-is-unsat.pbp` | the link: the output really is UNSATISFIABLE | `VERIFIED UNSATISFIABLE` | `VERIFIED UNSATISFIABLE` |
| `controls/nonempty.pbp` | **one knob**: the identical proof against a formula whose only difference is `preserved: x1 x2 ;` instead of `preserved: ;` | rejected | rejected |
| `singleton-preserved/singleton.pbp` | **POSITIVE**: `solx` twice over a preserved set of size **one**, concluding a complete enumeration of 2 | `COMPLETE ENUMERATION OF 2 SOLUTIONS` | `COMPLETE ENUMERATION OF 2 SOLUTIONS` |

`controls/nonempty.pbp` is the causation argument: with one variable in the preserved set
the exclusion is an ordinary unit constraint, nothing contradicts, and the **unfixed**
checker refuses the identical proof. So the forgery is the empty set, not `solx` and not
`conclusion BOUNDS`.

`singleton-preserved/` is the over-fixing guard: "reject `solx` unless the preserved set is
large" is not the fix, and the boundary between "excludes nothing" and "excludes something"
is exactly at zero.

## The fix (now in the fork; formerly ay patch `0002`)

The `Excluding` branch refuses an empty preserved set outright
(`CheckingError::SolutionExcludingEmptyPreservedSet`). There is no exclusion to record, so
the alternative — make it a no-op that adds nothing — would silently let the proof's
`num_excluded_solutions` counter and its exclusion list disagree; failing closed is the only
answer that keeps the count meaning what it says.

The check is in `SolutionChecker::compute`, so it covers every route to an empty preserved
set (`preserved: ;` in the formula, `epreserved`, `preserved_rm`) rather than the one the
fixture happens to use.

The instance pair
`tests/instances/incorrect/version3/solution_excluding_empty_preserved_set.*` and the
positive `tests/instances/correct/version3/solution_excluding_singleton_preserved_set.*`
ride in the patch.
