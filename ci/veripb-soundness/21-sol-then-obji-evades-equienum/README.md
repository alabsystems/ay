# 21 — `sol` + `obji` evades the `EQUIENUMERABLE` guard that `soli` trips (FIXED in the fork)

A textbook asymmetric-sibling bug: two spellings of the same step, one guarded and one not.

|                                |                                                                       |
| ------------------------------ | --------------------------------------------------------------------- |
| formula                        | `equienum.opb` — `min: x1 + x2`, `preserved: x1 x2`, the clause `x1 ∨ x2` |
| proof                          | `equienum.pbp` (`sol`, `obji`, `output EQUIENUMERABLE IMPLICIT`)        |
| **unfixed verdict**            | `s VERIFIED OUTPUT EQUIENUMERABLE`, exit 0                             |
| **truth**                      | the input has **3** solutions over its preserved set; the core it certifies equienumerable to has **none** |
| present in stock upstream `4bb10c2c` | yes                                                                   |
| present with `0001` only       | **yes**                                                               |
| present with the pinned patch | no — rejected, no `s` line                                            |

## The bug

`OutputRule::compute` guarded `EQUIENUMERABLE` with `context.solution_logged`, and
`SolutionChecker::compute` (`veripb-checker/src/rules/solution_logging.rs`) set that flag
like this:

```rust
match self.inner.rule_output {
    SolutionRuleOutput::Improving | SolutionRuleOutput::Excluding => context.solution_logged = true,
    SolutionRuleOutput::None => {}
}
```

`soli sol : v` is `Improving` and sets it. `sol sol` is `None` and does not. But `obji v`
is a *separate rule* (`ObjectiveValueRule`) that installs the **same** objective-improving
constraint `objective ≤ v-1` and never touches the flag at all. So

```
soli x1 ~x2 : 1 ;     -> refused
sol  x1 ~x2 ;  obji 1 ;   -> accepted
```

are the same step written two ways, with opposite outcomes. The flag was a *proxy* — "a
solution was logged" — for the actual hazard, which is "a constraint that removes solutions
is part of what I am about to export". The proxy was wrong in both directions: it missed
`obji`, and it stayed set after the constraint had been deleted again.

## Evidence chain

```
* #variable= 2 #constraint= 1
min: 1 x1 1 x2 ;
preserved: x1 x2 ;
1 x1 1 x2 >= 1 ;                % three solutions over {x1,x2}: 11, 10, 01

f 1 ;
sol x1 ~x2 ;                    % logs the value-1 solution, sets NO flag
obji 1 ;                        % installs "objective <= 0", i.e. ~x1 and ~x2 — and no flag
output EQUIENUMERABLE IMPLICIT ; % the core, restriction and all, is the output
conclusion NONE ;
```

## The pair that needs no external oracle

`bounds.pbp` is the same formula and the same binary, using `soli` to install the *same*
constraint for the purpose it is sound for — `s VERIFIED BOUNDS 1 <= obj <= 1`, exit 0,
before and after. Same constraint, same checker: legitimate as an optimality argument,
illegitimate as an exported solution-count guarantee.

```bash
veripb --opb equienum.opb equienum.pbp   # rejected (unfixed: OUTPUT EQUIENUMERABLE)
veripb --opb equienum.opb bounds.pbp     # s VERIFIED BOUNDS 1 <= obj <= 1, before and after
```

The exported output has no solutions at all: `variants/file-form/in.outopb` is the input
plus `-1 x1 -1 x2 >= 0`, which forces `x1 = x2 = 0` and contradicts the clause.

## `variants/`

| variant | reach path / knob | unfixed | fixed |
| --- | --- | --- | --- |
| `file-form/in.pbp` | the same forgery with `output EQUIENUMERABLE **FILE**`, where the checker actively matches the output formula against the core (four arguments, so the gate cannot run it) | `VERIFIED OUTPUT EQUIENUMERABLE` | rejected |
| `controls/soli.pbp` | **one knob**: `sol …; obji 1;` written as the single rule `soli … ;`, which is the same step and was already refused | rejected | rejected |
| `equioptimal-with-soli/equiopt.pbp` | **POSITIVE**: VeriPB's own `optimization_output_opposing_lits_objective` proof — `soli` installs an objective-improving constraint and exports it under `EQUIOPTIMAL FILE` | `VERIFIED OUTPUT EQUIOPTIMAL FOR obj < 2` | `VERIFIED OUTPUT EQUIOPTIMAL FOR obj < 2` |

`controls/soli.pbp` is the causation argument and the whole story of the defect: the same
step, spelled as one rule instead of two, was refused by the **unfixed** checker. The
forgery is the asymmetry.

`equioptimal-with-soli/` is the over-fixing guard and it is why the fix is not "apply the
`solution_logged` test to all three guarantees". `EQUIOPTIMAL`'s verdict line is explicitly
relative to the logged value — `s VERIFIED OUTPUT EQUIOPTIMAL FOR obj < 2` — so an exported
`objective ≤ 1` is consistent with what is being claimed. Moving the existing flag to all
three arms would reject this upstream test, and a restriction that goes one step too far is
its own defect.

## The fix (now in the fork; formerly ay patch `0002`)

`context.solution_logged` is **gone**. `soli` and `obji` mark the constraint they install
`is_objective_restricting`, `solx` marks its constraint `is_solution_excluding`
(`veripb-formula/src/db_constraint.rs`), and `output` tests for the hazard:

* a **solution-excluding** constraint live at `output` time invalidates all three strong
  guarantees (fixture 20);
* an **objective-restricting** constraint live at `output` time invalidates
  `EQUIENUMERABLE` — it removes every solution that is not strictly better than the logged
  value, so the counts cannot agree — but not `EQUIOPTIMAL`, for the reason above.
  `EQUISATISFIABLE` cannot reach the case at all: it is refused when an objective is
  present, and both `soli` and `obji` require one.

The instance pair
`tests/instances/incorrect/version3/output_equienumerable_sol_then_obji.*` rides in the
patch, with upstream's `correct/version3/optimization_output_opposing_lits_objective.*` as
the positive.
