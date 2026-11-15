# 20 — `EQUISATISFIABLE` / `EQUIOPTIMAL` are not guarded against exported exclusions (FIXED in the fork)

|                                |                                                                       |
| ------------------------------ | --------------------------------------------------------------------- |
| formula                        | `equisat.opb` — `preserved: x1 x2`, the clause `x1 ∨ x2`; **3 models** |
| proof                          | `equisat.pbp` (three `solx`, `output EQUISATISFIABLE IMPLICIT`)        |
| **unfixed verdict**            | `s VERIFIED OUTPUT EQUISATISFIABLE`, exit 0                            |
| **truth**                      | the input has **3** solutions; the core it certifies equisatisfiable to has **none** |
| present in stock upstream `4bb10c2c` | yes                                                                   |
| present with `0001` only       | **yes**                                                               |
| present with the pinned patch | no — rejected, no `s` line                                            |

## The bug

`OutputRule::compute` (`veripb-checker/src/rules/output.rs`) had exactly one guard against
a proof that has *removed solutions*, and it was in the wrong arm:

```rust
// Check conditions for `EQUIENUMERABLE`.
if self.guarantee == OutputGuarantee::Equienumerable {
    if context.preserved_variables.is_none() && context.witnesses_used { … }
    if context.solution_logged {
        return Err(CheckingError::OutputEquienumSolutionLogged);
    }
}
```

`EQUISATISFIABLE` and `EQUIOPTIMAL` are not tested at all. So three `solx` lines export the
exclusions into the output formula — the output is then the input **minus** every solution
the proof excluded — and the checker certifies the two equisatisfiable. Three exclusions
over a formula with three solutions leave an output with none.

## Evidence chain

```
* #variable= 2 #constraint= 1
preserved: x1 x2 ;
1 x1 1 x2 >= 1 ;                  % three solutions: 11, 10, 01

f 1;
solx x1 x2;                       % each installs an exclusion IN THE CORE
solx x1 ~x2;
solx ~x1 x2;
output EQUISATISFIABLE IMPLICIT;  % the core, exclusions and all, is the output
conclusion NONE;
```

## The pair that needs no external oracle

The claim is about a *pair* of formulas, so the disproof is a pair of ordinary verdicts from
the same binary:

```bash
veripb --opb equisat.opb equisat.pbp                  # rejected (unfixed: OUTPUT EQUISATISFIABLE)
veripb --opb equisat.opb sat.pbp                      # s VERIFIED SATISFIABLE   (the input)
veripb --opb variants/file-form/out.opb \
            variants/file-form/out.pbp                # s VERIFIED UNSATISFIABLE (the output)
```

Both of those verify before and after the fix. A satisfiable formula is not equisatisfiable
to an unsatisfiable one.

## `variants/`

| variant | reach path / knob | unfixed | fixed |
| --- | --- | --- | --- |
| `file-form/in.pbp` | the same forgery with `output EQUISATISFIABLE **FILE**`, where the checker actively matches the output formula against the core (four arguments, so the gate cannot run it) | `VERIFIED OUTPUT EQUISATISFIABLE` | rejected |
| `file-form/out.pbp` | the link: the exported output really is UNSATISFIABLE | `VERIFIED UNSATISFIABLE` | `VERIFIED UNSATISFIABLE` |
| `equioptimal/opt.pbp` | the same defect on the **`EQUIOPTIMAL`** arm: one `solx` and an `e`, on `min: x2` with `preserved: x1` | `VERIFIED OUTPUT EQUIOPTIMAL FOR obj < 1` | rejected |
| `equioptimal/in-opt-0.pbp` | the link: the input's optimum is 0 | `VERIFIED BOUNDS 0 <= obj <= 0` | `VERIFIED BOUNDS 0 <= obj <= 0` |
| `equioptimal/out-opt-1.pbp` | the link: the output's optimum is 1 | `VERIFIED BOUNDS 1 <= obj <= 1` | `VERIFIED BOUNDS 1 <= obj <= 1` |
| `controls/equienum.pbp` | **one knob**: the identical proof asking for `EQUIENUMERABLE` instead, which was the one arm that *was* guarded | rejected | rejected |
| `redundance-export-valid/decision.pbp` | **POSITIVE**: VeriPB's own `decision_output` proof, which exports two `red`-derived constraints — also not implied by the input — under `EQUISATISFIABLE FILE` | `VERIFIED OUTPUT EQUISATISFIABLE` | `VERIFIED OUTPUT EQUISATISFIABLE` |

`controls/equienum.pbp` is the causation argument in its cleanest form: the *same proof*,
one keyword different, was refused by the unfixed checker. The three guarantees were not
treated alike, and there was no reason for it.

`redundance-export-valid/` is the over-fixing guard, and it draws the line the fix has to
respect: exporting a constraint that does not follow from the input is **normal** —
redundancy-based strengthening does it on every line — and `EQUISATISFIABLE` is exactly the
guarantee that covers it, because `red` preserves satisfiability. What `solx` does not
preserve is satisfiability. A fix phrased as "the output must be implied by the input" would
reject this proof and most of the format.

## The fix (now in the fork; formerly ay patch `0002`)

`solx` marks its constraint `is_solution_excluding`
(`veripb-formula/src/db_constraint.rs`), and all three strong guarantees —
`EQUISATISFIABLE`, `EQUIOPTIMAL`, `EQUIENUMERABLE` — refuse when
`Database::first_solution_excluding()` finds one live at `output` time.

Testing the **constraint** rather than a `solution_logged` flag fixes two things at once.
The flag was set by the `sol*` rules rather than by the hazard (see fixture 21), and it
never cleared, so a proof that deleted its exclusions before `output` was refused for
something that was no longer true.

Objective-restricting constraints (`soli`, `obji`) are handled separately and only for
`EQUIENUMERABLE`; see `21-sol-then-obji-evades-equienum/README.md` for why `EQUIOPTIMAL`
tolerates them.

The instance pairs
`tests/instances/incorrect/version3/output_equisatisfiable_solution_excluding.*` and
`.../output_equioptimal_solution_excluding.*` ride in the patch, with upstream's
`correct/version3/decision_output.*` as the positive.
