# 12 — `proofgoal <id>` fabricates the goal inside a proof by contradiction (FIXED in the fork)

Six proof lines, **no arithmetic anywhere**, and the checker prints
`s VERIFIED UNSATISFIABLE` for an arbitrary satisfiable formula. Nothing has to be large,
nothing has to be near a type boundary, and no formula feature is required: the whole
forgery rides in the proof.

|                                |                                                                    |
| ------------------------------ | ------------------------------------------------------------------ |
| formula                        | `pbc.opb` — `1 x1 1 x2 >= 1 ;`, i.e. the clause `x1 ∨ x2`           |
| proof                          | `pbc.pbp` (5 rule lines)                                            |
| **unfixed verdict**            | `s VERIFIED UNSATISFIABLE`, exit 0, with default flags              |
| **truth**                      | **SATISFIABLE** — three of the four assignments are models          |
| present in stock upstream `4bb10c2c` | yes                                                                 |
| present with `0001` only       | **yes**                                                             |
| present with the pinned patch | no — rejected, no `s` line                                          |

## The bug

Two independent halves, either of which is enough on its own.

**`SubproofContext::pop_database_goal`** (`veripb-checker/src/subproof_context.rs`) did not
error when the named database ID had no registered proofgoal. It **fabricated** one:

```rust
} else {
    let constraint = database.get_entry_usize(index)?;
    Ok(Proofgoal::mk_single_constraint(
        Rc::new(constraint.substitute(&self.witness)),  // witness is EMPTY here
        None,
        false,
    ))
}
```

Inside a proof-by-contradiction subproof the witness is empty and no database goals are ever
registered, so **every** database ID lands in that branch and the reconstructed goal is
`C_id` itself. Opening it adds the counterexample premise `¬C_id` while `C_id` is still in
the database, so `rup >= 1 ;` is an instant, meaningless contradiction.

**`EndSubproofChecker::end_proofgoal`** (`veripb-checker/src/rules/end_subproof.rs`) then
set `contradiction_proven = true` on the **enclosing** subproof, and
`SubproofContext::finalize` short-circuits on that flag straight to `finalize_unchecked`.
The obligation a `pbc` actually owes — a contradiction from `¬C` — is never checked, and the
claimed constraint (here the empty one) enters the database.

`proof_by_contradiction_subproof` is set at three places, and all three are reachable:

| set by | spelling | forged verdict |
| --- | --- | --- |
| `rules/proof_by_contradiction.rs:45` | `pbc C : subproof` (v3) | `VERIFIED UNSATISFIABLE` for a satisfiable formula |
| `rules/red_strengthening.rs:112` | `red C ; ; begin` (v2, empty witness) | same |
| `rules/deletion.rs:242` | `delc` under `strengthening_to_core on` | **`VERIFIED SATISFIABLE` for an unsatisfiable formula** |

The third was the untested one, and it is a different forgery: it deletes a **core**
constraint with no proof, so the remaining database is satisfied by a logged solution that
falsifies the real formula.

## Evidence chain

`pbc.opb` is `x1 ∨ x2`. The proof:

```
f 1 ;
pbc >= 1 : subproof      % owes: a contradiction from ~(>= 1), i.e. from nothing useful
proofgoal 1              % fabricates the goal `C_1`; scope premise is ~C_1
rup >= 1 ;               % C_1 and ~C_1 are both in the database — instant conflict
qed;                     % <- sets contradiction_proven on the pbc subproof
qed;                     % <- finalize short-circuits, `>= 1` enters the database
conclusion UNSAT ;
```

## The pair that needs no external oracle

`sat.pbp` is the same formula and the same binary with a logged model. It answers
`s VERIFIED SATISFIABLE`, exit 0. One checker, one formula, both verdicts.

```bash
veripb --opb pbc.opb pbc.pbp   # rejected (unfixed: s VERIFIED UNSATISFIABLE)
veripb --opb pbc.opb sat.pbp   # s VERIFIED SATISFIABLE, before and after
```

## `variants/`

Not rows — `expected.tsv` carries one pair per row and `pbc` is the shortest universal form —
but they are what makes the diagnosis exact and the fix complete.

| variant | what it is | unfixed | fixed |
| --- | --- | --- | --- |
| `delc-strengthening-to-core/delc.pbp` | the CHECKED DELETION reach path, on the unsatisfiable `x1 ∧ ¬x1`: the fabricated goal discharges the deletion obligation, core constraint 2 leaves for free, and `sol x1` then satisfies what is left | `VERIFIED SATISFIABLE` | rejected |
| `delc-strengthening-to-core/unsat.pbp` | the truth, same formula and binary: one `rup >= 1 ;` | `VERIFIED UNSATISFIABLE` | `VERIFIED UNSATISFIABLE` |
| `delc-strengthening-to-core/control-no-proofgoal.pbp` | the same deletion with the `proofgoal` wrapper removed | rejected | rejected |
| `red-v2-empty-witness/redv2.pbp` | the version 2.0 spelling: `red >= 1 ; ; begin` is a proof by contradiction and an empty witness touches nothing | `VERIFIED UNSATISFIABLE` | rejected |
| `nested-in-red-proofgoal/nested.pbp` | a `pbc` nested inside a proofgoal of an ordinary `red` — a fix that only guarded the outermost subproof would miss it | `VERIFIED UNSATISFIABLE` | rejected |
| `nested-in-red-proofgoal/sat.pbp` | the model for that variant's formula | `VERIFIED SATISFIABLE` | `VERIFIED SATISFIABLE` |
| `structure-control/control.pbp` | **one knob**: `pbc.pbp` with the `proofgoal 1` / `qed;` wrapper deleted | rejected | rejected |
| `structure-control/control-internal-goal.pbp` | the internal-goal spelling `proofgoal #1`, which `pop_internal_goal` has always refused | rejected | rejected |
| `legitimate-goal1/legit.pbp` | **not a forgery**: the one shape where a goal-local contradiction really does discharge the enclosing subproof | `VERIFIED NO CONCLUSION` | `VERIFIED NO CONCLUSION` |

`structure-control/` is the causation argument: with the fabricated goal removed and nothing
else changed, the unfixed checker refuses the proof — so what forged the verdict is the
fabrication, not "`pbc` subproofs accept anything".

`legitimate-goal1/` is the over-fixing guard, and it is the reason the fix is a restriction
rather than a deletion. Version 2.0 `red` with an empty witness has goal `#1` equal to
`C|∅ = C`, so the premise its scope adds is `¬C` — the very constraint the subproof already
carries. A contradiction there really is a contradiction from `¬C`. Simply removing the
`contradiction_proven` promotion would reject this proof.

## The fix (now in the fork; formerly ay patch `0002`)

1. `pop_database_goal` refuses (`DatabaseProofgoalNotExisting`) when the subproof is a proof
   by contradiction, making it symmetric with `pop_internal_goal`, which has always errored
   on an unregistered index. Outside such a subproof the reconstruction stays: a witness only
   makes the constraints it *touches* non-trivial, so a prover is entitled to open
   `proofgoal <id>` for an untouched one, and the scope it gets carries the correct premise
   `¬(C_id|ω)`.
2. `end_proofgoal` promotes a goal-local contradiction to the enclosing subproof **only** for
   the goal recorded by `SubproofContext::premise_equivalent_goal` — the single goal whose
   counterexample premise IS the subproof's own `¬C`, which `red_strengthening` and
   `deletion` mark when they build it with an empty witness.

Regression tests ride in the patch:
`tests/instances/incorrect/version3/pbc_fabricated_database_proofgoal.*`,
`.../delc_strengthening_to_core_fabricated_database_proofgoal.*`,
`tests/instances/incorrect/version2/red_empty_witness_fabricated_database_proofgoal.*`, and
the positive `tests/instances/correct/version2/red_empty_witness_goal1_contradiction.*`.

## What was deliberately NOT changed

The reconstructed goal is built with `scope_restriction: None` while a registered database
goal carries `Some(ScopeId::LessEqual)`, so inside an explicit `scope geq` block the
reconstructed one is not refused. That is a weaker check than the registered path gets, but
it grants nothing: popping an ID that was never registered removes no obligation from
`database_proofgoals`, so no real goal can be skipped by opening it in the wrong scope. It
is recorded here rather than changed.
