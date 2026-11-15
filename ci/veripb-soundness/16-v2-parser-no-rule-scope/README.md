# 16 — the version 2.0 parser enforces no rule scope (FIXED in the fork)

Six proof lines forge `s VERIFIED SATISFIABLE` for an **arbitrary unsatisfiable formula**.

|                                |                                                                       |
| ------------------------------ | --------------------------------------------------------------------- |
| formula                        | `unsat.opb` — four clauses over `x1..x3` with **zero** models         |
| proof                          | `v2.pbp` — six lines of proof format **version 2.0**                  |
| **unfixed verdict**            | `s VERIFIED SATISFIABLE`, exit 0, with default flags                   |
| **truth**                      | **UNSATISFIABLE** — 0 of 8 assignments satisfy it (exhaustive)        |
| present in stock upstream `4bb10c2c` | yes                                                                   |
| present with `0001` only       | **yes**                                                               |
| present with the pinned patch | no — rejected, no `s` line                                            |

## The bug

The version 3.0 parser has always checked where a rule may appear
(`veripb-parser/src/pbp_parser/parser.rs`):

```rust
if *scope_context > rule_scope {
    Err(self.lexer.report_error(
        format!("The rule `{}` is not allowed in a {} context", rule, scope_context.as_str()), …
    ))?;
};
```

Its sibling checked **nothing**. `grep -n scope
veripb-parser/src/pbp_parser/legacy_v2/parser.rs` returned no hits at all: the version 2.0
parser is line-oriented, dispatches on the leading token, and had no notion of the context
it was in.

`def_order`/`pre_order` **swaps the database** (`DefineOrderRule::get_new_database` returns
`Database::new()`) so the order can be defined against a clean slate. So a `sol` written
inside an unterminated `pre_order` is checked against the order's private **empty** scratch
database: `check_solution` walks a database with nothing in it, finds nothing to falsify,
and reports success. That sets `context.best_valid_objective_value`, and
`ConclusionChecker` with no solution hint treats exactly that value as its sole evidence
(`veripb-checker/src/rules/conclusion.rs`):

```rust
None => {
    if best_valid_objective_value.is_none() {
        return Err(CheckingError::SolutionMissing(…));
    }
    Ok(None)          // <- "a solution was logged, so the formula is satisfiable"
}
```

The formula is never consulted again.

## Evidence chain

```
pseudo-Boolean proof version 2.0
f 4                       % four clauses over x1..x3, zero models
output NONE
pre_order anything        % opens an order block; the database is swapped for an EMPTY one
sol x1 x2 x3              % checked against the EMPTY database — "verified"
conclusion SAT            % no hint, so the logged solution is the only evidence
end pseudo-Boolean proof
```

The `pre_order` is never closed, and nothing complained about that either.

## The pair that needs no external oracle

`unsat.pbp` is the same formula and the same binary, refuting it honestly in one `rup`
line, answering `s VERIFIED UNSATISFIABLE`, exit 0, before and after.

```bash
veripb --opb unsat.opb v2.pbp      # rejected (unfixed: s VERIFIED SATISFIABLE)
veripb --opb unsat.opb unsat.pbp   # s VERIFIED UNSATISFIABLE, before and after
```

## `variants/`

| variant | reach path / knob | unfixed | fixed |
| --- | --- | --- | --- |
| `cnf-pigeonhole/forge.pbp` | the same six lines against a DIMACS **CNF** pigeonhole instance (`--cnf`), i.e. a formula nobody would call adversarial | `VERIFIED SATISFIABLE` | rejected |
| `controls/sol_outside_pre_order.pbp` | **one knob**: the identical proof with the `pre_order` line removed, so `sol` runs at the top level against the real database | rejected | rejected |
| `version3-same-shape/v3.pbp` | **one knob**: the identical shape written in proof format **version 3.0**, where the sibling parser has always refused it | rejected | rejected |
| `version2-sol-at-top-level/sat.pbp` | **POSITIVE**: `sol` in version 2.0 at the top level, where it belongs, on a satisfiable formula | `VERIFIED SATISFIABLE` | `VERIFIED SATISFIABLE` |

`controls/` and `version3-same-shape/` together are the causation argument: the forgery is
neither "`sol` is broken" nor "`conclusion SAT` without a hint is broken" — both are refused
the moment the rule is where it belongs, and the version 3.0 parser refuses the same shape
outright. What is broken is that one of the two parsers never asked.

`version2-sol-at-top-level/` is the over-fixing guard: a placement table transcribed too
aggressively would reject ordinary version 2.0 proofs.

## The fix (now in the fork; formerly ay patch `0002`)

`Scope::allows_rule()` and `Scope::rule_not_allowed_message()`
(`veripb-parser/src/pbp_parser/utils.rs`) are now the **one** rule-placement predicate in
the crate, and **both** parsers call it. Two copies of a check are two chances to have only
one of them.

The version 2.0 parser gets its context from
`ProofProcessor::current_scope()` — the checker's own subcontext stack, which is the state
the rules are actually executed against — rather than from a second model of the nesting.
That is deliberate: a duplicate model is a thing that can drift, and this parser having *no*
model is how the defect happened. `version2_rule_scope()` transcribes the version 3.0
placement table onto the version 2.0 token set.

`red` is the one deliberate difference and it is recorded in the code: version 3.0 restricts
it to `Scope::Specification`, but version 2.0 has no `pbc` rule and spells a proof by
contradiction as a nested `red … ; ; begin … end`. Transcribing version 3.0's placement for
`red` rejects upstream's own `correct/version2/stein9.pbp` and
`correct/version2/general_watcher_bug_propagating_fully_at_level_zero.pbp`, so `red` is left
unrestricted in version 2.0.

The instance pair `tests/instances/incorrect/version2/sol_inside_pre_order.*` rides in the
patch.
