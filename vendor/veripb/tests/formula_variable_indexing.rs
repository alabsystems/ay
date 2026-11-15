//! The checker must refuse a formula it cannot index, rather than read out of bounds.
//!
//! `PropagationEngine::init_trail` sizes the trail's `Assignment` from `var_names.len()`, and
//! the constraint scanners then read that assignment with `Assignment::get_lit_value_unchecked`
//! — whose safety contract is `lit.get_var() < assignment.len()`. Every formula parser is
//! therefore required to hand the checker a variable-name table that covers every literal it
//! stored. OPB and WCNF get that for free (they intern each name as they meet it, so an index
//! only exists once its table slot does); the DIMACS CNF parser did not, because it returned the
//! variable count the `p cnf` header *declares* instead of the size of the variable space the
//! file *uses*.
//!
//! That hole is closed in the parser. This is the backstop: a check at the one boundary where an
//! untrusted formula becomes a database, so that a future parser coming up short is a refusal
//! rather than undefined behaviour on the accept/reject path. It is deliberately unreachable
//! through the shipped front ends, which is exactly why it needs a test of its own.

use veripb_checker::prelude::*;
use veripb_formula::prelude::*;

/// The whole error chain as one string. `CheckingLineError`'s own `Display` is only the
/// location; the diagnosis is its `source`.
fn chain(error: &dyn std::error::Error) -> String {
    let mut out = error.to_string();
    let mut source = error.source();
    while let Some(next) = source {
        out.push_str(" | ");
        out.push_str(&next.to_string());
        source = next.source();
    }
    out
}

/// A checker context whose variable-name table covers `x0..x{n-1}` and nothing else.
fn context_with(num_variables: usize) -> Context {
    let mut var_names = VarNameManager::with_capacity(num_variables);
    for i in 0..num_variables {
        var_names.add_by_name(&format!("x{i}"));
    }
    Context::new(CheckerConfig::default(), var_names, None)
}

fn formula_with_clause_on(var: VarIdx) -> Formula {
    let mut formula = Formula::default();
    formula
        .constraints
        .push(Clause::from_lits(vec![Lit::from_var(var, false)]).into());
    formula
}

#[test]
fn a_formula_whose_literal_has_no_name_table_slot_is_refused() {
    // The exact shortfall `p cnf 1 1` + `5 0` used to produce: a two-entry name table and a
    // clause on variable 5.
    let error = ForwardsChecker::new(context_with(2), formula_with_clause_on(5))
        .err()
        .expect("a formula the checker cannot index must not be accepted");
    let rendered = chain(&error);
    assert!(
        rendered.contains("variable index 5") && rendered.contains("only covers 2 variables"),
        "the refusal must name the index and the table size, got: {rendered}"
    );
}

#[test]
fn the_first_unindexable_variable_is_refused() {
    // The boundary itself, and the one case the other three miss. A table of `n` names covers
    // `x0..x{n-1}`, so `x{n}` is the *first* index with no slot — the smallest out-of-bounds
    // read `get_lit_value_unchecked` can make, one element past the end of the `Assignment`.
    //
    // Without this the comparison is unpinned: relaxing `index >= num_variables` to
    // `index > num_variables` in `check_formula_is_indexable` leaves every other test in the
    // workspace green (measured: `cargo test --workspace`, 0 failed) while re-admitting exactly
    // this formula. A one-element overrun is the shape least likely to fault and most likely to
    // read a live neighbouring allocation, i.e. to produce a plausible wrong verdict rather
    // than a crash.
    let error = ForwardsChecker::new(context_with(2), formula_with_clause_on(2))
        .err()
        .expect("a formula whose largest variable is exactly the table size must not be accepted");
    let rendered = chain(&error);
    assert!(
        rendered.contains("variable index 2") && rendered.contains("only covers 2 variables"),
        "the refusal must name the index and the table size, got: {rendered}"
    );
}

#[test]
fn the_last_indexable_variable_is_still_accepted() {
    // The positive control, one index below the failure: `x1` is the last slot of a two-entry
    // table, so this must build. A backstop that refuses the boundary would reject real
    // formulas.
    ForwardsChecker::new(context_with(2), formula_with_clause_on(1))
        .expect("the largest indexable variable is not out of range");
}

#[test]
fn an_objective_term_is_checked_too() {
    // The objective's literals reach the same unchecked accessors through substitution and
    // solution checking, so the backstop covers it as well — and `PBObjective` keeps its terms
    // in a `BTreeMap<VarIdx, _>`, where the largest key is the one that matters.
    let formula = Formula {
        objective: Some(PBObjective::from_terms(
            vec![GeneralPBTerm::new(1.into(), Lit::from_var(9, false))],
            0.into(),
            false,
        )),
        ..Default::default()
    };
    let error = ForwardsChecker::new(context_with(2), formula)
        .err()
        .expect("an objective the checker cannot index must not be accepted");
    assert!(
        chain(&error).contains("variable index 9"),
        "the refusal must name the objective's variable"
    );
}
