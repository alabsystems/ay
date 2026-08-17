// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Failed-literal dominator diagnostic regressions.

use super::*;

#[test]
fn test_failed_literal_dominator_forced_only_reports_missing_metadata() {
    // Variables: d=0 (decision), a=1, b=2, c=3
    let d = Literal::positive(Variable(0));
    let a = Literal::positive(Variable(1));
    let b = Literal::positive(Variable(2));
    let c = Literal::positive(Variable(3));

    let mut clauses = ClauseArena::new();
    let reason_b = ClauseRef(clauses.add(&[d.negated(), b], true) as u32);
    let reason_c = ClauseRef(clauses.add(&[b.negated(), c], true) as u32);

    let conflict_clause = vec![b.negated(), c.negated()];
    let trail = vec![d, a, b, c];
    let var_data = make_var_data(
        &[0, 1, 2, 3],
        &[1, 1, 1, 1],
        &[None, None, Some(reason_b), Some(reason_c)],
    );
    let probe_parent: Vec<Option<Literal>> = vec![None, Some(d), None, Some(b)];

    let full = failed_literal_dominator(
        &conflict_clause,
        d,
        &trail,
        &var_data,
        &probe_parent,
        &clauses,
    );
    let forced_only = failed_literal_dominator_forced_only(
        &conflict_clause,
        d,
        &trail,
        &var_data,
        &probe_parent,
        &clauses,
    );

    assert_eq!(forced_only.forced, full.forced);
    assert_eq!(forced_only.failure, full.failure);
    assert_eq!(forced_only.failure, Some(DominatorFailure::MissingMetadata));
}

/// When the parent-chain walk encounters a level-1 literal with a reason
/// but no probe_parent entry, `failed_literal_dominator` reports `MissingMetadata`.
///
/// Setup: d (decision) → a → b → c. Conflict has only one level-1 lit (¬c),
/// so UIP = c. Walk: c → b (parent). b has a reason clause but probe_parent[b]
/// is None → MissingMetadata.
#[test]
fn test_failed_literal_dominator_missing_metadata() {
    let d = Literal::positive(Variable(0)); // decision (var 0)
    let a = Literal::positive(Variable(1)); // implied (var 1)
    let b = Literal::positive(Variable(2)); // implied, parent MISSING (var 2)
    let c = Literal::positive(Variable(3)); // implied (var 3)

    // Conflict with only c at level 1 (d at level 0 to avoid UIP ambiguity
    // in dominator fold). Actually, we need single level-1 lit so UIP = c.
    // Use a conflict clause with ¬c plus a level-0 literal.
    let conflict_clause = vec![c.negated()];

    let trail = vec![d, a, b, c];

    // b has a reason (implied by d via binary clause) but probe_parent[b] = None.
    let mut clauses = ClauseArena::new();
    let reason_b = clauses.add(&[b, d.negated()], false) as u32;
    let reason_c = clauses.add(&[c, b.negated()], false) as u32;
    let var_data = make_var_data(
        &[0, 1, 2, 3],
        &[1, 1, 1, 1],
        &[
            None,
            None,
            Some(ClauseRef(reason_b)),
            Some(ClauseRef(reason_c)),
        ],
    );
    // probe_parent: d=None (decision), a=d, b=None (MISSING!), c=b
    let probe_parent: Vec<Option<Literal>> = vec![None, Some(d), None, Some(b)];

    let result = failed_literal_dominator(
        &conflict_clause,
        d,
        &trail,
        &var_data,
        &probe_parent,
        &clauses,
    );

    // UIP = c. Walk: c → parent b. b has reason but no probe_parent → MissingMetadata.
    assert_eq!(result.forced, None);
    assert_eq!(
        result.failure,
        Some(DominatorFailure::MissingMetadata),
        "Expected MissingMetadata failure when probe_parent is absent for implied literal b",
    );
}

/// When the conflict clause has no level-1 literals, `failed_literal_dominator`
/// returns `NoDominator`. This tests the `uip == None` early exit (line 678).
#[test]
fn test_failed_literal_dominator_no_level1_lits_returns_no_dominator() {
    let d = Literal::positive(Variable(0)); // decision (level 1)
    let a = Literal::positive(Variable(1)); // level 0

    // Conflict clause with only level-0 literal ¬a — no level-1 lits.
    let conflict_clause = vec![a.negated()];
    let trail = vec![d];
    let var_data = make_var_data(&[0, 0], &[1, 0], &[None, None]);
    let probe_parent: Vec<Option<Literal>> = vec![None, None];
    let clauses = ClauseArena::new();

    let result = failed_literal_dominator(
        &conflict_clause,
        d,
        &trail,
        &var_data,
        &probe_parent,
        &clauses,
    );

    assert_eq!(result.forced, None);
    assert_eq!(
        result.failure,
        Some(DominatorFailure::NoDominator),
        "Expected NoDominator when conflict has no level-1 literals",
    );
}

/// When the parent-chain walk enters a cycle (steps > trail.len()),
/// `failed_literal_dominator` returns `ParentChainCycle`. The production
/// soundness gate logs the error and returns a typed failure in all builds.
#[test]
fn test_failed_literal_dominator_parent_chain_cycle() {
    let d = Literal::positive(Variable(0)); // decision
    let a = Literal::positive(Variable(1));
    let b = Literal::positive(Variable(2));

    // Conflict with single level-1 literal ¬b, so UIP = b.
    // Then parent walk: b → a → b → a → ... (cycle).
    let conflict_clause = vec![b.negated()];
    let trail = vec![d, a, b];

    let mut clauses = ClauseArena::new();
    let reason_a = clauses.add(&[a, b.negated()], false); // a implied by b
    let reason_b = clauses.add(&[b, a.negated()], false); // b implied by a
    let var_data = make_var_data(
        &[0, 1, 2],
        &[1, 1, 1],
        &[
            None,
            Some(ClauseRef(reason_a as u32)),
            Some(ClauseRef(reason_b as u32)),
        ],
    );
    // probe_parent: d=decision, a→b, b→a (CYCLE!)
    let probe_parent: Vec<Option<Literal>> = vec![None, Some(b), Some(a)];

    let result = failed_literal_dominator(
        &conflict_clause,
        d,
        &trail,
        &var_data,
        &probe_parent,
        &clauses,
    );

    assert_eq!(result.forced, None);
    assert_eq!(
        result.failure,
        Some(DominatorFailure::ParentChainCycle),
        "Expected ParentChainCycle when parent chain a→b→a→... forms a cycle",
    );
}
