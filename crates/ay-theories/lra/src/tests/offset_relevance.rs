// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression (#smtopt-offset-churn): an offset equality whose atom
/// is already asserted true on the trail must not be re-emitted as
/// a model-equality request. The split loop recreates theory
/// instances, resetting the per-instance dedup set; without this
/// skip the same pair is re-requested every round and each request
/// converts a Sat into another NeedModelEqualities round-trip
/// (measured on QF_LIRA LCTES/smtopt: one pair re-emitted 101
/// times in 12 s; 107k decisions to `sat` without the churn, 1.4M
/// and `unknown` with it). A pair whose atom is not asserted keeps
/// the normal path (here dropped only for missing justifications,
/// which removes it from the dedup set — pre-existing semantics).
#[test]
fn offset_pair_already_asserted_true_is_not_reemitted() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Real);
    let b = terms.mk_var("b", Sort::Real);
    let c = terms.mk_var("c", Sort::Real);
    let d = terms.mk_var("d", Sort::Real);
    let ab_eq = terms.mk_eq(a, b);
    let _cd_eq = terms.mk_eq(c, d);
    let e = terms.mk_var("e", Sort::Real);
    let f = terms.mk_var("f", Sort::Real);

    let mut solver = LraSolver::new(&terms);
    solver.vars = (0..6)
        .map(|_| VarInfo {
            value: InfRational::from_rational(BigRational::zero()),
            lower: None,
            upper: None,
            status: Some(VarStatus::NonBasic),
        })
        .collect();
    for (var, term) in [(0u32, a), (1, b), (2, c), (3, d), (4, e), (5, f)] {
        solver.var_to_term.insert(var, term);
        solver.term_to_var.insert(term, var);
    }
    solver.asserted.insert(ab_eq, true);
    solver.pending_offset_equalities.push((0, 1, 0, 0));
    solver.pending_offset_equalities.push((2, 3, 0, 0));
    solver.pending_offset_equalities.push((4, 5, 0, 0));

    let requests = solver.take_pending_offset_equalities();
    assert!(
        requests.is_empty(),
        "no request may be emitted (asserted pair skipped, other pair unjustified)"
    );
    let pair_ab = if a.0 < b.0 { (a, b) } else { (b, a) };
    let pair_cd = if c.0 < d.0 { (c, d) } else { (d, c) };
    assert!(
        solver.propagated_equality_pairs.contains(&pair_ab),
        "already-asserted pair stays deduplicated within the instance"
    );
    assert!(
        !solver.propagated_equality_pairs.contains(&pair_cd),
        "unasserted-but-unjustified pair keeps the old retry semantics"
    );
    let pair_ef = if e.0 < f.0 { (e, f) } else { (f, e) };
    assert!(
        solver.propagated_equality_pairs.contains(&pair_ef),
        "plain pair with no authored equality atom is gated as consumer-less"
    );
}
