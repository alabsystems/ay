// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn encode_decision_polarity() {
    assert_eq!(BcpKernelProvider::encode_literal(1, false), 2); // +1
    assert_eq!(BcpKernelProvider::encode_literal(3, true), 7); // -3
}

/// End-to-end host check: build the kernel from a real Solver's original
/// ledger, decide a literal, run native BCP, and shadow-compare. On a fresh
/// formula (no learned clauses yet) the kernel must agree exactly.
#[test]
fn shadow_host_matches_native_on_implication_chain() {
    // Clauses (DIMACS): (-1 2) (-2 3) (-3 4). Deciding +1 forces 2,3,4.
    let mut solver = Solver::new(4);
    let v = |i: u32| Variable::new(i);
    assert!(solver.add_clause(vec![Literal::negative(v(0)), Literal::positive(v(1))]));
    assert!(solver.add_clause(vec![Literal::negative(v(1)), Literal::positive(v(2))]));
    assert!(solver.add_clause(vec![Literal::negative(v(2)), Literal::positive(v(3))]));
    solver.initialize_watches(); // attach 2WL watch lists before propagation

    solver.decide(Literal::positive(v(0))); // decision: var1 = true
    let mut host = ExternalCodegenBcpShadowHost::build(&solver);
    let pre = ExternalCodegenBcpShadowHost::capture_pre_state(&solver);
    let native_conflict = solver.search_propagate();

    let outcome = host.shadow_compare(&solver, &pre, native_conflict);
    assert_eq!(
        outcome,
        ShadowCompareOutcome::Match,
        "kernel must match native BCP on a fresh implication chain \
         (matches={}, divergences={}, skipped={})",
        host.matches,
        host.divergences,
        host.skipped
    );
    assert_eq!(host.divergences, 0);
    assert_eq!(host.total_compared(), 1);
}

/// Conflict verdicts must agree: deciding +1 with (-1 2)(-1 -2) conflicts.
#[test]
fn shadow_host_agrees_on_conflict() {
    let mut solver = Solver::new(2);
    let v = |i: u32| Variable::new(i);
    assert!(solver.add_clause(vec![Literal::negative(v(0)), Literal::positive(v(1))]));
    assert!(solver.add_clause(vec![Literal::negative(v(0)), Literal::negative(v(1))]));
    solver.initialize_watches();

    solver.decide(Literal::positive(v(0)));
    let mut host = ExternalCodegenBcpShadowHost::build(&solver);
    let pre = ExternalCodegenBcpShadowHost::capture_pre_state(&solver);
    let native_conflict = solver.search_propagate();

    let outcome = host.shadow_compare(&solver, &pre, native_conflict);
    assert_eq!(outcome, ShadowCompareOutcome::Match);
    assert_eq!(host.divergences, 0);
}

/// Phase 2: differential-evidence corpus. Over many fresh random CNFs, the
/// shadow host must NEVER diverge from ay-sat native BCP (issue #678
/// `ay_sat_bcp_differential` vs `dense_reference_bcp`).
#[test]
fn shadow_host_zero_divergence_over_random_corpus() {
    // Deterministic xorshift64 PRNG — no external rng dependency.
    let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut rng = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };

    let mut total_matches = 0u64;
    let mut total_div = 0u64;
    let mut total_compares = 0u64;

    for _ in 0..400 {
        let num_vars = 3 + (rng() % 6) as usize; // 3..=8
        let num_clauses = 2 + (rng() % 6) as usize; // 2..=7
        let mut solver = Solver::new(num_vars);
        for _ in 0..num_clauses {
            let size = 2 + (rng() % 2) as usize; // 2 or 3 (no units)
            let mut vars_used: Vec<u32> = Vec::new();
            let mut lits: Vec<Literal> = Vec::new();
            while lits.len() < size {
                let var = (rng() % num_vars as u64) as u32;
                if vars_used.contains(&var) {
                    continue; // distinct vars => no tautology / dup literal
                }
                vars_used.push(var);
                let v = Variable::new(var);
                lits.push(if rng() & 1 == 0 {
                    Literal::positive(v)
                } else {
                    Literal::negative(v)
                });
            }
            solver.add_clause(lits);
        }
        solver.initialize_watches();
        // size>=2 clauses never unit-propagate at add time, so the trail is
        // empty and `decide` is legal. Skip the trial defensively otherwise.
        if solver.qhead != solver.trail.len() {
            continue;
        }
        let dvar = (rng() % num_vars as u64) as u32;
        if solver.var_is_assigned(dvar as usize) {
            continue;
        }
        let v = Variable::new(dvar);
        let dlit = if rng() & 1 == 0 {
            Literal::positive(v)
        } else {
            Literal::negative(v)
        };
        solver.decide(dlit);

        let mut host = ExternalCodegenBcpShadowHost::build(&solver);
        let pre = ExternalCodegenBcpShadowHost::capture_pre_state(&solver);
        let conflict = solver.search_propagate();
        let outcome = host.shadow_compare(&solver, &pre, conflict);
        assert_ne!(
            outcome,
            ShadowCompareOutcome::Divergence,
            "kernel diverged from native BCP on fresh CNF \
             (num_vars={num_vars}, clauses={num_clauses})"
        );
        total_matches += host.matches;
        total_div += host.divergences;
        total_compares += host.total_compared();
    }

    assert_eq!(total_div, 0, "expected zero divergence across the corpus");
    assert!(
        total_matches >= 64,
        "corpus should yield >= 64 matched compares, got {total_matches} \
         (compares={total_compares})"
    );
}

/// Phase 3 + 4: the install gate is fail-closed and activation is held shut
/// pre-product-gate even when the kernel is shadow-trustworthy.
#[test]
fn install_gate_is_fail_closed_and_preactivation() {
    let mut solver = Solver::new(2);
    let v = |i: u32| Variable::new(i);
    solver.add_clause(vec![Literal::positive(v(0)), Literal::positive(v(1))]);
    solver.initialize_watches();
    let mut host = ExternalCodegenBcpShadowHost::build(&solver);

    // No evidence => withhold (fail-closed), never active.
    assert_eq!(
        host.install_decision(),
        KernelInstallDecision::InsufficientEvidence
    );
    assert!(!host.useful_native_enabled());

    // Enough agreeing compares => Trustworthy, but STILL not active.
    host.matches = ExternalCodegenBcpShadowHost::MIN_EVIDENCE_COMPARES;
    assert_eq!(host.install_decision(), KernelInstallDecision::Trustworthy);
    assert!(
        !host.useful_native_enabled(),
        "Phase 4 product gate must stay closed (no measured end-to-end win yet)"
    );

    // Any divergence => reject (fail-closed), regardless of match count.
    host.divergences = 1;
    assert_eq!(host.install_decision(), KernelInstallDecision::Diverged);
    assert!(!host.useful_native_enabled());
    assert_eq!(host.differential_evidence().divergences, 1);
}

/// Phase 2/3: the host emits external-codegen `ay_sat_watch_bcp` contract proof-fact
/// metadata that satisfies the gate's structural check — but only when its
/// differential evidence is clean (fail-closed otherwise).
#[test]
fn emits_contract_proof_fact_metadata_only_when_trustworthy() {
    use external_codegen_codegen::ay_sat_bcp_contract::ay_sat_bcp_proof_fact_metadata_matches;

    let mut solver = Solver::new(2);
    let v = |i: u32| Variable::new(i);
    solver.add_clause(vec![Literal::positive(v(0)), Literal::positive(v(1))]);
    solver.initialize_watches();
    let mut host = ExternalCodegenBcpShadowHost::build(&solver);

    // No evidence yet => no emission (fail-closed).
    assert!(host.emit_proof_fact_metadata().is_none());

    // Trustworthy => emits metadata satisfying the external-codegen contract check.
    host.matches = ExternalCodegenBcpShadowHost::MIN_EVIDENCE_COMPARES;
    let md = host
        .emit_proof_fact_metadata()
        .expect("trustworthy host must emit proof-fact metadata");
    assert!(
        ay_sat_bcp_proof_fact_metadata_matches(&md),
        "emitted metadata must satisfy the ay_sat_watch_bcp contract"
    );
    assert_eq!(
        md.get("ay_bcp.replay_comparison.empirical_compares")
            .map(String::as_str),
        Some(
            ExternalCodegenBcpShadowHost::MIN_EVIDENCE_COMPARES
                .to_string()
                .as_str()
        )
    );

    // Any divergence => fail-closed again (no emission).
    host.divergences = 1;
    assert!(host.emit_proof_fact_metadata().is_none());
}
