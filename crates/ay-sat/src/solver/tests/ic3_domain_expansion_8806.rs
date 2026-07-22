// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression for #8806: multi-round BFS cone-of-influence expansion in
//! `expand_domain_bcp` must not permanently skip a long clause marked after
//! its first scan — otherwise the expanded domain is incomplete and IC3
//! domain-restricted BCP can silently skip unit-propagation opportunities,
//! producing false UNSAT during consecution queries.
//!
//! The scenario constructs long (≥3-literal) clauses arranged so that the
//! clause reachable in round N+1 is seen first — with no domain variable
//! at that point — and another clause later in the arena order introduces
//! the connecting variable. The buggy implementation (`visited_clauses`
//! marked on first scan) would permanently skip the earlier clause; the
//! fixed implementation only marks a clause absorbed once every variable
//! is in-domain, so later rounds pick up the newly-added bridge variable.

use super::*;

/// Build a minimal cone-of-influence case where the cone bridge clause
/// appears in arena order BEFORE the clause that seeds the connecting
/// variable. Verify that after `set_domain`, every transitively-connected
/// variable is in the expanded `active_domain` bitmap.
#[test]
fn expand_domain_bcp_marks_clauses_absorbed_only_when_fully_in_domain_8806() {
    let mut solver = Solver::new(0);
    // Variable layout: d0 seeds the domain. a, b, c, z are connected
    // transitively via long clauses.
    //   v0 = d0 (domain seed)
    //   v1 = a
    //   v2 = b
    //   v3 = c
    //   v4 = z
    let vars: Vec<Variable> = (0..5).map(|_| solver.new_var()).collect();
    let d0 = vars[0];
    let a = vars[1];
    let b = vars[2];
    let c = vars[3];
    let z = vars[4];

    // Arena order is insertion order. Place the "bridge" clause FIRST,
    // before any domain variable can reach it, so the buggy path marks it
    // visited without absorbing. Only later clauses introduce `a`, which
    // the bridge clause would need a second round to pick up.
    //
    // Clause #1 (long, 3+ literals, no domain var at round-0 entry):
    //     (~a | b | c)
    solver.add_clause(vec![
        Literal::negative(a),
        Literal::positive(b),
        Literal::positive(c),
    ]);

    // Clause #2 (long, seeds `a` from d0):
    //     (~d0 | a | z)
    // When this clause is scanned in round 0 phase 2, d0 IS in the domain,
    // so a and z get added. `a` must then re-drive clause #1 in round 1.
    solver.add_clause(vec![
        Literal::negative(d0),
        Literal::positive(a),
        Literal::positive(z),
    ]);

    // Restrict the decision domain to {d0}. Expansion should pull in
    // {d0, a, z} from clause #2 and then {b, c} from clause #1 during
    // round 1. The buggy `visited_clauses` implementation would permanently
    // skip clause #1 because it had no domain var in round 0.
    solver.set_domain(&[d0]);

    let active = solver
        .active_domain
        .as_ref()
        .expect("active_domain must be populated after set_domain");
    assert!(active[d0.index()], "d0 must remain in expanded domain");
    assert!(
        active[a.index()],
        "a must be added via clause (~d0 | a | z)"
    );
    assert!(
        active[z.index()],
        "z must be added via clause (~d0 | a | z)"
    );
    assert!(
        active[b.index()],
        "b must be added via clause (~a | b | c) after round 1 reabsorb (#8806)"
    );
    assert!(
        active[c.index()],
        "c must be added via clause (~a | b | c) after round 1 reabsorb (#8806)"
    );

    solver.clear_domain();
}

/// Same structure but with IC3 mode enabled, exercising
/// `set_domain_ic3_fast` which wraps `expand_domain_bcp` and caches the
/// result. Cache misses on the first call must produce the fully-expanded
/// domain; this guards against the cache replaying a truncated domain.
#[test]
fn expand_domain_bcp_ic3_mode_expanded_cache_is_complete_8806() {
    let mut solver = Solver::new(0);
    let vars: Vec<Variable> = (0..5).map(|_| solver.new_var()).collect();
    let d0 = vars[0];
    let a = vars[1];
    let b = vars[2];
    let c = vars[3];
    let z = vars[4];

    // Same clause order as the first test. IC3 mode is activated AFTER
    // variables are allocated; clauses are added after to match the
    // production pattern (PDR builds transition relation, then toggles
    // IC3 mode, then starts querying).
    solver.add_clause(vec![
        Literal::negative(a),
        Literal::positive(b),
        Literal::positive(c),
    ]);
    solver.add_clause(vec![
        Literal::negative(d0),
        Literal::positive(a),
        Literal::positive(z),
    ]);

    solver.set_ic3_mode();

    // First call: cache miss, runs expand_domain_bcp.
    solver.set_domain(&[d0]);
    {
        let active = solver
            .active_domain
            .as_ref()
            .expect("active_domain populated after set_domain");
        assert!(active[d0.index()]);
        assert!(active[a.index()]);
        assert!(active[z.index()]);
        assert!(
            active[b.index()] && active[c.index()],
            "IC3-mode cache miss must store the fully-expanded domain (#8806)"
        );
    }
    solver.clear_domain();

    // Second call with the same seed: cache hit. The cached bitmap must
    // also be complete (otherwise every subsequent query replays the bug).
    solver.set_domain(&[d0]);
    {
        let active = solver
            .active_domain
            .as_ref()
            .expect("active_domain populated on cache hit");
        assert!(active[b.index()] && active[c.index()]);
    }
    solver.clear_domain();
}

/// Stress: long chain of long clauses exercised back-to-front in arena
/// order so every round must re-examine clauses that were empty-of-domain
/// on the prior pass. The bug scales with chain length; the fix must close
/// the full chain.
#[test]
fn expand_domain_bcp_long_chain_reverse_order_8806() {
    let mut solver = Solver::new(0);

    // Layout: v0 seeds the domain; the chain is built through long
    // "bridge" clauses keyed on bridge variables v1..v10. Each bridge
    // variable needs a separate distinct filler to keep the clause
    // length ≥ 3 (binary clauses live in watch lists, not the arena, so
    // they bypass the `absorbed_clauses` path being tested).
    //
    //   v0:           domain seed
    //   v1..v10:      chain bridge variables, pulled in via long clauses
    //   v11..v20:     unique filler literals (one per chain clause)
    //
    // Total: 21 variables.
    let vars: Vec<Variable> = (0..21).map(|_| solver.new_var()).collect();

    // Insert bridge clauses in REVERSE arena order so round N+1 must
    // re-examine clauses that round N saw with no domain variable.
    //   clause_k : (~v_k | v_{k+1} | filler_k)   for k = 10, 9, ..., 1
    // filler_k = v_{10 + k} is a fresh variable never referenced elsewhere,
    // so it cannot collapse the clause or create tautologies.
    for k in (1..=10).rev() {
        let filler = vars[10 + k];
        solver.add_clause(vec![
            Literal::negative(vars[k]),
            Literal::positive(vars[k + 1]),
            Literal::positive(filler),
        ]);
    }
    // Seed clause, inserted LAST: (~v0 | v1 | filler0). filler0 = v11 is
    // shared with the k=1 bridge's filler? No — k=1 uses v_{10+1}=v11.
    // Pick v20 as the seed filler (used by k=10 as v_{10+10}=v20? yes),
    // so allocate one extra variable instead: v21 as the dedicated seed
    // filler to avoid any overlap with chain clauses.
    let seed_filler = solver.new_var();
    solver.add_clause(vec![
        Literal::negative(vars[0]),
        Literal::positive(vars[1]),
        Literal::positive(seed_filler),
    ]);

    solver.set_domain(&[vars[0]]);

    let active = solver
        .active_domain
        .as_ref()
        .expect("active_domain populated");
    for i in 0..=10 {
        assert!(
            active[vars[i].index()],
            "chain variable v{i} must be pulled into expanded domain via reverse-order chain (#8806)"
        );
    }
    // Fillers must also be pulled in (every clause that touches the
    // domain contributes all its variables).
    for k in 1..=10 {
        assert!(
            active[vars[10 + k].index()],
            "filler for chain clause k={k} must be pulled in (#8806)"
        );
    }
    assert!(
        active[seed_filler.index()],
        "seed clause filler must be pulled in (#8806)"
    );

    solver.clear_domain();
}
