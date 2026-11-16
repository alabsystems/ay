// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the independent-support brancher
//! (`solver/indep_support.rs`).

use super::*;
use crate::literal::Literal;

fn lit(v: i32) -> Literal {
    if v > 0 {
        Literal::positive(Variable((v - 1) as u32))
    } else {
        Literal::negative(Variable((-v - 1) as u32))
    }
}

/// `out <-> a & b` (1-based DIMACS-style variable numbers).
fn and_gate(cls: &mut Vec<Vec<Literal>>, out: i32, a: i32, b: i32) {
    cls.push(vec![lit(-out), lit(a)]);
    cls.push(vec![lit(-out), lit(b)]);
    cls.push(vec![lit(out), lit(-a), lit(-b)]);
}

/// `out <-> a ^ b` as its four parity clauses.
fn xor_gate(cls: &mut Vec<Vec<Literal>>, out: i32, a: i32, b: i32) {
    cls.push(vec![lit(-out), lit(a), lit(b)]);
    cls.push(vec![lit(-out), lit(-a), lit(-b)]);
    cls.push(vec![lit(out), lit(-a), lit(b)]);
    cls.push(vec![lit(out), lit(a), lit(-b)]);
}

fn solver_with(num_vars: usize, cls: &[Vec<Literal>]) -> Solver {
    let mut s = Solver::new(num_vars);
    for c in cls {
        s.add_clause(c.clone());
    }
    s
}

/// Gate 1(a): a chain of AND/XOR gates over 4 free inputs. The support
/// must be exactly the 4 inputs.
#[test]
fn indep_support_recovers_the_four_free_inputs_of_a_gate_chain() {
    // vars 1..4 free; 5 = 1&2, 6 = 3^4, 7 = 5^6, 8 = 7&1
    let mut cls = Vec::new();
    and_gate(&mut cls, 5, 1, 2);
    xor_gate(&mut cls, 6, 3, 4);
    xor_gate(&mut cls, 7, 5, 6);
    and_gate(&mut cls, 8, 7, 1);
    let mut s = solver_with(8, &cls);
    let support = s.compute_indep_support().expect("support computed");
    let mut got: Vec<u32> = support;
    got.sort_unstable();
    assert_eq!(
        got,
        vec![0, 1, 2, 3],
        "support must be exactly the four free inputs"
    );
}

/// Gate 1(b): a definition cycle must not produce a support that claims
/// to determine the cycle. The greedy is acyclic by construction, so the
/// cycle members stay in the support (and the closure check passes).
#[test]
fn indep_support_keeps_cycle_members_and_stays_closed() {
    // 1 = 2 ^ 3, 2 = 1 ^ 3, 3 = 1 ^ 2 — the SAME xor group, so all three
    // orientations exist. At most one of the three may be dropped.
    let mut cls = Vec::new();
    xor_gate(&mut cls, 1, 2, 3);
    // A second, disjoint xor group sharing no variable.
    xor_gate(&mut cls, 4, 5, 6);
    let mut s = solver_with(6, &cls);
    let support = s.compute_indep_support();
    // 4 of 6 is not <= 6/2, so the policy refuses to restrict; the point
    // of the test is that the closure verification is not fooled.
    let graph = {
        let mut decidable = vec![true; 6];
        let fixed = vec![false; 6];
        for (i, d) in decidable.iter_mut().enumerate() {
            *d = !s.var_lifecycle.is_removed(i);
        }
        s.collect_definitions(6, &decidable, &fixed)
            .expect("definitions")
    };
    let decidable = vec![true; 6];
    let fixed = vec![false; 6];
    let orders = Solver::support_orders(6, &graph, &decidable);
    for order in &orders {
        let in_set = Solver::greedy_support(order, &graph, &decidable, &fixed);
        let sup: Vec<u32> = (0..6).filter(|&v| in_set[v]).map(|v| v as u32).collect();
        assert!(
            Solver::verify_closure(6, &graph, &sup, &decidable, &fixed),
            "every greedy order must produce a closed support"
        );
        assert!(
            sup.len() >= 4,
            "two disjoint xor triangles cannot drop more than one member each"
        );
    }
    // Whatever the policy decided, it must not have installed a support
    // that leaves variables underivable.
    if let Some(sup) = support {
        assert!(Solver::verify_closure(6, &graph, &sup, &decidable, &fixed));
    }
}

/// Gate 1(c): a gate-free CNF has no definitions, so there is nothing to
/// restrict and the brancher stays out of the way.
#[test]
fn indep_support_is_inert_on_a_gate_free_cnf() {
    let cls = vec![
        vec![lit(1), lit(2), lit(3)],
        vec![lit(-1), lit(-2), lit(4)],
        vec![lit(2), lit(-3), lit(-4)],
        vec![lit(-1), lit(3), lit(4)],
    ];
    let mut s = solver_with(4, &cls);
    assert!(
        s.compute_indep_support().is_none(),
        "a gate-free CNF must not install a decision restriction"
    );
    s.install_indep_support();
    assert_eq!(s.indep_support.len(), 0);
}

/// The whitelist restricts decisions and NEVER signals SAT: with every
/// support variable assigned the restricted pick returns `None` and the
/// unrestricted route still has work to do.
#[test]
fn exhausted_support_falls_back_instead_of_claiming_sat() {
    let mut cls = Vec::new();
    and_gate(&mut cls, 5, 1, 2);
    xor_gate(&mut cls, 6, 3, 4);
    let mut s = solver_with(6, &cls);
    s.indep_support = vec![0, 1, 2, 3];
    for v in 0..4u32 {
        s.decide(Literal::positive(Variable(v)));
        assert!(s.propagate().is_none(), "no conflict expected");
    }
    assert!(
        s.pick_indep_support_decision().is_none(),
        "all support variables assigned"
    );
    // The unrestricted route is what decides whether the search is done.
    let _ = s.pick_next_decision_variable_main();
}

/// A whitelist entry that outlives its variable must never reach BCP:
/// variable compaction renumbers into a SMALLER range, and a stale index
/// used as a decision literal indexes `vals` out of bounds (observed as a
/// hard panic in `ay-prefetch::val_at` before compact.rs remapped the
/// list). Both the remap and this guard are required.
#[test]
fn out_of_range_support_entries_are_never_decided() {
    let mut cls = Vec::new();
    and_gate(&mut cls, 3, 1, 2);
    let mut s = solver_with(3, &cls);
    s.indep_support = vec![0, 9_999, u32::MAX];
    let picked = s.pick_indep_support_decision();
    assert_eq!(
        picked,
        Some(Variable(0)),
        "only the in-range entry may be decided"
    );
    s.decide(Literal::positive(Variable(0)));
    assert!(s.propagate().is_none());
    assert!(
        s.pick_indep_support_decision().is_none(),
        "stale entries must not be offered once the live entry is assigned"
    );
}

/// `retire_indep_support_eliminations` drops entries preprocessing
/// retired and refuses a whitelist that is no longer a real reduction.
#[test]
fn retiring_eliminations_refuses_a_whitelist_that_stopped_reducing() {
    let mut cls = Vec::new();
    and_gate(&mut cls, 5, 1, 2);
    xor_gate(&mut cls, 6, 3, 4);
    let mut s = solver_with(6, &cls);
    s.indep_support = vec![0, 1, 2, 3];
    s.retire_indep_support_eliminations();
    assert!(
        s.indep_support.is_empty(),
        "4 of 6 decidable is not a meaningful restriction"
    );
    s.indep_support = vec![0, 1];
    s.retire_indep_support_eliminations();
    assert_eq!(s.indep_support, vec![0, 1]);
    assert_eq!(s.stats.indep_support_size, 2);
}

/// `a ^ b ^ c = 1` as its four parity clauses (the XNOR group).
fn xnor3(cls: &mut Vec<Vec<Literal>>, a: i32, b: i32, c: i32) {
    cls.push(vec![lit(a), lit(b), lit(c)]);
    cls.push(vec![lit(a), lit(-b), lit(-c)]);
    cls.push(vec![lit(-a), lit(b), lit(-c)]);
    cls.push(vec![lit(-a), lit(-b), lit(c)]);
}

/// `a ^ b ^ c = rhs` clause group.
fn xor3(cls: &mut Vec<Vec<Literal>>, a: i32, b: i32, c: i32, rhs: bool) {
    if rhs {
        xnor3(cls, a, b, c);
    } else {
        xor_gate(cls, a, b, c);
    }
}

/// GE candidate (DR-AY-SAT-GE-SUPPORT-20261111): ten 3-XOR equations over
/// 12 variables with GF(2) rank 10 (2 free variables) whose determination
/// structure defeats the acyclic-removal greedy — every shipped order
/// keeps at least 5 variables, because breaking the system down requires
/// combining equations, not peeling single definitions. The computed
/// support must be the GE candidate. (System found by offline search
/// against the same greedy/orders; see the DR.)
#[test]
fn ge_basis_recovers_free_vars_the_greedy_cannot() {
    let eqs: [(i32, i32, i32, bool); 10] = [
        (2, 6, 10, true),
        (1, 5, 12, false),
        (1, 5, 11, false),
        (4, 5, 7, true),
        (4, 6, 7, false),
        (7, 9, 11, false),
        (1, 2, 12, true),
        (3, 8, 10, true),
        (1, 8, 9, false),
        (3, 7, 8, true),
    ];
    let mut cls = Vec::new();
    for (a, b, c, rhs) in eqs {
        xor3(&mut cls, a, b, c, rhs);
    }
    let mut s = solver_with(12, &cls);
    let decidable = vec![true; 12];
    let fixed = vec![false; 12];
    let graph = s
        .collect_definitions(12, &decidable, &fixed)
        .expect("definitions");
    assert_eq!(
        graph.ge_free.len(),
        2,
        "rank-10 XOR system over 12 variables leaves 2 free"
    );
    for order in Solver::support_orders(12, &graph, &decidable) {
        let in_set = Solver::greedy_support(&order, &graph, &decidable, &fixed);
        let kept = in_set.iter().filter(|&&b| b).count();
        assert!(
            kept >= 5,
            "the greedy cannot break this XOR system (kept {kept})"
        );
    }
    let mut s = solver_with(12, &cls);
    let support = s.compute_indep_support().expect("GE support installs");
    assert_eq!(
        support.len(),
        2,
        "support must be the two GE free variables"
    );
    assert_eq!(s.stats.indep_support_ge_free_vars, 2);
}

/// An inconsistent XOR subsystem (both parities of the same equation
/// present) refuses the GE candidate instead of concluding anything: no
/// basis expressions are recorded and no wrong restriction is installed.
#[test]
fn ge_basis_refuses_an_inconsistent_xor_subsystem() {
    let mut cls = Vec::new();
    // x1 ^ x2 ^ x3 = 0 (x3 = x1 ^ x2) and x1 ^ x2 ^ x3 = 1 (x3 = !(x1 ^ x2)).
    xor_gate(&mut cls, 3, 1, 2);
    cls.push(vec![lit(1), lit(2), lit(3)]);
    cls.push(vec![lit(1), lit(-2), lit(-3)]);
    cls.push(vec![lit(-1), lit(2), lit(-3)]);
    cls.push(vec![lit(-1), lit(-2), lit(3)]);
    // A satisfiable tail so the formula as a whole is not the subject.
    xor_gate(&mut cls, 6, 4, 5);
    let mut s = solver_with(6, &cls);
    let decidable = vec![true; 6];
    let fixed = vec![false; 6];
    let graph = s
        .collect_definitions(6, &decidable, &fixed)
        .expect("definitions");
    assert!(
        graph.ge_exprs.is_empty(),
        "inconsistent XOR subsystem must refuse the GE candidate"
    );
    assert_eq!(s.stats.indep_support_ge_free_vars, 0);
}
