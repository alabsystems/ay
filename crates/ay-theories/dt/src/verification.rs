// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani verification proofs for the DT theory solver.

use super::*;

/// Kani proof: completeness - DT solver returns definite answer for decidable fragment.
///
/// For the MVP, we verify that check() always returns Sat or Unsat (not Unknown)
/// when the input is within the decidable fragment (non-recursive datatypes).
#[kani::proof]
#[kani::unwind(4)]
fn proof_completeness_decidable_fragment() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);

    // Register a simple 2-constructor datatype
    solver.register_datatype("Bool2", &["True2".to_string(), "False2".to_string()]);

    // Create bounded number of constructor terms
    let t1 = TermId::new(kani::any());
    let t2 = TermId::new(kani::any());

    // Register 0-2 constructors
    if kani::any() {
        solver.register_constructor(
            t1,
            "Bool2",
            if kani::any() { "True2" } else { "False2" },
            &[],
        );
    }
    if kani::any() {
        solver.register_constructor(
            t2,
            "Bool2",
            if kani::any() { "True2" } else { "False2" },
            &[],
        );
    }

    // Optionally assert equality
    if kani::any() {
        solver.assert_equality(t1, t2);
    }

    // check() must return Sat or Unsat, never Unknown
    let result = solver.check();
    kani::assert(
        matches!(result, TheoryResult::Sat | TheoryResult::Unsat(_)),
        "DT solver must return definite answer for decidable fragment",
    );
}

/// Kani proof: algebraic closure - Union-find invariants preserved.
///
/// Verifies that after any sequence of operations, the union-find structure
/// maintains valid representatives (find is idempotent).
#[kani::proof]
#[kani::unwind(4)]
fn proof_union_find_invariant() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);

    // Create bounded terms
    let t1 = TermId::new(1);
    let t2 = TermId::new(2);
    let t3 = TermId::new(3);

    // Initialize terms in union-find
    solver.parent.insert(t1, t1);
    solver.parent.insert(t2, t2);
    solver.parent.insert(t3, t3);

    // Perform some unions
    if kani::any() {
        solver.union(t1, t2);
    }
    if kani::any() {
        solver.union(t2, t3);
    }

    // Verify find is idempotent: find(find(x)) == find(x)
    let r1 = solver.find(t1);
    let r1_again = solver.find(r1);
    kani::assert(r1 == r1_again, "find must be idempotent");
}

/// Kani proof: push/pop preserves scope depth correctly.
#[kani::proof]
#[kani::unwind(4)]
fn proof_push_pop_scope_depth() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);

    let initial_depth = solver.scopes.len();

    // Push some scopes
    solver.push();
    kani::assert(
        solver.scopes.len() == initial_depth + 1,
        "push must increment scope depth",
    );

    solver.push();
    kani::assert(
        solver.scopes.len() == initial_depth + 2,
        "second push must increment scope depth",
    );

    // Pop
    solver.pop();
    kani::assert(
        solver.scopes.len() == initial_depth + 1,
        "pop must decrement scope depth",
    );

    solver.pop();
    kani::assert(
        solver.scopes.len() == initial_depth,
        "second pop must restore original depth",
    );
}

/// Kani proof: pop on empty scope is safe (no panic).
#[kani::proof]
#[kani::unwind(2)]
fn proof_pop_empty_is_safe() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);

    // Pop on empty should be no-op
    solver.pop();
    kani::assert(
        solver.scopes.is_empty(),
        "pop on empty preserves empty state",
    );
}

/// Kani proof: reset clears all mutable state.
#[kani::proof]
#[kani::unwind(4)]
fn proof_reset_clears_state() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);

    // Add some state
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);
    let t1 = TermId::new(1);
    solver.register_constructor(t1, "Option", "None", &[]);
    solver.push();

    // Reset
    solver.reset();

    // Verify mutable state is cleared
    kani::assert(
        solver.term_constructors.is_empty(),
        "reset clears term_constructors",
    );
    kani::assert(solver.parent.is_empty(), "reset clears parent");
    kani::assert(solver.pending.is_empty(), "reset clears pending");
    kani::assert(solver.scopes.is_empty(), "reset clears scopes");
    // Note: datatype_defs is preserved
    kani::assert(
        solver.datatype_defs.contains_key("Option"),
        "reset preserves datatype_defs",
    );
}

/// Kani proof: union transitivity - if a == b and b == c, then a == c.
#[kani::proof]
#[kani::unwind(4)]
fn proof_union_transitivity() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);

    let t1 = TermId::new(1);
    let t2 = TermId::new(2);
    let t3 = TermId::new(3);

    // Initialize
    solver.parent.insert(t1, t1);
    solver.parent.insert(t2, t2);
    solver.parent.insert(t3, t3);

    // Union t1 and t2
    solver.union(t1, t2);
    // Union t2 and t3
    solver.union(t2, t3);

    // Now t1, t2, t3 should all have the same representative
    let r1 = solver.find(t1);
    let r2 = solver.find(t2);
    let r3 = solver.find(t3);

    kani::assert(r1 == r2, "t1 and t2 must be in same class after union");
    kani::assert(r2 == r3, "t2 and t3 must be in same class after union");
    kani::assert(r1 == r3, "transitivity: t1 and t3 must be in same class");
}

/// Kani proof: find always returns a term that is its own representative.
#[kani::proof]
#[kani::unwind(4)]
fn proof_find_returns_root() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);

    let t1 = TermId::new(1);
    let t2 = TermId::new(2);

    solver.parent.insert(t1, t1);
    solver.parent.insert(t2, t2);

    // Optionally union
    if kani::any() {
        solver.union(t1, t2);
    }

    // find returns a root (self-parent)
    let r1 = solver.find(t1);
    let r1_parent = *solver.parent.get(&r1).unwrap_or(&r1);
    kani::assert(r1 == r1_parent, "find must return a root (self-parent)");
}

/// Kani proof: constructor registration is idempotent for the same term.
#[kani::proof]
#[kani::unwind(4)]
fn proof_register_constructor_idempotent() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);

    solver.register_datatype("Bool2", &["True2".to_string(), "False2".to_string()]);

    let t1 = TermId::new(1);
    solver.register_constructor(t1, "Bool2", "True2", &[]);

    let count_after_first = solver.term_constructors.len();

    // Register same term again (overwrites)
    solver.register_constructor(t1, "Bool2", "True2", &[]);

    let count_after_second = solver.term_constructors.len();

    kani::assert(
        count_after_first == count_after_second,
        "re-registering same term doesn't increase count",
    );
}

/// Kani proof: push/pop restores constructor registration state.
#[kani::proof]
#[kani::unwind(4)]
fn proof_push_pop_constructor_state() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);

    solver.register_datatype("Bool2", &["True2".to_string(), "False2".to_string()]);

    // Register in base scope
    let t1 = TermId::new(1);
    solver.register_constructor(t1, "Bool2", "True2", &[]);
    let base_count = solver.term_constructors.len();

    solver.push();

    // Register in new scope
    let t2 = TermId::new(2);
    solver.register_constructor(t2, "Bool2", "False2", &[]);
    kani::assert(
        solver.term_constructors.len() == base_count + 1,
        "registration increases count in new scope",
    );

    solver.pop();

    // Only base registration should remain
    kani::assert(
        solver.term_constructors.len() == base_count,
        "pop restores constructor count",
    );
    kani::assert(
        solver.term_constructors.contains_key(&t1),
        "base registration preserved after pop",
    );
}

/// Kani proof: clash detection soundness - different constructors in same class => conflict.
///
/// When two terms with different constructors from the same datatype are in the
/// same equivalence class, check_clash() must detect the conflict.
#[kani::proof]
#[kani::unwind(4)]
fn proof_clash_detection_soundness() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);

    solver.register_datatype("Bool2", &["True2".to_string(), "False2".to_string()]);

    let t1 = TermId::new(1);
    let t2 = TermId::new(2);

    // Register different constructors from the same datatype
    solver.register_constructor(t1, "Bool2", "True2", &[]);
    solver.register_constructor(t2, "Bool2", "False2", &[]);

    // Before union, no clash
    let clash_before = solver.check_clash();
    kani::assert(clash_before.is_none(), "no clash before union");

    // After union, they are in the same class => clash
    solver.assert_equality(t1, t2);
    let clash_after = solver.check_clash();
    kani::assert(
        clash_after.is_some(),
        "clash detected after union of different constructors",
    );
}
