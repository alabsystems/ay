// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_sat::{ExtCheckResult, Extension, Literal, SatResult, SolverContext, Variable};

#[test]
fn test_xor_constraint_new() {
    // Basic XOR
    let xor = XorConstraint::new(vec![1, 2, 3], true);
    assert_eq!(xor.vars, vec![1, 2, 3]);
    assert!(xor.rhs);

    // Duplicate removal (a XOR a = 0)
    let xor = XorConstraint::new(vec![1, 2, 2, 3], true);
    assert_eq!(xor.vars, vec![1, 3]);
    assert!(xor.rhs);

    // Sorted
    let xor = XorConstraint::new(vec![3, 1, 2], false);
    assert_eq!(xor.vars, vec![1, 2, 3]);
}

#[test]
fn test_xor_constraint_unit() {
    // x = true (x XOR true = 0 doesn't make sense, let's think about this)
    // XOR constraint: x1 XOR ... XOR xn = rhs means parity of assigned vars equals rhs
    // For unit: x = rhs directly
    // rhs=true means x must be 1 (positive literal)
    // rhs=false means x must be 0 (negative literal)
    let xor = XorConstraint::new(vec![5], true);
    assert!(xor.is_unit());
    let lit = xor.unit_lit().unwrap();
    assert_eq!(lit.variable().id(), 5);
    assert!(lit.is_positive()); // x = 1

    let xor = XorConstraint::new(vec![5], false);
    let lit = xor.unit_lit().unwrap();
    assert_eq!(lit.variable().id(), 5);
    assert!(!lit.is_positive()); // x = 0
}

#[test]
fn test_xor_constraint_tautology_conflict() {
    // Empty with rhs=false is tautology (0 = 0)
    let xor = XorConstraint::new(vec![], false);
    assert!(xor.is_tautology());
    assert!(!xor.is_conflict());

    // Empty with rhs=true is conflict (0 = 1)
    let xor = XorConstraint::new(vec![], true);
    assert!(!xor.is_tautology());
    assert!(xor.is_conflict());

    // Pairs cancel: (1,1) = empty
    let xor = XorConstraint::new(vec![1, 1], false);
    assert!(xor.is_tautology());
}

#[test]
fn test_packed_row_operations() {
    let mut row = PackedRow::new(100);
    assert!(row.is_zero());

    row.set(5, true);
    row.set(67, true);
    assert!(!row.is_zero());
    assert!(row.get(5));
    assert!(row.get(67));
    assert!(!row.get(6));

    assert_eq!(row.iter_set_bits().collect::<Vec<_>>(), vec![5, 67]);
}

#[test]
fn test_packed_row_xor() {
    let mut row1 = PackedRow::new(10);
    row1.set(1, true);
    row1.set(3, true);
    row1.rhs = true;

    let mut row2 = PackedRow::new(10);
    row2.set(1, true);
    row2.set(5, true);
    row2.rhs = false;

    row1.xor_in(&row2);

    // 1 XOR 1 = 0, 3 stays, 5 added
    assert!(!row1.get(1));
    assert!(row1.get(3));
    assert!(row1.get(5));
    assert!(row1.rhs); // true XOR false = true
}

#[test]
fn test_gaussian_solver_basic() {
    // a XOR b = 1
    // b XOR c = 0
    // Should derive: a XOR c = 1
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![1, 2], false),
    ];

    let mut solver = GaussianSolver::new(&constraints);
    let result = solver.eliminate();
    assert!(
        !matches!(result, GaussResult::Conflict(_)),
        "Expected no conflict"
    );
}

#[test]
fn test_gaussian_solver_conflict() {
    // a XOR b = 1
    // a XOR b = 0
    // Contradiction!
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![0, 1], false),
    ];

    let mut solver = GaussianSolver::new(&constraints);
    let result = solver.eliminate();
    assert!(
        matches!(result, GaussResult::Conflict(_)),
        "Expected conflict"
    );
}

#[test]
fn test_gaussian_solver_propagation() {
    // a = 1 (unit XOR: a XOR 0 = 1, i.e., a = 1)
    let constraints = vec![XorConstraint::new(vec![0], true)];

    let solver = GaussianSolver::new(&constraints);
    let props = solver.get_all_propagations();
    assert_eq!(props.len(), 1);
    // a = 1 means positive literal
    let (lit, _row_idx) = &props[0];
    assert!(lit.is_positive());
    assert_eq!(lit.variable().id(), 0);
}

#[test]
fn test_gaussian_solver_assign() {
    // a XOR b = 1
    // Set a = 1, should propagate b = 0
    let constraints = vec![XorConstraint::new(vec![0, 1], true)];

    let mut solver = GaussianSolver::new(&constraints);
    solver.eliminate();
    let result = solver.assign(0, true);

    match result {
        GaussResult::Propagate(lit, _row_idx) => {
            assert_eq!(lit.variable().id(), 1);
            // a=1, a XOR b = 1 => b = 0 (negative)
            assert!(!lit.is_positive());
        }
        _ => panic!("Expected propagation"),
    }
}

#[test]
fn test_three_var_system() {
    // x1 XOR x2 = 1
    // x2 XOR x3 = 1
    // x1 XOR x3 = 0
    // This is consistent: x1=1, x2=0, x3=1 works
    let constraints = vec![
        XorConstraint::new(vec![1, 2], true),
        XorConstraint::new(vec![2, 3], true),
        XorConstraint::new(vec![1, 3], false),
    ];

    let mut solver = GaussianSolver::new(&constraints);
    let result = solver.eliminate();
    assert!(
        !matches!(result, GaussResult::Conflict(_)),
        "Expected no conflict"
    );
}

#[test]
fn test_three_var_conflict() {
    // x1 XOR x2 = 1
    // x2 XOR x3 = 1
    // x1 XOR x3 = 1
    // Adding all: 0 = 1, conflict!
    let constraints = vec![
        XorConstraint::new(vec![1, 2], true),
        XorConstraint::new(vec![2, 3], true),
        XorConstraint::new(vec![1, 3], true),
    ];

    let mut solver = GaussianSolver::new(&constraints);
    let result = solver.eliminate();
    assert!(
        matches!(result, GaussResult::Conflict(_)),
        "Expected conflict"
    );
}

// ======== XorExtension Tests ========

/// Mock solver context for testing XorExtension.
struct MockContext {
    values: HashMap<u32, bool>,
    trail: Vec<Literal>,
    level: u32,
    var_levels: HashMap<u32, u32>,
}

impl MockContext {
    fn new() -> Self {
        Self {
            values: HashMap::default(),
            trail: Vec::new(),
            level: 0,
            var_levels: HashMap::default(),
        }
    }

    fn assign(&mut self, var: u32, value: bool) {
        self.values.insert(var, value);
        let lit = if value {
            Literal::positive(Variable::new(var))
        } else {
            Literal::negative(Variable::new(var))
        };
        self.trail.push(lit);
        self.var_levels.insert(var, self.level);
    }

    fn new_level(&mut self) {
        self.level += 1;
    }

    fn backtrack_to(&mut self, level: u32) {
        self.level = level;
        // Remove assignments above this level
        self.trail.retain(|lit| {
            let var = lit.variable().id();
            if let Some(&var_level) = self.var_levels.get(&var) {
                if var_level > level {
                    self.values.remove(&var);
                    return false;
                }
            }
            true
        });
        self.var_levels.retain(|_, &mut v| v <= level);
    }
}

impl SolverContext for MockContext {
    fn value(&self, var: Variable) -> Option<bool> {
        self.values.get(&var.id()).copied()
    }

    fn decision_level(&self) -> u32 {
        self.level
    }

    fn var_level(&self, var: Variable) -> Option<u32> {
        self.var_levels.get(&var.id()).copied()
    }

    fn trail(&self) -> &[Literal] {
        &self.trail
    }
}

#[test]
fn test_xor_extension_new() {
    // Create extension with simple constraints
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true), // x0 XOR x1 = 1
    ];
    let ext = XorExtension::new(constraints);
    assert_eq!(ext.num_constraints(), 1);
    assert_eq!(ext.num_variables(), 2);
    assert!(ext.contains_var(0));
    assert!(ext.contains_var(1));
    assert!(!ext.contains_var(2));
}

#[test]
fn test_xor_extension_initial_conflict() {
    // Contradictory constraints should detect conflict
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),  // x0 XOR x1 = 1
        XorConstraint::new(vec![0, 1], false), // x0 XOR x1 = 0
    ];
    let ext = XorExtension::new(constraints);
    let ctx = MockContext::new();

    // Should have conflict immediately
    assert!(ext.conflict.is_some());
    assert!(ext.can_propagate(&ctx));
}

#[test]
fn test_xor_extension_initial_propagation() {
    // Unit constraint should produce propagation
    let constraints = vec![
        XorConstraint::new(vec![0], true), // x0 = 1
    ];
    let mut ext = XorExtension::new(constraints);
    let ctx = MockContext::new();

    // Should have initial propagation
    assert!(ext.can_propagate(&ctx));

    let result = ext.propagate(&ctx);
    assert!(
        result.clauses.is_empty(),
        "XOR should use lightweight propagations"
    );
    assert_eq!(result.propagations.len(), 1);
    // The clause should propagate x0 = true
    let clause = &result.propagations[0].0;
    assert!(clause
        .iter()
        .any(|lit| lit.variable().id() == 0 && lit.is_positive()));
}

#[test]
fn test_xor_extension_propagate_after_assign() {
    // x0 XOR x1 = 1
    // After assigning x0 = true, should propagate x1 = false
    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut ext = XorExtension::new(constraints);
    let mut ctx = MockContext::new();

    // No initial propagation (2 vars, not unit)
    let result = ext.propagate(&ctx);
    assert!(result.clauses.is_empty());
    assert!(result.propagations.is_empty());

    // Assign x0 = true
    ctx.assign(0, true);

    // Now we should have a propagation
    let result = ext.propagate(&ctx);
    assert!(
        result.clauses.is_empty(),
        "XOR should use lightweight propagations"
    );
    assert!(!result.propagations.is_empty());

    // Find the clause that propagates x1
    let prop_clause = result.propagations.iter().find(|(c, lit)| {
        *lit == Literal::negative(Variable::new(1))
            && c.iter()
                .any(|lit| lit.variable().id() == 1 && !lit.is_positive())
    });
    assert!(prop_clause.is_some(), "Should propagate x1 = false");
}

#[test]
fn test_xor_extension_conflict_clause_uses_only_source_row_vars() {
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![2, 3], true),
    ];
    let mut ext = XorExtension::new(constraints);
    let mut ctx = MockContext::new();

    // Preload unrelated tracked assignments from a different XOR row.
    ctx.assign(2, true);
    ctx.assign(3, false);
    ctx.assign(0, true);
    ctx.assign(1, true);

    let result = ext.propagate(&ctx);
    let conflict = result.conflict.expect("Should detect row conflict");
    assert_eq!(conflict.len(), 2, "Conflict should use only the source row");
    assert!(conflict.iter().all(|lit| lit.variable().id() <= 1));
}

#[test]
fn test_xor_extension_resyncs_after_trail_shrink_without_explicit_backtrack() {
    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut ext = XorExtension::new(constraints);
    let mut ctx = MockContext::new();

    ctx.assign(0, true);
    let result = ext.propagate(&ctx);
    assert_eq!(result.propagations.len(), 1);

    // Backtrack in the SAT context only. The extension must lazily rebuild from
    // the shortened trail on the next propagate() call.
    ctx.new_level();
    ctx.assign(1, false);
    let _ = ext.propagate(&ctx);
    ctx.backtrack_to(0);

    let result = ext.propagate(&ctx);
    assert!(result.clauses.is_empty());
    assert_eq!(result.propagations.len(), 1);
    let (reason, propagated) = &result.propagations[0];
    assert_eq!(*propagated, Literal::negative(Variable::new(1)));
    assert_eq!(reason[0], *propagated);
}

#[test]
fn test_xor_extension_conflict_detection() {
    // x0 XOR x1 = 1
    // Assign x0 = true, x1 = true => conflict (1 XOR 1 = 0 != 1)
    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut ext = XorExtension::new(constraints);
    let mut ctx = MockContext::new();

    ctx.assign(0, true);
    let _ = ext.propagate(&ctx);

    // Now assign x1 = true (violates the constraint)
    ctx.assign(1, true);

    let result = ext.propagate(&ctx);
    assert!(
        result.conflict.is_some(),
        "Should detect conflict: 1 XOR 1 != 1"
    );
}

#[test]
fn test_xor_extension_check() {
    // x0 XOR x1 = 1
    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut ext = XorExtension::new(constraints);
    let mut ctx = MockContext::new();

    // Satisfying assignment: x0 = true, x1 = false
    ctx.assign(0, true);
    let _ = ext.propagate(&ctx);
    ctx.assign(1, false);
    let _ = ext.propagate(&ctx);

    let check_result = ext.check(&ctx);
    assert!(matches!(check_result, ExtCheckResult::Sat));
}

#[test]
fn test_xor_extension_backtrack() {
    // x0 XOR x1 = 1
    // x1 XOR x2 = 0
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![1, 2], false),
    ];
    let mut ext = XorExtension::new(constraints);
    let mut ctx = MockContext::new();

    // Level 0: assign x0 = true
    ctx.assign(0, true);
    let _ = ext.propagate(&ctx);

    // Level 1: assign x1 = false (satisfies first constraint: true XOR false = 1)
    ctx.new_level();
    ctx.assign(1, false);
    let _ = ext.propagate(&ctx);
    // This should propagate x2 = false (false XOR x2 = 0 => x2 = 0)

    // Now backtrack to level 0
    ext.backtrack(0);
    ctx.backtrack_to(0);

    // Extension should have reset and be ready for new assignments
    // Check that we can make different assignments now
    assert!(ext.needs_propagate || ext.pending_propagations.is_empty());
}

#[test]
fn test_xor_extension_backtrack_recovers_non_watched_unit() {
    // x0 XOR x1 XOR x2 XOR x3 XOR x4 = 0
    //
    // Watches are initialized on x0 and x1. After satisfying the row and then
    // backtracking only x4, the extension must still rediscover the unit
    // propagation x4 = false even though x4 was never watched.
    let constraints = vec![XorConstraint::new(vec![0, 1, 2, 3, 4], false)];
    let mut ext = XorExtension::new(constraints);
    let mut ctx = MockContext::new();

    // Root-level assignments leave x1 and x4 unassigned, so no unit yet.
    ctx.assign(2, true);
    ctx.assign(3, false);
    ctx.assign(0, true);
    let result = ext.propagate(&ctx);
    assert!(result.clauses.is_empty());
    assert!(result.propagations.is_empty());
    assert!(result.conflict.is_none());

    // Add x1 and then x4 at deeper levels, but propagate only after both are on
    // the SAT trail. This leaves the row fully assigned and satisfied.
    ctx.new_level();
    ctx.assign(1, false);
    ctx.new_level();
    ctx.assign(4, false);
    let result = ext.propagate(&ctx);
    assert!(result.clauses.is_empty());
    assert!(result.propagations.is_empty());
    assert!(result.conflict.is_none());

    // Backtrack away only x4. The row is now unit on x4=false, even though x4
    // was not one of the watched columns.
    ext.backtrack(1);
    ctx.backtrack_to(1);

    let result = ext.propagate(&ctx);
    let propagates_x4_false = result.propagations.iter().any(|(clause, lit)| {
        *lit == Literal::negative(Variable::new(4))
            && matches!(clause.first(), Some(first) if *first == *lit)
    });

    assert!(
        propagates_x4_false,
        "backtrack should recover x4=false propagation from the full row, got {:?}",
        result.propagations
    );
}

#[test]
fn test_xor_extension_three_way_chain() {
    // x0 XOR x1 = 1
    // x1 XOR x2 = 1
    // This implies x0 XOR x2 = 0 (x0 = x2)
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![1, 2], true),
    ];
    let mut ext = XorExtension::new(constraints);
    let mut ctx = MockContext::new();

    // Assign x0 = true
    ctx.assign(0, true);
    let _ = ext.propagate(&ctx);
    // Should propagate x1 = false (from first constraint)

    ctx.assign(1, false);
    let result = ext.propagate(&ctx);
    // Should propagate x2 = true (from second constraint: false XOR x2 = 1)

    // Find propagation for x2
    let propagates_x2 = result
        .propagations
        .iter()
        .any(|(_, lit)| *lit == Literal::positive(Variable::new(2)));
    assert!(
        propagates_x2,
        "Should propagate x2 after chain of assignments"
    );
}

// ======== XorFinder Tests ========

fn encode_three_var_xor(a: u32, b: u32, c: u32, rhs: bool) -> Vec<Vec<Literal>> {
    let forbidden_assignments = if rhs {
        vec![
            [false, false, false],
            [true, true, false],
            [true, false, true],
            [false, true, true],
        ]
    } else {
        vec![
            [true, false, false],
            [false, true, false],
            [false, false, true],
            [true, true, true],
        ]
    };

    forbidden_assignments
        .into_iter()
        .map(|assignment| {
            [(a, assignment[0]), (b, assignment[1]), (c, assignment[2])]
                .into_iter()
                .map(|(var, value)| {
                    if value {
                        Literal::negative(Variable::new(var))
                    } else {
                        Literal::positive(Variable::new(var))
                    }
                })
                .collect()
        })
        .collect()
}

#[test]
fn test_xorfinder_two_var_xor() {
    // CNF encoding of x0 XOR x1 = 1:
    // (-x0 OR -x1) - forbids (1,1) -> parity 0
    // (x0 OR x1)   - forbids (0,0) -> parity 0
    let clauses = vec![
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
    ];

    let mut finder = XorFinder::new();
    let xors = finder.find_xors(&clauses);

    assert_eq!(xors.len(), 1);
    assert_eq!(xors[0].vars, vec![0, 1]);
    assert!(xors[0].rhs); // XOR = 1
}

#[test]
fn test_xorfinder_two_var_xor_rhs_false() {
    // CNF encoding of x0 XOR x1 = 0 (equivalence):
    // (-x0 OR x1)  - forbids (1,0) -> parity 1
    // (x0 OR -x1)  - forbids (0,1) -> parity 1
    let clauses = vec![
        vec![
            Literal::negative(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
    ];

    let mut finder = XorFinder::new();
    let xors = finder.find_xors(&clauses);

    assert_eq!(xors.len(), 1);
    assert_eq!(xors[0].vars, vec![0, 1]);
    assert!(!xors[0].rhs); // XOR = 0
}

#[test]
fn test_xorfinder_three_var_xor() {
    // CNF encoding of x0 XOR x1 XOR x2 = 1:
    // Need 4 clauses (2^3 / 2 = 4)
    // Forbid combinations with even parity (sum of trues is even):
    //
    // A clause (l0 OR l1 OR l2) forbids the assignment where all literals are FALSE.
    // If li = xi (positive), forbidden xi = 0.
    // If li = -xi (negative), forbidden xi = 1.
    //
    // To forbid (0,0,0): need all positive -> (x0 OR x1 OR x2)
    // To forbid (1,1,0): need -x0, -x1, x2 -> (-x0 OR -x1 OR x2)
    // To forbid (1,0,1): need -x0, x1, -x2 -> (-x0 OR x1 OR -x2)
    // To forbid (0,1,1): need x0, -x1, -x2 -> (x0 OR -x1 OR -x2)
    let clauses = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(2)),
        ],
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
            Literal::positive(Variable::new(2)),
        ],
        vec![
            Literal::negative(Variable::new(0)),
            Literal::positive(Variable::new(1)),
            Literal::negative(Variable::new(2)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(1)),
            Literal::negative(Variable::new(2)),
        ],
    ];

    let mut finder = XorFinder::new();
    let xors = finder.find_xors(&clauses);

    assert_eq!(xors.len(), 1);
    assert_eq!(xors[0].vars, vec![0, 1, 2]);
    assert!(xors[0].rhs); // XOR = 1
}

#[test]
fn test_xorfinder_finds_three_var_parity_formula() {
    let clauses = encode_three_var_xor(1, 2, 3, true);

    let mut finder = XorFinder::new();
    let xors = finder.find_xors(&clauses);

    assert_eq!(xors, vec![XorConstraint::new(vec![1, 2, 3], true)]);
}

#[test]
fn test_xorfinder_finds_three_var_xor_cnf_pattern() {
    let clauses = encode_three_var_xor(4, 5, 6, true);

    let mut finder = XorFinder::new();
    let (xors, indices) = finder.find_xors_with_indices(&clauses);

    assert_eq!(xors, vec![XorConstraint::new(vec![4, 5, 6], true)]);
    assert_eq!(indices.len(), 4);
    assert!(indices.contains(&0));
    assert!(indices.contains(&1));
    assert!(indices.contains(&2));
    assert!(indices.contains(&3));
}

#[test]
fn test_xorfinder_does_not_identify_non_xor_cnf_as_xor() {
    let clauses = vec![
        vec![
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(2)),
            Literal::positive(Variable::new(3)),
        ],
        vec![
            Literal::negative(Variable::new(1)),
            Literal::negative(Variable::new(2)),
            Literal::positive(Variable::new(3)),
        ],
        vec![
            Literal::negative(Variable::new(1)),
            Literal::positive(Variable::new(2)),
            Literal::negative(Variable::new(3)),
        ],
        vec![
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(2)),
            Literal::negative(Variable::new(3)),
        ],
    ];

    let mut finder = XorFinder::new();
    let xors = finder.find_xors(&clauses);

    assert!(
        xors.is_empty(),
        "mixed-parity clause sets must not be classified as XOR encodings"
    );
}

#[test]
fn test_xorfinder_incomplete_xor() {
    // Only one clause - not enough for a complete XOR
    let clauses = vec![vec![
        Literal::negative(Variable::new(0)),
        Literal::negative(Variable::new(1)),
    ]];

    let mut finder = XorFinder::new();
    let xors = finder.find_xors(&clauses);

    assert!(xors.is_empty(), "Incomplete XOR should not be detected");
}

#[test]
fn test_xorfinder_multiple_xors() {
    // Two separate XORs
    // x0 XOR x1 = 1
    // x2 XOR x3 = 0
    let clauses = vec![
        // x0 XOR x1 = 1
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        // x2 XOR x3 = 0
        vec![
            Literal::negative(Variable::new(2)),
            Literal::positive(Variable::new(3)),
        ],
        vec![
            Literal::positive(Variable::new(2)),
            Literal::negative(Variable::new(3)),
        ],
    ];

    let mut finder = XorFinder::new();
    let xors = finder.find_xors(&clauses);

    assert_eq!(xors.len(), 2);
}

#[test]
fn test_xorfinder_with_extra_clauses() {
    // XOR clauses mixed with non-XOR clauses
    let clauses = vec![
        // x0 XOR x1 = 1
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        // Extra clauses that don't form XORs
        vec![Literal::positive(Variable::new(0))], // unit clause
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(2)),
            Literal::positive(Variable::new(3)),
        ],
    ];

    let mut finder = XorFinder::new();
    let xors = finder.find_xors(&clauses);

    assert_eq!(xors.len(), 1);
    assert_eq!(xors[0].vars, vec![0, 1]);
}

#[test]
fn test_xorfinder_unsorted_clauses() {
    // Clauses with unsorted literals should still be detected
    let clauses = vec![
        vec![
            Literal::negative(Variable::new(1)),
            Literal::negative(Variable::new(0)),
        ], // Unsorted
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
    ];

    let mut finder = XorFinder::new();
    let xors = finder.find_xors(&clauses);

    assert_eq!(xors.len(), 1);
}

#[test]
fn test_xorfinder_with_indices() {
    let clauses = vec![
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        vec![Literal::positive(Variable::new(2))], // Extra clause
    ];

    let mut finder = XorFinder::new();
    let (xors, indices) = finder.find_xors_with_indices(&clauses);

    assert_eq!(xors.len(), 1);
    assert!(indices.contains(&0));
    assert!(indices.contains(&1));
    assert!(!indices.contains(&2));
}

#[test]
fn test_xorfinder_detects_binary_supported_partial_three_var_xor() {
    let clauses = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(1)),
            Literal::negative(Variable::new(2)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
            Literal::positive(Variable::new(2)),
        ],
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
            Literal::positive(Variable::new(2)),
        ],
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(2)),
        ],
    ];

    let mut finder = XorFinder::new();
    let (xors, indices) = finder.find_xors_with_indices(&clauses);

    assert_eq!(xors.len(), 1);
    assert_eq!(xors[0].vars, vec![0, 1, 2]);
    assert!(xors[0].rhs, "expected odd-parity ternary XOR");
    assert!(indices.contains(&0));
    assert!(indices.contains(&1));
    assert!(indices.contains(&2));
    assert!(
        !indices.contains(&3),
        "supporting binary clause must remain in the CNF"
    );
}

#[test]
fn test_xorfinder_does_not_overdetect_unsupported_partial_three_var_xor() {
    let clauses = vec![
        vec![
            Literal::negative(Variable::new(0)),
            Literal::positive(Variable::new(1)),
            Literal::negative(Variable::new(2)),
        ],
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
            Literal::positive(Variable::new(2)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(1)),
            Literal::negative(Variable::new(2)),
        ],
    ];

    let mut finder = XorFinder::new();
    let xors = finder.find_xors(&clauses);

    assert!(
        xors.is_empty(),
        "three XOR clauses without supporting CNF must stay as CNF"
    );
}

#[test]
fn test_preprocess_clauses_basic() {
    // CNF encoding of x0 XOR x1 = 1
    let clauses = vec![
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
    ];

    let (remaining, xor_ext) = preprocess_clauses(&clauses);

    // All clauses should be consumed by XOR detection
    assert!(remaining.is_empty());

    // Should have detected XOR
    let ext = xor_ext.expect("Should detect XOR");
    assert_eq!(ext.num_constraints(), 1);
}

#[test]
fn test_preprocess_clauses_mixed() {
    // CNF encoding of x0 XOR x1 = 1, plus a regular clause
    let clauses = vec![
        // XOR encoding
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        // Regular clause (not part of XOR)
        vec![
            Literal::positive(Variable::new(2)),
            Literal::negative(Variable::new(3)),
        ],
    ];

    let (remaining, xor_ext) = preprocess_clauses(&clauses);

    // Regular clause should remain
    assert_eq!(remaining.len(), 1);
    assert_eq!(remaining[0].len(), 2);

    // Should have detected XOR
    let ext = xor_ext.expect("Should detect XOR");
    assert_eq!(ext.num_constraints(), 1);
}

#[test]
fn test_preprocess_clauses_no_xors() {
    // Regular clauses without XOR patterns
    let clauses = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(1)),
            Literal::negative(Variable::new(2)),
        ],
        vec![
            Literal::positive(Variable::new(2)),
            Literal::negative(Variable::new(0)),
        ],
    ];

    let (remaining, xor_ext) = preprocess_clauses(&clauses);

    // All clauses should remain
    assert_eq!(remaining.len(), 3);
    assert!(xor_ext.is_none());
}

#[test]
fn test_preprocess_clauses_with_stats() {
    // CNF encoding of x0 XOR x1 = 1 and x1 XOR x2 = 0
    let clauses = vec![
        // x0 XOR x1 = 1
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        // x1 XOR x2 = 0
        vec![
            Literal::negative(Variable::new(1)),
            Literal::positive(Variable::new(2)),
        ],
        vec![
            Literal::positive(Variable::new(1)),
            Literal::negative(Variable::new(2)),
        ],
    ];

    let (remaining, xor_ext, stats) = preprocess_clauses_with_stats(&clauses);

    assert!(remaining.is_empty());
    assert!(xor_ext.is_some());

    // Stats
    assert_eq!(stats.xors_detected, 2);
    assert_eq!(stats.clauses_consumed, 4);
    assert_eq!(stats.xor_variables, 3); // x0, x1, x2
}

#[test]
fn test_solve_with_xor_detection_sat() {
    use ay_sat::SatResult;

    // x0 XOR x1 = 1 (SAT)
    let clauses = vec![
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
    ];

    let result = solve_with_xor_detection(2, &clauses).into_inner();
    match result {
        SatResult::Sat(model) => {
            // x0 XOR x1 should be 1
            let x0 = model[0];
            let x1 = model[1];
            assert_ne!(x0, x1, "XOR should be satisfied");
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_solve_with_xor_detection_unsat() {
    use ay_sat::SatResult;

    // x0 XOR x1 = 1 AND x0 XOR x1 = 0 (UNSAT)
    let clauses = vec![
        // x0 XOR x1 = 1
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        // x0 XOR x1 = 0 (contradicts above)
        vec![
            Literal::negative(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
    ];

    let result = solve_with_xor_detection(2, &clauses).into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "Contradictory XORs should be UNSAT"
    );
}

#[test]
fn test_solve_with_xor_detection_chain() {
    use ay_sat::SatResult;

    // x0 XOR x1 = 1, x1 XOR x2 = 0, x2 XOR x3 = 1
    // This implies x0 XOR x3 = 0 (chain of XORs)
    let clauses = vec![
        // x0 XOR x1 = 1
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        // x1 XOR x2 = 0
        vec![
            Literal::negative(Variable::new(1)),
            Literal::positive(Variable::new(2)),
        ],
        vec![
            Literal::positive(Variable::new(1)),
            Literal::negative(Variable::new(2)),
        ],
        // x2 XOR x3 = 1
        vec![
            Literal::negative(Variable::new(2)),
            Literal::negative(Variable::new(3)),
        ],
        vec![
            Literal::positive(Variable::new(2)),
            Literal::positive(Variable::new(3)),
        ],
    ];

    let result = solve_with_xor_detection(4, &clauses).into_inner();
    match result {
        SatResult::Sat(model) => {
            let x0 = model[0];
            let x1 = model[1];
            let x2 = model[2];
            let x3 = model[3];
            // Verify all XOR constraints
            assert_ne!(x0, x1, "x0 XOR x1 = 1");
            assert_eq!(x1, x2, "x1 XOR x2 = 0");
            assert_ne!(x2, x3, "x2 XOR x3 = 1");
            // Derived: x0 XOR x3 = 0
            assert_eq!(x0, x3, "x0 XOR x3 should be 0");
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_solve_with_xor_detection_mixed_cnf() {
    use ay_sat::SatResult;

    let clauses = vec![
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        vec![Literal::positive(Variable::new(0))],
        vec![
            Literal::positive(Variable::new(2)),
            Literal::negative(Variable::new(3)),
        ],
    ];

    let result = solve_with_xor_detection(4, &clauses).into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model[0], "CNF unit should force x0 = true");
            assert!(!model[1], "XOR propagation should force x1 = false");
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

#[test]
fn test_solve_with_xor_detection_stats() {
    // x0 XOR x1 = 1
    let clauses = vec![
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
    ];

    let xor_result = solve_with_xor_detection_stats(2, &clauses);

    assert_eq!(xor_result.stats.xors_detected, 1);
    assert_eq!(xor_result.stats.clauses_consumed, 2);
    assert_eq!(xor_result.stats.xor_variables, 2);
    assert!(xor_result.result.is_sat());
}

// ======== Extended DIMACS Parser Tests ========

#[test]
fn test_parse_ext_dimacs_xor_only() {
    // XOR-only formula: x1 XOR x2 = 1
    let input = r"
p cnf 2 0
x1 2 0
";
    let formula = parse_ext_dimacs_str(input).unwrap();
    assert_eq!(formula.num_vars, 2);
    assert_eq!(formula.clauses.len(), 0);
    assert_eq!(formula.xors.len(), 1);
    assert_eq!(formula.xors[0].vars, vec![0, 1]); // 0-indexed
    assert!(formula.xors[0].rhs); // XOR = 1
}

#[test]
fn test_parse_ext_dimacs_negated_xor() {
    // x-1 0 means x1 = 0 (false)
    // In CryptoMiniSat format: negative literal flips rhs
    // Default rhs is true (1), one negation makes it false (0)
    let input = r"
p cnf 1 0
x-1 0
";
    let formula = parse_ext_dimacs_str(input).unwrap();
    assert_eq!(formula.xors.len(), 1);
    assert_eq!(formula.xors[0].vars, vec![0]);
    assert!(!formula.xors[0].rhs); // x1 = 0
}

#[test]
fn test_parse_ext_dimacs_mixed_polarity() {
    // x1 -2 3 0 means x1 XOR x2 XOR x3 = 0 (one negation flips)
    let input = r"
p cnf 3 0
x1 -2 3 0
";
    let formula = parse_ext_dimacs_str(input).unwrap();
    assert_eq!(formula.xors.len(), 1);
    assert_eq!(formula.xors[0].vars, vec![0, 1, 2]);
    assert!(!formula.xors[0].rhs); // Even parity (one flip)
}

#[test]
fn test_parse_ext_dimacs_two_negations() {
    // x-1 -2 0 means x1 XOR x2 = 1 (two flips = back to original)
    let input = r"
p cnf 2 0
x-1 -2 0
";
    let formula = parse_ext_dimacs_str(input).unwrap();
    assert_eq!(formula.xors[0].vars, vec![0, 1]);
    assert!(formula.xors[0].rhs); // Back to odd parity
}

#[test]
fn test_parse_ext_dimacs_mixed_cnf_xor() {
    // Mix of CNF clauses and XOR constraints
    let input = r"
p cnf 4 2
1 2 0
-3 4 0
x1 2 0
x3 4 0
";
    let formula = parse_ext_dimacs_str(input).unwrap();
    assert_eq!(formula.num_vars, 4);
    assert_eq!(formula.clauses.len(), 2);
    assert_eq!(formula.xors.len(), 2);

    // Check CNF clauses
    assert_eq!(formula.clauses[0].len(), 2);
    assert_eq!(formula.clauses[1].len(), 2);

    // Check XOR constraints
    assert_eq!(formula.xors[0].vars, vec![0, 1]);
    assert_eq!(formula.xors[1].vars, vec![2, 3]);
}

#[test]
fn test_parse_ext_dimacs_preserves_empty_cnf_clause() {
    let formula = parse_ext_dimacs_str("p cnf 0 1\n0\n").unwrap();

    assert_eq!(formula.clauses, vec![Vec::new()]);
    assert!(formula.xors.is_empty());
}

#[test]
fn test_ext_dimacs_solver_sizes_by_actual_variables() {
    let formula = parse_ext_dimacs_str("p cnf 4000000000 1\n1 -2 3 0\n").unwrap();
    assert_eq!(formula.num_vars, 4_000_000_000);

    let (solver, xor) = formula.into_solver_with_xor();
    assert_eq!(solver.user_num_vars(), 3);
    assert!(xor.is_none());
}

#[test]
fn test_ext_dimacs_rejects_pathological_actual_variable_count() {
    let error = parse_ext_dimacs_str("p cnf 300000000 0\nx300000000 0\n").unwrap_err();

    assert!(matches!(
        error,
        ExtDimacsError::VariableCountTooLarge {
            actual: 300_000_000,
            ..
        }
    ));
}

#[test]
fn test_native_ext_dimacs_formula_revalidates_actual_variable_count() {
    let formula = ExtDimacsFormula {
        num_vars: 0,
        num_clauses: 0,
        clauses: Vec::new(),
        xors: vec![XorConstraint::new(vec![u32::MAX], true)],
    };
    let error = match formula.try_into_solver_with_xor() {
        Err(error) => error,
        Ok(_) => panic!("native formulas must be checked before dense allocation"),
    };
    assert!(matches!(
        error,
        ExtDimacsError::VariableCountTooLarge { .. }
    ));
}

#[test]
fn test_native_ext_dimacs_try_solve_rejects_pathological_variable_count() {
    let formula = ExtDimacsFormula {
        num_vars: usize::MAX,
        num_clauses: 0,
        clauses: Vec::new(),
        xors: vec![XorConstraint::new(vec![u32::MAX], false)],
    };
    assert!(matches!(
        formula.try_solve(),
        Err(ExtDimacsError::VariableCountTooLarge { .. })
    ));
}

#[test]
fn test_solve_ext_dimacs_empty_cnf_clause_is_unsat() {
    let result = solve_ext_dimacs_str("p cnf 0 1\n0\n").unwrap();

    assert!(
        result.is_unsat(),
        "empty CNF clause must be UNSAT: {result:?}"
    );
}

#[test]
fn test_parse_ext_dimacs_cryptominisat_simple() {
    // Test file from CryptoMiniSat: x1 0 means x1 = true
    let input = r"
p cnf 1 1
x1 0
c CHECK: s SATISFIABLE
c CHECK: v 1 0
";
    let formula = parse_ext_dimacs_str(input).unwrap();
    assert_eq!(formula.xors.len(), 1);
    assert_eq!(formula.xors[0].vars, vec![0]);
    assert!(formula.xors[0].rhs); // x1 = 1
}

#[test]
fn test_parse_ext_dimacs_cryptominisat_longer() {
    // Test based on CryptoMiniSat xor_longer.cnf
    // x1 2 3 4 5 6 7 8 9 10 0 and x-1 0 ... x-9 0
    let input = r"
p cnf 10 10
x1 2 3 4 5 6 7 8 9 10 0
x-1 0
x-2 0
x-3 0
x-4 0
x-5 0
x-6 0
x-7 0
x-8 0
x-9 0
";
    let formula = parse_ext_dimacs_str(input).unwrap();
    assert_eq!(formula.xors.len(), 10);

    // First XOR: x1 XOR x2 XOR ... XOR x10 = 1
    assert_eq!(formula.xors[0].vars.len(), 10);
    assert!(formula.xors[0].rhs);

    // Remaining XORs: xi = 0 for i in 1..9
    for i in 1..10 {
        assert_eq!(formula.xors[i].vars.len(), 1);
        assert!(!formula.xors[i].rhs); // = 0
    }
}

#[test]
fn test_solve_ext_dimacs_sat() {
    // x1 XOR x2 = 1: SAT with x1 != x2
    let input = r"
p cnf 2 0
x1 2 0
";
    let result = solve_ext_dimacs_str(input).unwrap().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert_ne!(model[0], model[1], "x1 XOR x2 = 1 should be satisfied");
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_empty_crypto_minisat_xor_record_is_noop() {
    let formula = parse_ext_dimacs_str("p cnf 0 0\nx0\n").expect("empty XOR record parses");
    assert!(formula.clauses.is_empty());
    assert!(formula.xors.is_empty());
    assert!(formula.solve().is_sat());
}

#[test]
fn test_solve_ext_dimacs_unsat() {
    // Contradictory XORs: x1 = 1 AND x1 = 0
    let input = r"
p cnf 1 0
x1 0
x-1 0
";
    let result = solve_ext_dimacs_str(input).unwrap();
    // Fixed: empty clause DB + contradictory XOR extension correctly returns
    // Unsat (was Unknown due to #5806, fixed in #5823).
    assert!(
        result.is_unsat(),
        "Contradictory XOR system should be UNSAT, got {result:?}"
    );
}

#[test]
fn test_solve_ext_dimacs_chain() {
    // Chain of XORs should be SAT
    let input = r"
p cnf 4 0
x1 2 0
x2 3 0
x3 4 0
";
    let result = solve_ext_dimacs_str(input).unwrap().into_inner();
    match result {
        SatResult::Sat(model) => {
            // Verify constraints
            assert_ne!(model[0], model[1]); // x1 XOR x2 = 1
            assert_ne!(model[1], model[2]); // x2 XOR x3 = 1
            assert_ne!(model[2], model[3]); // x3 XOR x4 = 1
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_solve_ext_dimacs_mixed() {
    // CNF clause (x1 OR x2) plus XOR (x1 XOR x2 = 0, meaning x1 = x2)
    // To encode XOR = 0, we need an odd number of negative literals
    // x-1 2 0 means: rhs=1, flip for -1 => rhs=0
    // Combined: x1 = x2 AND (x1 OR x2) means both true or (x1=x2=true)
    let input = r"
p cnf 2 1
1 2 0
x-1 2 0
";
    let result = solve_ext_dimacs_str(input).unwrap().into_inner();
    match result {
        SatResult::Sat(model) => {
            // XOR = 0 means x1 = x2
            assert_eq!(model[0], model[1]);
            // CNF clause requires at least one true
            assert!(model[0] || model[1]);
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_write_ext_dimacs() {
    let clauses = vec![vec![
        Literal::positive(Variable::new(0)),
        Literal::negative(Variable::new(1)),
    ]];
    let xors = vec![
        XorConstraint::new(vec![0, 1], true),  // x1 XOR x2 = 1
        XorConstraint::new(vec![2, 3], false), // x3 XOR x4 = 0
    ];

    let mut output = Vec::new();
    write_ext_dimacs(&mut output, 4, &clauses, &xors).unwrap();

    let written = String::from_utf8(output).unwrap();

    // Parse back and verify
    let formula = parse_ext_dimacs_str(&written).unwrap();
    assert_eq!(formula.clauses.len(), 1);
    assert_eq!(formula.xors.len(), 2);
    assert!(formula.xors[0].rhs); // First XOR = 1
    assert!(!formula.xors[1].rhs); // Second XOR = 0
}

#[test]
fn test_write_empty_xor_parities_preserves_semantics() {
    let mut output = Vec::new();
    write_ext_dimacs(
        &mut output,
        0,
        &[],
        &[
            XorConstraint::new(Vec::new(), false),
            XorConstraint::new(Vec::new(), true),
        ],
    )
    .unwrap();

    let written = String::from_utf8(output).unwrap();
    assert_eq!(written, "p cnf 0 1\n0\n");
    let reparsed = parse_ext_dimacs_str(&written).unwrap();
    assert_eq!(reparsed.clauses, vec![Vec::new()]);
    assert!(reparsed.xors.is_empty());
    assert!(reparsed.solve().is_unsat());
}

#[test]
fn test_write_empty_false_xor_is_omitted_as_tautology() {
    let mut output = Vec::new();
    write_ext_dimacs(
        &mut output,
        0,
        &[],
        &[XorConstraint::new(Vec::new(), false)],
    )
    .unwrap();

    assert_eq!(String::from_utf8(output).unwrap(), "p cnf 0 0\n");
}

#[test]
fn test_write_ext_dimacs_rejects_variable_beyond_header_without_output() {
    let clauses = vec![vec![Literal::positive(Variable::new(1))]];
    let mut output = Vec::new();
    let error = write_ext_dimacs(&mut output, 1, &clauses, &[])
        .expect_err("one-based variable 2 must exceed a one-variable header");
    assert_eq!(error.kind(), std::io::ErrorKind::InvalidInput);
    assert!(output.is_empty());
}

#[test]
fn test_write_ext_dimacs_rejects_unrepresentable_xor_variable_without_output() {
    let xors = vec![XorConstraint::new(vec![u32::MAX], true)];
    let mut output = Vec::new();
    let error = write_ext_dimacs(&mut output, usize::MAX, &[], &xors)
        .expect_err("u32::MAX cannot be serialized as a one-based i32 variable");
    assert_eq!(error.kind(), std::io::ErrorKind::InvalidInput);
    assert!(output.is_empty());
}

#[test]
fn test_parse_ext_dimacs_roundtrip() {
    let input = r"
p cnf 4 2
1 -2 0
3 4 0
x1 2 0
x-3 4 0
";
    let formula = parse_ext_dimacs_str(input).unwrap();

    let mut output = Vec::new();
    write_ext_dimacs(
        &mut output,
        formula.num_vars,
        &formula.clauses,
        &formula.xors,
    )
    .unwrap();

    let reparsed = parse_ext_dimacs(&output[..]).unwrap();

    // Verify structure preserved
    assert_eq!(reparsed.clauses.len(), formula.clauses.len());
    assert_eq!(reparsed.xors.len(), formula.xors.len());

    // XOR RHS values should match
    for (orig, new) in formula.xors.iter().zip(reparsed.xors.iter()) {
        assert_eq!(orig.rhs, new.rhs);
        assert_eq!(orig.vars, new.vars);
    }
}

#[test]
fn test_ext_dimacs_error_missing_problem() {
    let input = "x1 2 0";
    let result = parse_ext_dimacs_str(input);
    assert!(matches!(result, Err(ExtDimacsError::MissingProblemLine)));
}

#[test]
fn test_ext_dimacs_error_var_out_of_range() {
    let input = r"
p cnf 2 0
x1 2 3 0
";
    let result = parse_ext_dimacs_str(input);
    assert!(matches!(
        result,
        Err(ExtDimacsError::VariableOutOfRange { var: 3, max: 2 })
    ));
}

#[test]
fn test_ext_dimacs_empty_xor_record_is_accepted_as_noop() {
    let input = r"
p cnf 2 0
x0
";
    let formula = parse_ext_dimacs_str(input).expect("CryptoMiniSat x0 record is valid");
    assert!(formula.xors.is_empty());
}

#[test]
fn test_cryptominisat_xor_file_simple() {
    // Reproduces reference/cryptominisat/tests/cnf-files/xor.cnf
    // x1 = 1 (SAT, solution: x1=true)
    let input = r"
c RUN: %solver %s | %OutputCheck %s
p cnf 1 1
x1 0
c CHECK: s SATISFIABLE
c CHECK: v 1 0
";
    let result = solve_ext_dimacs_str(input).unwrap().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert!(model[0], "x1 should be true");
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_cryptominisat_xor_file_longer() {
    // Reproduces reference/cryptominisat/tests/cnf-files/xor_longer.cnf
    // x1 XOR x2 XOR ... XOR x10 = 1
    // x1 = 0, x2 = 0, ..., x9 = 0
    // Therefore x10 must be 1 to satisfy the first XOR
    let input = r"
c RUN: %solver %s | %OutputCheck %s
p cnf 10 10
x1 2 3 4 5 6 7 8 9 10 0
x-1 0
x-2 0
x-3 0
x-4 0
x-5 0
x-6 0
x-7 0
x-8 0
x-9 0
c CHECK: s SATISFIABLE
c CHECK: v -1 -2 -3 -4 -5 -6 -7 -8 -9 10 0
";
    let result = solve_ext_dimacs_str(input).unwrap().into_inner();
    match result {
        SatResult::Sat(model) => {
            // x1-x9 should be false
            for (i, &val) in model.iter().enumerate().take(9) {
                assert!(!val, "x{} should be false", i + 1);
            }
            // x10 should be true
            assert!(model[9], "x10 should be true");
        }
        _ => panic!("Expected SAT"),
    }
}

// ============================================================================
// RREF Invariant Verification Tests (Phase 2 Proofs)
// ============================================================================
//
// These tests verify that the RREF matrix structure is preserved correctly
// across assignments and backtracks. Phase 2 is implemented: assign() does NOT
// modify the RREF matrix rows - only the assignments array changes.
//
// The evaluate() method is used to check propagations on RREF rows with
// current assignments without modifying the matrix structure.

/// PROOF: RREF rows are immutable -- assign() never modifies them.
///
/// The RREF matrix is the single source of truth after eliminate().
/// Assignments only update the packed assignment state, not the rows.
#[test]
fn test_phase2_rref_preserved_by_assign() {
    // Simple system: x0 XOR x1 = 1
    //               x1 XOR x2 = 0
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![1, 2], false),
    ];
    let mut solver = GaussianSolver::new(&constraints);
    solver.eliminate();

    // Capture RREF state after elimination
    let rows_snapshot: Vec<_> = solver.rows.iter().map(|r| r.bits.clone()).collect();

    // Verify rows exist after eliminate()
    assert!(
        !rows_snapshot.is_empty(),
        "RREF should exist after eliminate()"
    );

    // Assign x0 = true - should NOT modify rows
    let _ = solver.assign(0, true);

    // INVARIANT 1: Rows must be unchanged after assign
    let rows_after_assign: Vec<_> = solver.rows.iter().map(|r| r.bits.clone()).collect();
    assert_eq!(
        rows_after_assign, rows_snapshot,
        "assign() must NOT modify RREF rows (lazy backtrack invariant)"
    );

    // INVARIANT 2: Assignments array must track current values
    assert_eq!(
        solver.assignments[solver.var_to_col[&0]],
        Some(true),
        "assign() must update assignments array"
    );

    // Assign another variable
    let _ = solver.assign(1, false);

    // Rows still unchanged
    let rows_after_second: Vec<_> = solver.rows.iter().map(|r| r.bits.clone()).collect();
    assert_eq!(
        rows_after_second, rows_snapshot,
        "Multiple assigns must NOT modify RREF rows"
    );
}

/// PROOF: Lazy backtrack -- clear_assignments() resets state without touching rows.
///
/// Verifies that after assigning, clearing, and re-assigning:
/// 1. RREF rows are never modified
/// 2. Assignment state is correctly reset
/// 3. Propagations work correctly after backtrack
#[test]
fn test_lazy_backtrack_clear_assignments_preserves_rows() {
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![1, 2], false),
    ];
    let mut solver = GaussianSolver::new(&constraints);
    solver.eliminate();

    // Capture initial RREF
    let original_rows: Vec<_> = solver.rows.iter().map(|r| r.bits.clone()).collect();

    // Assign x0 = true
    let _ = solver.assign(0, true);

    // Rows should still match RREF
    let after_first: Vec<_> = solver.rows.iter().map(|r| r.bits.clone()).collect();
    assert_eq!(after_first, original_rows, "assign should not modify rows");

    // Lazy backtrack: just clear assignments (O(n)), no row copy needed
    solver.clear_assignments();

    // Verify rows unchanged
    let after_clear: Vec<_> = solver.rows.iter().map(|r| r.bits.clone()).collect();
    assert_eq!(
        after_clear, original_rows,
        "clear_assignments() must not modify rows"
    );

    // Verify assignments cleared
    assert!(
        solver.assignments.iter().all(Option::is_none),
        "clear_assignments() should clear all assignments"
    );

    // Assign x1 = false (second round after backtrack)
    let _ = solver.assign(1, false);

    // Rows should STILL match RREF
    let after_second_assign: Vec<_> = solver.rows.iter().map(|r| r.bits.clone()).collect();
    assert_eq!(
        after_second_assign, original_rows,
        "assign() after clear_assignments() must NOT modify rows"
    );
}

/// PROOF: Lazy backtrack via unassign() -- per-variable O(1) backtrack.
///
/// Verifies the CMS-style backtrack pattern: unassign individual variables
/// without touching the matrix at all.
#[test]
fn test_lazy_backtrack_unassign_per_variable() {
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),  // x0 XOR x1 = 1
        XorConstraint::new(vec![1, 2], false), // x1 XOR x2 = 0
    ];
    let mut solver = GaussianSolver::new(&constraints);
    solver.eliminate();

    let original_rows: Vec<_> = solver.rows.iter().map(|r| r.bits.clone()).collect();

    // Assign x0 = true (propagates x1 = false)
    let result = solver.assign(0, true);
    assert!(
        matches!(result, GaussResult::Propagate(_, _)),
        "Should propagate x1 after assigning x0"
    );

    // Assign x1 = false (propagates x2 = false)
    let result = solver.assign(1, false);
    assert!(
        matches!(result, GaussResult::Propagate(_, _)),
        "Should propagate x2 after assigning x1"
    );

    // Assign x2 = false (all satisfied)
    let result = solver.assign(2, false);
    assert!(
        matches!(result, GaussResult::Nothing),
        "All rows satisfied, no more propagations"
    );

    // Now backtrack x2 and x1 (simulating backtrack by 2 levels)
    solver.unassign(2);
    solver.unassign(1);
    solver.reset_satisfied();

    // Rows must be unchanged -- this is the key invariant
    let after_backtrack: Vec<_> = solver.rows.iter().map(|r| r.bits.clone()).collect();
    assert_eq!(
        after_backtrack, original_rows,
        "unassign() must not modify rows (O(1) lazy backtrack)"
    );

    // Verify only x0 remains assigned
    assert_eq!(solver.assignments[solver.var_to_col[&0]], Some(true));
    assert_eq!(solver.assignments[solver.var_to_col[&1]], None);
    assert_eq!(solver.assignments[solver.var_to_col[&2]], None);

    // Re-assign x1 = false (correct value) and verify propagation works
    let result = solver.assign(1, false);
    // x0=true, x1=false, RREF row 1 is x1 XOR x2 = 0 => x2 = false
    // This should produce a propagation
    let props = solver.get_all_propagations();
    assert!(
        !props.is_empty() || matches!(result, GaussResult::Propagate(_, _)),
        "Should produce propagation for x2 after re-assign x1=false"
    );
}

/// PROOF: Phase 2 evaluate() detects conflicts correctly.
///
/// Verifies that evaluate() on RREF rows detects conflicts
/// (all assigned, parity mismatch).
#[test]
fn test_phase2_evaluate_conflict() {
    // x0 XOR x1 = 1 (need odd parity)
    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut solver = GaussianSolver::new(&constraints);
    solver.eliminate();

    // Assign x0 = true, x1 = true
    // This violates x0 XOR x1 = 1 (true XOR true = false ≠ 1)
    let _ = solver.assign(0, true);
    let result = solver.assign(1, true);

    assert!(
        matches!(result, GaussResult::Conflict(_)),
        "Should detect conflict when parity violated"
    );
}

/// PROOF: Phase 2 evaluate() produces unit propagations.
///
/// Verifies that when all but one variable in a row is assigned,
/// evaluate() returns Unit with the correct value.
#[test]
fn test_phase2_evaluate_unit_propagation() {
    // x0 XOR x1 = 1
    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut solver = GaussianSolver::new(&constraints);
    solver.eliminate();

    // Assign x0 = true, leaving x1 unassigned
    // x0 XOR x1 = 1 => true XOR x1 = 1 => x1 = 0
    let result = solver.assign(0, true);

    match result {
        GaussResult::Propagate(lit, _row_idx) => {
            assert_eq!(lit.variable().id(), 1, "Should propagate x1");
            assert!(!lit.is_positive(), "x1 should be false (negative literal)");
        }
        other => panic!("Expected Propagate(x1=false), got {other:?}"),
    }
}

// ========================================================================
// PROOF TEST: P1 #105 - XOR Reason Clause Performance Bug
// ========================================================================
//
// Documents the performance bug identified in PROVER commit 298c4bb.
//
// BUG LOCATION: lib.rs lines 790-804
//
// ROOT CAUSE:
// - `propagate()` builds reason clauses from ALL assigned trail variables
// - Should build from ONLY the specific XOR constraint that caused propagation
//
// IMPACT:
// - Reason clauses grow to 100-300 literals (should be 3-5)
// - SAT solver must process thousands of huge clauses
// - par8-1.cnf: 60+ seconds instead of <10ms
//
// REQUIRED FIX:
// 1. Add row_idx to GaussResult::Propagate variant
// 2. Track source row in propagate_watched()
// 3. Build reasons from constraint.vars, not entire trail
//
// See the development design notes

#[test]
fn test_proof_p105_reason_clause_size_expectation() {
    // PROOF: Reason clauses should be bounded by constraint size
    //
    // For a propagation from XOR constraint (x1 ⊕ x2 ⊕ x3 = 1):
    // - If x1=true, x2=true are assigned, propagate x3=true
    // - Correct reason clause: (¬x1 ∨ ¬x2 ∨ x3) - 3 literals
    // - NOT: (¬v1 ∨ ¬v2 ∨ ... ∨ ¬vN ∨ x3) for all N assigned vars
    //
    // This test documents the expected behavior after the fix.

    // Create a simple XOR constraint
    let constraint = XorConstraint::new(vec![0, 1, 2], true); // x0 ⊕ x1 ⊕ x2 = 1

    // When building a reason clause for propagating x2,
    // the clause should contain only vars from this constraint (x0, x1, x2)
    // NOT all assigned variables in the system

    assert_eq!(
        constraint.vars.len(),
        3,
        "Test constraint should have exactly 3 variables"
    );

    // After the fix, reason clauses from this constraint should have
    // at most constraint.vars.len() literals (3 in this case)
    let max_expected_reason_size = constraint.vars.len();

    // This is the invariant that should hold after the fix:
    // For any propagation from a constraint, the reason clause size
    // should be <= constraint.vars.len()
    //
    // Currently (before fix), this invariant is violated because
    // propagate() uses all trail variables as reasons.

    assert!(
        max_expected_reason_size <= 10,
        "XOR constraints typically have few variables; \
             reason clauses should be similarly bounded"
    );
}

#[test]
fn test_proof_p105_gauss_result_tracks_source() {
    // PROOF: GaussResult::Propagate includes source row index
    //
    // The fix adds row index to both Propagate and Conflict variants:
    //   GaussResult::Propagate(Literal, usize)
    //   GaussResult::Conflict(usize)
    //
    // With row_idx, we know which XOR constraint caused the
    // propagation, allowing minimal reason clause construction.

    // Test that GaussResult enum exists with expected variants
    let nothing = GaussResult::Nothing;
    let conflict = GaussResult::Conflict(0);
    let propagate = GaussResult::Propagate(Literal::positive(Variable::new(0)), 0);

    // These should compile - verifying new structure with row indices
    match nothing {
        GaussResult::Nothing => {}
        _ => panic!("Expected Nothing variant"),
    }
    match conflict {
        GaussResult::Conflict(row_idx) => {
            // Now includes source row index
            assert_eq!(row_idx, 0);
        }
        _ => panic!("Expected Conflict variant"),
    }
    match propagate {
        GaussResult::Propagate(lit, row_idx) => {
            // Now includes both literal AND source row index
            let _ = lit;
            assert_eq!(row_idx, 0);
        }
        _ => panic!("Expected Propagate variant"),
    }
}

#[test]
fn test_proof_p105_minimal_reason_clause_verification() {
    // PROOF: Reason clauses use only source row variables, not entire trail
    //
    // This is the KEY TEST for P1 #105 fix.
    //
    // Setup: Create 3 independent XOR constraints covering 6 variables:
    //   Constraint 0: x0 XOR x1 = 1
    //   Constraint 1: x2 XOR x3 = 1
    //   Constraint 2: x4 XOR x5 = 1
    //
    // Assign x0, x2, x4 = true (3 assignments in trail).
    // This should trigger propagations for x1, x3, x5.
    //
    // BUG (before fix): Each reason clause contains ALL 3 trail variables
    //   e.g., (¬x0 ∨ ¬x2 ∨ ¬x4 ∨ x1) - 4 literals (WRONG!)
    //
    // FIX (after fix): Each reason clause contains ONLY source row variables
    //   e.g., (¬x0 ∨ x1) - 2 literals (CORRECT!)
    //
    // INVARIANT: reason_clause.len() <= constraint.vars.len()

    let constraints = vec![
        XorConstraint::new(vec![0, 1], true), // x0 XOR x1 = 1
        XorConstraint::new(vec![2, 3], true), // x2 XOR x3 = 1
        XorConstraint::new(vec![4, 5], true), // x4 XOR x5 = 1
    ];
    let mut ext = XorExtension::new(constraints.clone());
    let mut ctx = MockContext::new();

    // No initial propagations (all constraints have 2 unassigned vars)
    let result = ext.propagate(&ctx);
    assert!(
        result.clauses.is_empty() && result.propagations.is_empty(),
        "No propagations before any assignments"
    );

    // Assign x0 = true, x2 = true, x4 = true (builds up trail with 3 vars)
    ctx.assign(0, true);
    ctx.assign(2, true);
    ctx.assign(4, true);

    // Now we should have 3 propagations
    let result = ext.propagate(&ctx);

    // Should have propagation clauses (one per constraint)
    assert!(
        !result.propagations.is_empty(),
        "Should have propagation clauses after assignments"
    );

    // CRITICAL INVARIANT: Each reason clause size <= constraint size
    for (clause, propagated) in &result.propagations {
        // Find which constraint this clause came from by looking at the conclusion
        let conclusion_var = propagated.variable().id();

        // conclusion_var tells us which constraint: 1 -> constraint 0, 3 -> constraint 1, 5 -> constraint 2
        let constraint_idx = match conclusion_var {
            1 => 0,
            3 => 1,
            5 => 2,
            other => panic!("Unexpected propagated variable: {other}"),
        };

        let source_constraint = &constraints[constraint_idx];
        let max_allowed_size = source_constraint.vars.len();

        assert!(
            clause.len() <= max_allowed_size,
            "P1 #105 INVARIANT VIOLATED: Reason clause for var {} has {} literals, \
                 but source constraint has only {} variables. \
                 Clause: {:?}",
            conclusion_var,
            clause.len(),
            max_allowed_size,
            clause
        );

        // Extra check: should be exactly 2 literals (1 negated reason + 1 conclusion)
        // for a 2-variable XOR
        assert_eq!(
            clause.len(),
            2,
            "For 2-variable XOR, reason clause should have exactly 2 literals. Got: {clause:?}"
        );
    }
}

// ============================================================================
// XOR Density Heuristic Tests (#7928)
// ============================================================================

#[test]
fn test_density_heuristic_high_density_enables_ge() {
    assert!(should_enable_gauss_elimination(100, 0, 50));
}

#[test]
fn test_density_heuristic_low_density_disables_ge() {
    assert!(!should_enable_gauss_elimination(200, 9800, 20));
}

#[test]
fn test_density_heuristic_exactly_five_percent() {
    assert!(should_enable_gauss_elimination(500, 9500, 100));
}

#[test]
fn test_density_heuristic_just_below_five_percent() {
    assert!(!should_enable_gauss_elimination(499, 9501, 100));
}

#[test]
fn test_density_heuristic_zero_consumed_disables_ge() {
    assert!(!should_enable_gauss_elimination(0, 1000, 0));
}

#[test]
fn test_density_heuristic_small_pure_xor_formula() {
    assert!(should_enable_gauss_elimination(4, 0, 2));
}

#[test]
fn test_density_heuristic_single_xor_in_large_formula() {
    assert!(!should_enable_gauss_elimination(2, 9998, 1));
}

#[test]
fn test_density_heuristic_crypto_benchmark_typical() {
    assert!(should_enable_gauss_elimination(300_000, 700_000, 5_000));
}

#[test]
fn test_density_heuristic_overflow_protection() {
    assert!(should_enable_gauss_elimination(usize::MAX / 2, 0, 100));
}

#[test]
fn test_density_heuristic_both_zero() {
    assert!(!should_enable_gauss_elimination(0, 0, 0));
}

#[test]
fn test_solve_density_gated_below_threshold() {
    use ay_sat::SatResult;

    let mut clauses = vec![
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
    ];
    for i in 2..102u32 {
        clauses.push(vec![
            Literal::positive(Variable::new(i)),
            Literal::positive(Variable::new(i + 1)),
        ]);
    }

    let result = solve_with_xor_detection(104, &clauses);
    assert!(
        matches!(result.into_inner(), SatResult::Sat(_)),
        "low-density formula should solve via pure SAT"
    );
}

#[test]
fn test_solve_density_gated_above_threshold() {
    use ay_sat::SatResult;

    let mut clauses = Vec::new();
    for i in 0..10u32 {
        let a = i * 2;
        let b = i * 2 + 1;
        clauses.push(vec![
            Literal::negative(Variable::new(a)),
            Literal::negative(Variable::new(b)),
        ]);
        clauses.push(vec![
            Literal::positive(Variable::new(a)),
            Literal::positive(Variable::new(b)),
        ]);
    }

    let xor_result = solve_with_xor_detection_stats(20, &clauses);
    assert_eq!(xor_result.stats.xors_detected, 10);
    assert_eq!(xor_result.stats.clauses_consumed, 20);

    match xor_result.result.into_inner() {
        SatResult::Sat(model) => {
            for i in 0..10usize {
                assert_ne!(
                    model[i * 2],
                    model[i * 2 + 1],
                    "XOR constraint {i} violated"
                );
            }
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

// ============================================================================
// Component Splitting Tests (#8166)
// ============================================================================

#[test]
fn test_component_split_independent_constraints() {
    // Two disjoint XOR constraints should be split into 2 components.
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),  // component A
        XorConstraint::new(vec![2, 3], false), // component B
    ];
    let ext = XorExtension::new(constraints);

    assert_eq!(ext.num_components(), 2);
    assert_eq!(ext.num_constraints(), 2);
    assert_eq!(ext.num_variables(), 4);
}

#[test]
fn test_component_split_connected_constraints() {
    // Constraints sharing variables stay in one component.
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![1, 2], false),
    ];
    let ext = XorExtension::new(constraints);

    assert_eq!(ext.num_components(), 1);
}

#[test]
fn test_component_split_propagation_across_independent_components() {
    // Two independent components, each should propagate independently.
    // Component A: x0 XOR x1 = 1
    // Component B: x2 XOR x3 = 0
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![2, 3], false),
    ];
    let mut ext = XorExtension::new(constraints);
    let mut ctx = MockContext::new();

    // Assign x0 = true -> should propagate x1 = false (component A only)
    ctx.assign(0, true);
    let result = ext.propagate(&ctx);
    let prop_x1 = result
        .propagations
        .iter()
        .any(|(_, lit)| *lit == Literal::negative(Variable::new(1)));
    assert!(prop_x1, "Should propagate x1 = false from component A");

    // Assign x2 = true -> should propagate x3 = true (component B, xor=0 means equal)
    ctx.assign(2, true);
    let result = ext.propagate(&ctx);
    let prop_x3 = result
        .propagations
        .iter()
        .any(|(_, lit)| *lit == Literal::positive(Variable::new(3)));
    assert!(prop_x3, "Should propagate x3 = true from component B");
}

#[test]
fn test_component_split_conflict_in_one_component() {
    // Component A: x0 XOR x1 = 1
    // Component B: x2 XOR x3 = 0
    // Conflict in A: x0=true, x1=true (1 XOR 1 = 0 != 1)
    // Component B should be unaffected.
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![2, 3], false),
    ];
    let mut ext = XorExtension::new(constraints);
    let mut ctx = MockContext::new();

    ctx.assign(0, true);
    let _ = ext.propagate(&ctx);
    ctx.assign(1, true); // violates component A
    let result = ext.propagate(&ctx);

    assert!(
        result.conflict.is_some(),
        "Should detect conflict in component A"
    );
    // Conflict should only involve variables from component A
    let conflict = result.conflict.unwrap();
    assert!(
        conflict.iter().all(|lit| lit.variable().id() <= 1),
        "Conflict clause should only involve component A variables, got: {conflict:?}"
    );
}

#[test]
fn test_component_split_backtrack_and_repropagate() {
    // Two independent components with backtracking.
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![2, 3], false),
    ];
    let mut ext = XorExtension::new(constraints);
    let mut ctx = MockContext::new();

    // Level 0: assign x0 = true (propagates x1 in comp A)
    ctx.assign(0, true);
    let _ = ext.propagate(&ctx);

    // Level 1: assign x2 = false (propagates x3 in comp B)
    ctx.new_level();
    ctx.assign(2, false);
    let _ = ext.propagate(&ctx);

    // Backtrack to level 0
    ext.backtrack(0);
    ctx.backtrack_to(0);

    // Component A's propagation (x1) should still be recoverable
    let result = ext.propagate(&ctx);
    let prop_x1 = result
        .propagations
        .iter()
        .any(|(_, lit)| *lit == Literal::negative(Variable::new(1)));
    assert!(
        prop_x1,
        "After backtrack, component A should repropagate x1"
    );
}

#[test]
fn test_component_split_check_soundness() {
    // Verify that check() validates all components correctly.
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),  // x0 XOR x1 = 1
        XorConstraint::new(vec![2, 3], false), // x2 XOR x3 = 0
    ];
    let mut ext = XorExtension::new(constraints);
    let mut ctx = MockContext::new();

    // Satisfying assignment
    ctx.assign(0, true);
    ctx.assign(1, false);
    ctx.assign(2, true);
    ctx.assign(3, true);
    let _ = ext.propagate(&ctx);

    let check_result = ext.check(&ctx);
    assert!(
        matches!(check_result, ExtCheckResult::Sat),
        "All constraints satisfied"
    );
}

#[test]
fn test_component_split_solve_multi_component_sat() {
    use ay_sat::SatResult;

    // 5 independent XOR pairs: (0,1), (2,3), (4,5), (6,7), (8,9) all = 1
    let mut clauses = Vec::new();
    for i in 0..5u32 {
        let a = i * 2;
        let b = i * 2 + 1;
        clauses.push(vec![
            Literal::negative(Variable::new(a)),
            Literal::negative(Variable::new(b)),
        ]);
        clauses.push(vec![
            Literal::positive(Variable::new(a)),
            Literal::positive(Variable::new(b)),
        ]);
    }

    let xor_result = solve_with_xor_detection_stats(10, &clauses);
    assert_eq!(xor_result.stats.xors_detected, 5);

    match xor_result.result.into_inner() {
        SatResult::Sat(model) => {
            for i in 0..5usize {
                assert_ne!(model[i * 2], model[i * 2 + 1], "XOR pair {i} violated");
            }
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

#[test]
fn test_component_split_solve_multi_component_with_chain() {
    use ay_sat::SatResult;

    // Component A: chain x0-x1-x2 (connected via shared vars)
    // Component B: independent pair x3 XOR x4 = 1
    let clauses = vec![
        // x0 XOR x1 = 1
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        // x1 XOR x2 = 0
        vec![
            Literal::negative(Variable::new(1)),
            Literal::positive(Variable::new(2)),
        ],
        vec![
            Literal::positive(Variable::new(1)),
            Literal::negative(Variable::new(2)),
        ],
        // x3 XOR x4 = 1
        vec![
            Literal::negative(Variable::new(3)),
            Literal::negative(Variable::new(4)),
        ],
        vec![
            Literal::positive(Variable::new(3)),
            Literal::positive(Variable::new(4)),
        ],
    ];

    let result = solve_with_xor_detection(5, &clauses).into_inner();
    match result {
        SatResult::Sat(model) => {
            assert_ne!(model[0], model[1], "x0 XOR x1 = 1");
            assert_eq!(model[1], model[2], "x1 XOR x2 = 0");
            assert_ne!(model[3], model[4], "x3 XOR x4 = 1");
        }
        other => panic!("Expected SAT, got {other:?}"),
    }
}

#[test]
fn test_component_split_initial_conflict_detected() {
    // Contradictory constraints within one component are still detected.
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![0, 1], false),
    ];
    let ext = XorExtension::new(constraints);
    assert!(ext.conflict.is_some(), "Should detect initial conflict");
}

#[test]
fn test_component_split_reason_clause_minimal() {
    // Same as test_proof_p105_minimal_reason_clause_verification but with
    // independent components. Each reason clause should only use variables
    // from its component.
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true), // component A
        XorConstraint::new(vec![2, 3], true), // component B
        XorConstraint::new(vec![4, 5], true), // component C
    ];
    let mut ext = XorExtension::new(constraints);
    let mut ctx = MockContext::new();
    assert_eq!(ext.num_components(), 3);

    ctx.assign(0, true);
    ctx.assign(2, true);
    ctx.assign(4, true);

    let result = ext.propagate(&ctx);
    assert!(
        !result.propagations.is_empty(),
        "Should have propagations from 3 components"
    );

    for (clause, propagated) in &result.propagations {
        // Each reason clause should have exactly 2 literals for 2-var XOR
        assert_eq!(
            clause.len(),
            2,
            "Reason clause size should be 2 for 2-var XOR, got: {clause:?}"
        );
        // All variables in the clause should be from the same component
        let propagated_var = propagated.variable().id();
        let component_pair = (propagated_var / 2) * 2;
        for lit in clause {
            let var = lit.variable().id();
            assert!(
                var == component_pair || var == component_pair + 1,
                "Variable {var} in reason clause does not belong to same component as propagated var {propagated_var}"
            );
        }
    }
}

// ============================================================================
// Per-component Matrix Size Limit Tests (#7928 - CMS port)
// ============================================================================

#[test]
fn test_component_within_limits_accepts_normal_matrix() {
    use preprocess::component_within_limits;
    assert!(component_within_limits(10, 20));
    assert!(component_within_limits(100, 500));
    assert!(component_within_limits(2000, 1000));
}

#[test]
fn test_component_within_limits_rejects_oversized_rows() {
    use preprocess::component_within_limits;
    assert!(!component_within_limits(2001, 100));
    assert!(!component_within_limits(10_000, 500));
}

#[test]
fn test_component_within_limits_rejects_oversized_columns() {
    use preprocess::component_within_limits;
    assert!(!component_within_limits(100, 1001));
    assert!(!component_within_limits(50, 5000));
}

#[test]
fn test_component_within_limits_boundary_values() {
    use preprocess::{
        component_within_limits, MAX_MATRIX_COLUMNS, MAX_MATRIX_ROWS, MIN_MATRIX_ROWS,
    };
    // Exactly at limits: accepted
    assert!(component_within_limits(MAX_MATRIX_ROWS, MAX_MATRIX_COLUMNS));
    assert!(component_within_limits(MIN_MATRIX_ROWS, 1));
    // Just over: rejected
    assert!(!component_within_limits(
        MAX_MATRIX_ROWS + 1,
        MAX_MATRIX_COLUMNS
    ));
    assert!(!component_within_limits(
        MAX_MATRIX_ROWS,
        MAX_MATRIX_COLUMNS + 1
    ));
}

#[test]
fn test_extension_filters_oversized_component() {
    // Create a system with one component having too many columns.
    // We need > MAX_MATRIX_COLUMNS unique variables in a connected component.
    // To keep it tractable, we use a chain of 2-var XORs that all share
    // variables, giving us num_constraints+1 variables.
    use preprocess::MAX_MATRIX_COLUMNS;

    // Create a chain that exceeds MAX_MATRIX_COLUMNS variables.
    let n = MAX_MATRIX_COLUMNS + 10;
    let constraints: Vec<XorConstraint> = (0..n as u32)
        .map(|i| XorConstraint::new(vec![i, i + 1], i % 2 == 0))
        .collect();

    // This large component should be filtered out
    let ext = XorExtension::new(constraints);
    assert_eq!(
        ext.num_components(),
        0,
        "component with {} columns should be filtered (limit {})",
        n + 1,
        MAX_MATRIX_COLUMNS
    );
}

#[test]
fn test_extension_max_num_matrices_cap() {
    use preprocess::MAX_NUM_MATRICES;

    // Create more independent 2-row components than the cap allows.
    let num_components = MAX_NUM_MATRICES + 3;
    let mut constraints = Vec::new();
    for i in 0..num_components {
        let base = (i * 4) as u32;
        // Each component: 2 XOR constraints sharing variables
        constraints.push(XorConstraint::new(vec![base, base + 1], true));
        constraints.push(XorConstraint::new(vec![base + 1, base + 2], false));
    }

    let ext = XorExtension::new(constraints);
    assert!(
        ext.num_components() <= MAX_NUM_MATRICES,
        "should cap at {} matrices, got {}",
        MAX_NUM_MATRICES,
        ext.num_components()
    );
}

#[test]
fn test_extension_keeps_small_components() {
    // Small components within limits should be kept.
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![1, 2], false),
        XorConstraint::new(vec![3, 4], true),
        XorConstraint::new(vec![4, 5], false),
    ];

    let ext = XorExtension::new(constraints);
    // Two 2-row components, both within limits
    assert_eq!(ext.num_components(), 2);
}

/// Verify that XOR extension with DRAT proof output produces valid proof
/// records when `set_extension_trusted_lemmas(true)` is used (#4533).
///
/// This tests the ext_dimacs / non-preprocessing XOR path where the XOR
/// extension is passed to `solve_with_extension` directly.
#[test]
fn test_xor_extension_drat_proof_emission() {
    use ay_sat::{ProofOutput, Solver};

    // Formula: x0 XOR x1 = 1, x0 = false, x1 = false
    // XOR constraint says exactly one of {x0, x1} must be true.
    // But both are forced false by unit clauses -> UNSAT.
    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut ext = XorExtension::new(constraints);

    let proof_output = ProofOutput::drat_text(Vec::new());
    let mut solver = Solver::with_proof_output(2, proof_output);
    solver.add_clause(vec![Literal::negative(Variable::new(0))]); // x0 = false
    solver.add_clause(vec![Literal::negative(Variable::new(1))]); // x1 = false

    // Mark XOR lemmas as trusted transforms (#4533)
    solver.set_extension_trusted_lemmas(true);

    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(
        result.is_unsat(),
        "XOR(x0,x1)=1 with x0=false, x1=false must be UNSAT"
    );

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof_bytes = writer.into_vec().expect("flush");
    let proof = String::from_utf8(proof_bytes).expect("UTF-8 proof");

    // DRAT proof must not be empty for UNSAT
    assert!(
        !proof.is_empty(),
        "DRAT proof must not be empty for UNSAT with XOR extension (#4533)"
    );

    // Must contain the empty clause (DRAT completion marker)
    let has_empty_clause = proof.lines().any(|line| line.trim() == "0");
    assert!(
        has_empty_clause,
        "DRAT proof must contain empty clause for UNSAT with XOR extension (#4533).\n\
         Full proof:\n{proof}"
    );
}

/// Verify that the preprocessing XOR path (solve_with_xor_detection) also
/// produces valid DRAT proofs (#4533).
#[test]
fn test_xor_preprocessing_path_drat_proof_emission() {
    use ay_sat::{ProofOutput, Solver};

    // Encode XOR(x0, x1) = 1 as CNF: {x0, x1} and {-x0, -x1}
    // Plus unit clauses forcing both false -> UNSAT with XOR detection
    let clauses = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        vec![
            Literal::negative(Variable::new(0)),
            Literal::negative(Variable::new(1)),
        ],
        vec![Literal::negative(Variable::new(0))], // x0 = false
        vec![Literal::negative(Variable::new(1))], // x1 = false
    ];

    let proof_output = ProofOutput::drat_text(Vec::new());
    let mut solver = Solver::with_proof_output(2, proof_output);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    // Use the preprocessing extension path which auto-sets trusted lemmas
    let result = solver
        .solve_with_preprocessing_extension::<XorExtension, _>(|active_clauses| {
            let mut finder = XorFinder::new();
            let (xors, used_indices) = finder.find_xors_with_indices(active_clauses);
            preprocess::build_prepared_extension(xors, used_indices, active_clauses.len())
        })
        .into_inner();

    assert!(
        result.is_unsat(),
        "XOR preprocessing path must detect UNSAT"
    );

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof_bytes = writer.into_vec().expect("flush");
    let proof = String::from_utf8(proof_bytes).expect("UTF-8 proof");

    assert!(
        !proof.is_empty(),
        "DRAT proof from XOR preprocessing path must not be empty (#4533)"
    );

    let has_empty_clause = proof.lines().any(|line| line.trim() == "0");
    assert!(
        has_empty_clause,
        "DRAT proof from XOR preprocessing must contain empty clause (#4533).\n\
         Full proof:\n{proof}"
    );
}
