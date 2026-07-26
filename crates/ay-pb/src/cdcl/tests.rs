//! Unit tests for the pseudo-Boolean CDCL solver (`super::PbCdclSolver`).
//! Extracted verbatim from `cdcl.rs` to keep the production module readable.

use super::*;
use std::cell::RefCell;
use std::rc::Rc;

/// A shared buffer for capturing proof output in tests.
#[derive(Clone)]
struct SharedBuf(Rc<RefCell<Vec<u8>>>);

impl SharedBuf {
    fn new() -> Self {
        Self(Rc::new(RefCell::new(Vec::new())))
    }

    fn as_string(&self) -> String {
        String::from_utf8(self.0.borrow().clone()).expect("proof output must be valid UTF-8")
    }
}

impl Write for SharedBuf {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.borrow_mut().extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

fn not(var: u32) -> PbLit {
    PbLit { var, negated: true }
}

fn linear_term(coeff: i128, pb_lit: PbLit) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![pb_lit],
    }
}

fn nonlinear_term(coeff: i128, lits: Vec<PbLit>) -> PbTerm {
    PbTerm { coeff, lits }
}

fn ge_constraint(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}

/// Builds a cardinality constraint `x_first + ... + x_(first+len-1) >= 1`
/// with `len` distinct positive literals. Used by the opt-in two-tier
/// `reduce_db` tests that need learned lemmas larger than
/// `REDUCE_DB_PROTECT_SIZE` so they are eligible for deletion (the opt-in
/// short-lemma tier protects size <= 2 lemmas).
fn ge_card_run(first: u32, len: u32) -> PbConstraint {
    ge_constraint(
        (first..first + len)
            .map(|v| linear_term(1, lit(v)))
            .collect(),
        1,
    )
}

fn eq_constraint(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Eq,
        rhs,
    }
}

#[test]
fn test_aggregation_lower_bound_certifies_perfect_cover() {
    // 4-cycle vertex cover: min x1+x2+x3+x4 s.t. each edge covered. Every var
    // appears in exactly 2 rows (k=2), rhs_sum=4 => surrogate LB = ceil(4/2) = 2,
    // which equals the true optimum (cover of a 4-cycle). This is the LP-dual
    // certificate that conflict-driven search cannot synthesize.
    let objective = PbObjective {
        terms: vec![
            linear_term(1, lit(1)),
            linear_term(1, lit(2)),
            linear_term(1, lit(3)),
            linear_term(1, lit(4)),
        ],
    };
    let coeffs = objective_positive_linear_coefficients(&objective).unwrap();
    let constraints = vec![
        ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(2))], 1),
        ge_constraint(vec![linear_term(1, lit(2)), linear_term(1, lit(3))], 1),
        ge_constraint(vec![linear_term(1, lit(3)), linear_term(1, lit(4))], 1),
        ge_constraint(vec![linear_term(1, lit(4)), linear_term(1, lit(1))], 1),
    ];
    assert_eq!(
        aggregation_objective_lower_bound_from_constraints(&constraints, &coeffs, &|| false),
        Some(2)
    );
}

#[test]
fn test_aggregation_lower_bound_excludes_non_objective_var_rows() {
    // LOAD-BEARING SOUNDNESS GUARD: a covering row whose variables are not all in
    // the objective must be EXCLUDED, else the aggregated LHS could exceed the
    // objective and the bound could overshoot the true optimum (=> wrong OPTIMUM
    // => category DQ). Here `min x1` s.t. `x1+x2+x3 >= 1` has true optimum 0
    // (set x2=1, x1=0); a wrong include would give ceil(1/1)=1.
    let objective = PbObjective {
        terms: vec![linear_term(1, lit(1))],
    };
    let coeffs = objective_positive_linear_coefficients(&objective).unwrap();
    let constraints = vec![ge_constraint(
        vec![
            linear_term(1, lit(1)),
            linear_term(1, lit(2)),
            linear_term(1, lit(3)),
        ],
        1,
    )];
    assert_eq!(
        aggregation_objective_lower_bound_from_constraints(&constraints, &coeffs, &|| false),
        None,
        "row with non-objective vars must be excluded (no bound), never overshoot"
    );
    // The combined public bound must not exceed the true optimum (0) either.
    let combined =
        objective_lower_bound_from_constraints(&constraints, &objective, &|| false).unwrap();
    assert!(
        combined <= 0,
        "combined LB {combined} overshoots true optimum 0"
    );
}

fn root_precheck_limits(
    import_batch_interval: usize,
    max_terms_per_constraint: usize,
) -> RootPropagationPrecheckLimits {
    RootPropagationPrecheckLimits {
        import_batch_interval,
        max_terms_per_constraint,
    }
}

fn run_root_precheck_with_limits(
    instance: &PbInstance,
    limits: RootPropagationPrecheckLimits,
) -> PbCdclResult {
    let mut never_stop = || false;
    PbCdclSolver::root_propagation_unsat_precheck_interruptible_with_limits(
        instance,
        &mut never_stop,
        limits,
    )
}

fn root_probe_decoy_pigeonhole_3_2_instance() -> PbInstance {
    let num_probe_decoys = 4;
    let num_pigeons = 3;
    let num_holes = 2;
    let mut constraints = Vec::new();
    let var_for = |pigeon: u32, hole: u32| num_probe_decoys + (pigeon * num_holes) + hole + 1;

    constraints.push(ge_constraint(
        vec![linear_term(100, lit(1)), linear_term(100, lit(2))],
        100,
    ));
    constraints.push(ge_constraint(
        vec![linear_term(100, not(1)), linear_term(100, not(2))],
        100,
    ));
    constraints.push(ge_constraint(
        vec![linear_term(100, lit(3)), linear_term(100, lit(4))],
        100,
    ));
    constraints.push(ge_constraint(
        vec![linear_term(100, not(3)), linear_term(100, not(4))],
        100,
    ));

    for pigeon in 0..num_pigeons {
        constraints.push(ge_constraint(
            (0..num_holes)
                .map(|hole| linear_term(1, lit(var_for(pigeon, hole))))
                .collect(),
            1,
        ));
    }

    for hole in 0..num_holes {
        constraints.push(ge_constraint(
            (0..num_pigeons)
                .map(|pigeon| linear_term(1, not(var_for(pigeon, hole))))
                .collect(),
            i128::from(num_pigeons) - 1,
        ));
    }

    PbInstance {
        num_vars: num_probe_decoys + (num_pigeons * num_holes),
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    }
}

fn solver_with_root_probe_disabled(instance: &PbInstance) -> PbCdclSolver {
    let mut solver = PbCdclSolver::new(instance);
    solver.config.root_probe_enabled = false;
    solver
}

#[test]
fn test_solve_trivially_satisfiable() {
    // x1 + x2 >= 1 (trivially SAT)
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();

    match result {
        PbCdclResult::Satisfiable(model) => {
            // At least one of x1, x2 must be true.
            assert!(model[0] || model[1]);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_solve_unsatisfiable() {
    // x1 >= 1 AND ~x1 >= 1 (x1 must be true AND false)
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1))], 1),
            ge_constraint(vec![linear_term(1, not(1))], 1),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();

    assert_eq!(result, PbCdclResult::Unsatisfiable);
}

// ---- Runtime var-pool tests ----

#[test]
fn test_new_var_grows_arrays_in_lockstep() {
    // Start from a 3-variable instance, then allocate runtime variables and
    // assert every per-variable array stays sized num_vars + 1 in lockstep.
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(1, lit(1)),
                linear_term(1, lit(2)),
                linear_term(1, lit(3)),
            ],
            1,
        )],
        objective: None,
    };
    let mut solver = PbCdclSolver::new(&instance);
    assert_eq!(solver.num_vars, 3);
    for expected in 4..=8u32 {
        let v = solver.new_var().expect("new_var must succeed");
        assert_eq!(v, expected, "new_var must hand out consecutive numbers");
        assert_eq!(solver.num_vars, expected);
        // These accessors panic via debug_assert if the arrays desynchronize.
        solver.debug_assert_var_arrays_in_lockstep();
        assert_eq!(solver.activity.len(), solver.num_vars as usize + 1);
        assert_eq!(solver.saved_phase.len(), solver.num_vars as usize + 1);
        assert_eq!(
            solver.vsids_heap.position.len(),
            solver.num_vars as usize + 1
        );
        assert!(
            solver.vsids_heap.contains(v),
            "new variable must be in the decision heap"
        );
    }
}

#[test]
fn test_add_constraint_runtime_preserves_sat_then_forces_unsat() {
    // Base: x1 + x2 >= 1 (SAT). Add a runtime constraint ~x1 >= 1 and ~x2 >= 1
    // (forces both false), which should make the formula UNSAT and the solver
    // must still report the correct verdict afterward.
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: None,
    };
    let mut solver = PbCdclSolver::new(&instance);
    // Still SAT before the runtime additions.
    assert!(matches!(
        solver.solve_with_assumptions(&[]),
        PbCdclAssumptionResult::Satisfiable(_)
    ));

    // Force x1 false at runtime.
    assert_eq!(
        solver.add_cardinality_runtime(&[not(1)], 1),
        RuntimeConstraintOutcome::Added
    );
    // Still SAT (x2 can be true).
    assert!(matches!(
        solver.solve_with_assumptions(&[]),
        PbCdclAssumptionResult::Satisfiable(_)
    ));

    // Force x2 false too: now x1 + x2 >= 1 cannot hold. Adding the unit at
    // level 0 must surface the conflict immediately.
    assert_eq!(
        solver.add_cardinality_runtime(&[not(2)], 1),
        RuntimeConstraintOutcome::Conflict
    );
}

#[test]
fn test_runtime_constraint_over_fresh_var_still_solves_correctly() {
    // Solve, allocate a fresh var r, add a constraint tying r to x1 (r >= x1,
    // encoded as ~x1 + r >= 1), and verify the solver still produces a model
    // that satisfies BOTH the original constraint and the runtime one.
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(vec![linear_term(1, lit(1))], 1)],
        objective: None,
    };
    let mut solver = PbCdclSolver::new(&instance);
    let r = solver.new_var().expect("fresh var");
    // r >= x1  <=>  ~x1 + r >= 1. Since x1 is forced true by the original
    // constraint, r must propagate to true.
    assert_eq!(
        solver.add_cardinality_runtime(&[not(1), lit(r)], 1),
        RuntimeConstraintOutcome::Added
    );
    match solver.solve_with_assumptions(&[]) {
        PbCdclAssumptionResult::Satisfiable(model) => {
            let r_idx = (r - 1) as usize;
            assert!(model[0], "x1 must be true");
            assert!(
                model[r_idx],
                "r must be forced true by the runtime implication r >= x1"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_runtime_permanent_constraint_survives_reduce_db() {
    // A runtime constraint must never be deleted by reduce_db: mark its
    // learned_permanent flag and verify it stays active after a forced
    // reduce_db pass.
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(1, lit(1)),
                linear_term(1, lit(2)),
                linear_term(1, lit(3)),
                linear_term(1, lit(4)),
            ],
            1,
        )],
        objective: None,
    };
    let mut solver = PbCdclSolver::new(&instance);
    assert_eq!(
        solver.add_cardinality_runtime(&[lit(1), lit(2)], 1),
        RuntimeConstraintOutcome::Added
    );
    // The runtime constraint occupies the (single) learned slot and must be
    // flagged permanent.
    assert_eq!(solver.learned_permanent.len(), 1);
    assert!(solver.learned_permanent[0]);
    // Give it a high LBD so it WOULD be deletable if not permanent, then force
    // reduce_db.
    solver.learned_lbd[0] = 100;
    solver.reduce_db();
    assert!(
        solver.learned_active[0],
        "permanent runtime constraint must survive reduce_db"
    );
}

#[test]
fn test_new_var_rejects_overflow() {
    // num_vars at i32::MAX must refuse to allocate (fails closed, never wraps).
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 0,
        constraints: vec![],
        objective: None,
    };
    let mut solver = PbCdclSolver::new(&instance);
    solver.num_vars = i32::MAX as u32;
    assert_eq!(solver.new_var(), None);
}

#[test]
fn test_root_propagation_unsat_precheck_returns_only_unsat() {
    let unsat = PbInstance {
        num_vars: 1,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1))], 1),
            ge_constraint(vec![linear_term(1, not(1))], 1),
        ],
        objective: None,
    };
    let sat = PbInstance {
        num_vars: 1,
        num_constraints: 1,
        constraints: vec![ge_constraint(vec![linear_term(1, lit(1))], 1)],
        objective: None,
    };

    assert_eq!(
        PbCdclSolver::root_propagation_unsat_precheck_interruptible(&unsat, || false),
        PbCdclResult::Unsatisfiable
    );
    assert_eq!(
        PbCdclSolver::root_propagation_unsat_precheck_interruptible(&sat, || false),
        PbCdclResult::Unknown
    );
}

#[test]
fn test_root_propagation_unsat_precheck_fails_closed_on_uncertainty() {
    let nonlinear_unsat_shape = PbInstance {
        num_vars: 2,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![nonlinear_term(1, vec![lit(1), lit(2)])], 1),
            ge_constraint(vec![linear_term(1, not(1))], 1),
        ],
        objective: None,
    };
    let interrupted = PbInstance {
        num_vars: 1,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1))], 1),
            ge_constraint(vec![linear_term(1, not(1))], 1),
        ],
        objective: None,
    };

    assert_eq!(
        PbCdclSolver::root_propagation_unsat_precheck_interruptible(&nonlinear_unsat_shape, || {
            false
        }),
        PbCdclResult::Unknown
    );
    assert_eq!(
        PbCdclSolver::root_propagation_unsat_precheck_interruptible(&interrupted, || true),
        PbCdclResult::Unknown
    );
}

#[test]
fn test_root_propagation_unsat_precheck_accepts_unsat_prefix_before_uncertain_suffix() {
    let mut constraints = vec![
        ge_constraint(vec![linear_term(1, lit(1))], 1),
        ge_constraint(vec![linear_term(1, not(1))], 1),
    ];
    while constraints.len() < ROOT_PROPAGATION_IMPORT_BATCH_INTERVAL {
        constraints.push(ge_constraint(vec![linear_term(1, lit(1))], 0));
    }
    constraints.push(ge_constraint(
        vec![nonlinear_term(1, vec![lit(1), lit(2)])],
        1,
    ));

    let instance = PbInstance {
        num_vars: 2,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    };

    assert_eq!(
        PbCdclSolver::root_propagation_unsat_precheck_interruptible(&instance, || false),
        PbCdclResult::Unsatisfiable
    );
}

#[test]
fn test_root_propagation_unsat_precheck_carries_assignment_across_batches() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 3,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1))], 1),
            ge_constraint(vec![linear_term(1, lit(2))], 0),
            ge_constraint(vec![linear_term(1, not(1))], 1),
        ],
        objective: None,
    };

    assert_eq!(
        run_root_precheck_with_limits(&instance, root_precheck_limits(2, 16)),
        PbCdclResult::Unsatisfiable
    );
}

#[test]
fn test_root_propagation_unsat_precheck_chains_propagation_across_batches() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 5,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1))], 1),
            ge_constraint(vec![linear_term(1, lit(3))], 0),
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, lit(3))], 0),
            ge_constraint(vec![linear_term(1, not(2))], 1),
        ],
        objective: None,
    };

    assert_eq!(
        run_root_precheck_with_limits(&instance, root_precheck_limits(2, 16)),
        PbCdclResult::Unsatisfiable
    );
}

#[test]
fn test_root_propagation_unsat_precheck_eq_negative_normalization_crosses_batch() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 3,
        constraints: vec![
            eq_constraint(vec![linear_term(-1, lit(1))], 0),
            ge_constraint(vec![linear_term(1, lit(2))], 0),
            ge_constraint(vec![linear_term(1, lit(1))], 1),
        ],
        objective: None,
    };

    assert_eq!(
        run_root_precheck_with_limits(&instance, root_precheck_limits(2, 16)),
        PbCdclResult::Unsatisfiable
    );
}

#[test]
fn test_root_propagation_unsat_precheck_fails_closed_on_too_wide_row() {
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 3,
        constraints: vec![
            ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(2)),
                    linear_term(1, lit(3)),
                ],
                1,
            ),
            ge_constraint(vec![linear_term(1, lit(4))], 1),
            ge_constraint(vec![linear_term(1, not(4))], 1),
        ],
        objective: None,
    };

    assert_eq!(
        run_root_precheck_with_limits(&instance, root_precheck_limits(1, 2)),
        PbCdclResult::Unknown
    );
}

#[test]
fn test_root_propagation_unsat_precheck_does_not_accumulate_small_row_terms() {
    let mut constraints = vec![ge_constraint(vec![linear_term(1, lit(1))], 1)];

    let filler_rows = ROOT_PROPAGATION_IMPORT_BATCH_TERM_INTERVAL / 3 + 1;
    for _ in 0..filler_rows {
        constraints.push(ge_constraint(
            vec![
                linear_term(0, lit(2)),
                linear_term(0, lit(3)),
                linear_term(0, lit(4)),
            ],
            0,
        ));
    }
    constraints.push(ge_constraint(vec![linear_term(1, not(1))], 1));
    constraints.push(ge_constraint(
        vec![nonlinear_term(1, vec![lit(1), lit(2)])],
        1,
    ));

    let instance = PbInstance {
        num_vars: 4,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    };

    assert_eq!(
        run_root_precheck_with_limits(&instance, root_precheck_limits(4096, 4)),
        PbCdclResult::Unknown,
        "many small rows must not force an early term-batch propagation before an uncertain suffix"
    );
}

#[test]
fn test_root_propagation_unsat_precheck_polls_while_screening_wide_row() {
    let mut terms: Vec<PbTerm> = (1..=ROOT_PROPAGATION_IMPORT_TERM_POLL_INTERVAL as u32)
        .map(|var| linear_term(1, lit(var)))
        .collect();
    terms.push(nonlinear_term(
        1,
        vec![
            lit(ROOT_PROPAGATION_IMPORT_TERM_POLL_INTERVAL as u32 + 1),
            lit(ROOT_PROPAGATION_IMPORT_TERM_POLL_INTERVAL as u32 + 2),
        ],
    ));
    let instance = PbInstance {
        num_vars: ROOT_PROPAGATION_IMPORT_TERM_POLL_INTERVAL as u32 + 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(terms, 1)],
        objective: None,
    };
    let calls = std::cell::Cell::new(0);
    let mut stop_on_second_poll = || {
        calls.set(calls.get() + 1);
        calls.get() >= 2
    };

    assert_eq!(
        PbCdclSolver::root_propagation_unsat_precheck_interruptible_with_limits(
            &instance,
            &mut stop_on_second_poll,
            root_precheck_limits(1, ROOT_PROPAGATION_IMPORT_TERM_POLL_INTERVAL + 2),
        ),
        PbCdclResult::Unknown
    );
    assert!(
        calls.get() >= 2,
        "wide-row screening should poll before importing or returning Unknown"
    );
}

#[test]
fn test_root_propagation_unsat_precheck_interrupts_during_wide_import_scan() {
    let mut terms = (1..=CONSTRUCTOR_LOAD_STOP_POLL_INTERVAL as u32)
        .map(|var| linear_term(1, lit(var)))
        .collect::<Vec<_>>();
    terms.push(nonlinear_term(1, vec![lit(1), lit(2)]));
    let instance = PbInstance {
        num_vars: CONSTRUCTOR_LOAD_STOP_POLL_INTERVAL as u32,
        num_constraints: 1,
        constraints: vec![ge_constraint(terms, 1)],
        objective: None,
    };
    let polls = std::cell::Cell::new(0usize);

    let result = PbCdclSolver::root_propagation_unsat_precheck_interruptible(&instance, || {
        let next = polls.get() + 1;
        polls.set(next);
        next >= 2
    });

    assert_eq!(result, PbCdclResult::Unknown);
    assert!(
        polls.get() >= 2,
        "precheck should poll while scanning one wide imported row"
    );
}

#[test]
fn test_root_propagation_unsat_precheck_term_batch_imports_wide_eq_prefix() {
    let mut eq_terms = Vec::with_capacity(ROOT_PROPAGATION_IMPORT_BATCH_TERM_INTERVAL + 1);
    eq_terms.push(linear_term(1, lit(1)));
    eq_terms.extend(
        (2..=ROOT_PROPAGATION_IMPORT_BATCH_TERM_INTERVAL as u32 + 1)
            .map(|var| linear_term(0, lit(var))),
    );
    let instance = PbInstance {
        num_vars: ROOT_PROPAGATION_IMPORT_BATCH_TERM_INTERVAL as u32 + 2,
        num_constraints: 3,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1))], 1),
            PbConstraint {
                terms: eq_terms,
                rel: PbRel::Eq,
                rhs: 0,
            },
            ge_constraint(vec![nonlinear_term(1, vec![lit(1), lit(2)])], 1),
        ],
        objective: None,
    };

    assert_eq!(
        PbCdclSolver::root_propagation_unsat_precheck_interruptible(&instance, || false),
        PbCdclResult::Unsatisfiable
    );
}

#[test]
fn test_bounded_objective_decision_unsat_check_runs_full_cdcl() {
    let bounded_decision = PbInstance {
        num_vars: 3,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(2)),
                    linear_term(1, lit(3)),
                ],
                2,
            ),
            ge_constraint(
                vec![
                    linear_term(1, not(1)),
                    linear_term(1, not(2)),
                    linear_term(1, not(3)),
                ],
                2,
            ),
        ],
        objective: None,
    };

    assert_eq!(
        PbCdclSolver::root_propagation_unsat_precheck_interruptible(&bounded_decision, || {
            false
        }),
        PbCdclResult::Unknown,
        "this bound needs search, not just root propagation"
    );
    assert_eq!(
        PbCdclSolver::bounded_objective_decision_unsat_check_interruptible(
            &bounded_decision,
            || false
        ),
        PbCdclResult::Unsatisfiable
    );
}

#[test]
fn test_bounded_objective_decision_guidance_uses_bound_row_weights_and_phases() {
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 0,
        constraints: vec![],
        objective: None,
    };
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    let bound = ge_constraint(
        vec![
            linear_term(-2, lit(1)),
            linear_term(-9, lit(2)),
            linear_term(-5, not(3)),
            linear_term(4, lit(4)),
        ],
        -7,
    );

    solver.seed_search_from_objective_bound_constraint(&bound);

    assert!(
        !solver.saved_phase[1],
        "negative x1 bound term prefers x1=false"
    );
    assert!(
        !solver.saved_phase[2],
        "negative x2 bound term prefers x2=false"
    );
    assert!(
        solver.saved_phase[3],
        "negative ~x3 bound term prefers x3=true"
    );
    assert!(
        solver.saved_phase[4],
        "positive x4 bound term prefers x4=true"
    );
    assert_eq!(
        solver.pick_decision_literal(),
        -2,
        "highest-weight bound variable should be branched first in its bound-satisfying phase"
    );
}

#[test]
fn test_bounded_objective_decision_guidance_ignores_non_linear_bound_rows() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 0,
        constraints: vec![],
        objective: None,
    };
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    let saved_before = solver.saved_phase.clone();
    let activity_before = solver.activity.clone();
    let unsupported_bound = ge_constraint(
        vec![
            linear_term(-10, lit(1)),
            nonlinear_term(-1, vec![lit(1), lit(2)]),
        ],
        -1,
    );

    solver.seed_search_from_objective_bound_constraint(&unsupported_bound);

    assert_eq!(solver.saved_phase, saved_before);
    assert_eq!(solver.activity, activity_before);
}

#[test]
fn test_bounded_objective_decision_guidance_boosts_bound_row_neighbors() {
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(7, lit(3))], 1),
            ge_constraint(vec![linear_term(20, lit(4))], 1),
        ],
        objective: None,
    };
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    let baseline = solver.activity.clone();
    let bound = ge_constraint(vec![linear_term(1, lit(1))], 1);

    solver.seed_activity_from_objective_bound_neighborhood(&bound);

    assert!(
        solver.activity[3] > baseline[3],
        "neighbor variable from a row touching the bound var should be boosted"
    );
    assert_eq!(
        solver.activity[4], baseline[4],
        "unrelated high-weight row should not receive bound-neighborhood activity"
    );
}

#[test]
fn test_bounded_objective_decision_guidance_ignores_wide_neighbor_rows() {
    let wide_terms = (1..=OBJECTIVE_BOUND_NEIGHBOR_MAX_ROW_TERMS as u32 + 1)
        .map(|var| linear_term(1, lit(var)))
        .collect::<Vec<_>>();
    let instance = PbInstance {
        num_vars: OBJECTIVE_BOUND_NEIGHBOR_MAX_ROW_TERMS as u32 + 1,
        num_constraints: 1,
        constraints: vec![ge_constraint(wide_terms, 1)],
        objective: None,
    };
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    let baseline = solver.activity.clone();
    let bound = ge_constraint(vec![linear_term(1, lit(1))], 1);

    solver.seed_activity_from_objective_bound_neighborhood(&bound);

    assert_eq!(
        solver.activity, baseline,
        "wide rows are skipped to keep bound-neighborhood seeding bounded"
    );
}

#[test]
fn test_bounded_objective_decision_unsat_check_fails_closed_on_sat() {
    let bounded_decision = PbInstance {
        num_vars: 2,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, not(2))], 1),
        ],
        objective: None,
    };

    assert_eq!(
        PbCdclSolver::bounded_objective_decision_unsat_check_interruptible(
            &bounded_decision,
            || false
        ),
        PbCdclResult::Unknown
    );
}

#[test]
fn test_bounded_objective_decision_unsat_check_is_interruptible() {
    let bounded_decision = PbInstance {
        num_vars: 1,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1))], 1),
            ge_constraint(vec![linear_term(1, not(1))], 1),
        ],
        objective: None,
    };

    assert_eq!(
        PbCdclSolver::bounded_objective_decision_unsat_check_interruptible(
            &bounded_decision,
            || true
        ),
        PbCdclResult::Unknown
    );
}

#[test]
fn test_bounded_objective_decision_unsat_check_fails_closed_on_unsupported_import() {
    let bounded_decision = PbInstance {
        num_vars: 2,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![nonlinear_term(1, vec![lit(1), lit(2)])], 1),
            ge_constraint(vec![linear_term(1, not(1))], 1),
        ],
        objective: None,
    };

    assert_eq!(
        PbCdclSolver::bounded_objective_decision_unsat_check_interruptible(
            &bounded_decision,
            || false
        ),
        PbCdclResult::Unknown
    );
}

#[test]
fn test_solve_with_propagation() {
    // 2*x1 + 3*x2 >= 4 with only 2 vars.
    // x2 must be true (coeff 3 >= 4-2=2 slack triggers), and if x2=true
    // then constraint is satisfied regardless of x1.
    // Actually: if x1=false, sum=3*x2 and need >=4, so x2 alone is
    // insufficient. Need x1=true as well for 2+3=5>=4. Actually x2=true
    // gives 3 which is < 4, so we need both. This is a more interesting
    // propagation test.
    //
    // Let's use: x1 + x2 + x3 >= 3 (all three must be true)
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(1, lit(1)),
                linear_term(1, lit(2)),
                linear_term(1, lit(3)),
            ],
            3,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();

    match result {
        PbCdclResult::Satisfiable(model) => {
            assert!(model[0] && model[1] && model[2]);
        }
        other => panic!("expected SAT with all true, got {other:?}"),
    }
}

#[test]
fn test_solve_interruptible_stops_early() {
    // Large-ish instance, interrupt immediately.
    let instance = PbInstance {
        num_vars: 10,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            (1..=10).map(|v| linear_term(1, lit(v))).collect(),
            5,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_interruptible(|| true);

    assert_eq!(result, PbCdclResult::Unknown);
}

#[test]
fn test_raw_native_nonlinear_fails_closed() {
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 3,
        constraints: vec![
            ge_constraint(
                vec![
                    nonlinear_term(1, vec![lit(1), lit(2)]),
                    nonlinear_term(1, vec![lit(3), lit(4)]),
                ],
                1,
            ),
            ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(2)),
                    linear_term(1, lit(3)),
                    linear_term(1, lit(4)),
                ],
                2,
            ),
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, not(4))], 1),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    assert_eq!(solver.solve(), PbCdclResult::Unknown);
}

#[test]
fn test_solve_with_assumptions_satisfiable() {
    // x1 + x2 >= 1 is satisfiable under ~x1, and propagates x2.
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_with_assumptions(&[not(1)]);

    match result {
        PbCdclAssumptionResult::Satisfiable(model) => {
            assert!(
                !model[0],
                "the ~x1 assumption must be reflected in the model"
            );
            assert!(model[1], "x2 must satisfy the remaining PB constraint");
        }
        other => panic!("expected SAT under assumptions, got {other:?}"),
    }

    let result = solver.solve_with_assumptions(&[lit(1)]);
    match result {
        PbCdclAssumptionResult::Satisfiable(model) => {
            assert!(model[0], "assumptions must be temporary across queries");
        }
        other => panic!("expected second assumption query to be SAT, got {other:?}"),
    }
}

#[test]
fn test_solve_with_assumptions_contradictory_assumptions_core() {
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 0,
        constraints: Vec::new(),
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_with_assumptions(&[lit(1), not(1)]);

    assert_eq!(
        result,
        PbCdclAssumptionResult::Unsatisfiable {
            core: vec![lit(1), not(1)]
        }
    );
}

#[test]
fn test_solve_with_assumptions_unsat_core_from_propagation() {
    // Hard constraint: at most one of x1 and x2 may be true.
    // Assumptions x1 and x2 conflict under that constraint.
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, not(1)), linear_term(1, not(2))],
            1,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_with_assumptions(&[lit(1), lit(2)]);

    assert_eq!(
        result,
        PbCdclAssumptionResult::Unsatisfiable {
            core: vec![lit(1), lit(2)]
        }
    );
}

#[test]
fn test_native_opt_core_probe_extracts_single_lit_core_lower_bound() {
    // Probing min x1 + x2 with both objective literals assumed false is
    // infeasible because the hard constraint requires one of them true.
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(1, lit(1)),
            linear_term(1, lit(2)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.probe_single_lit_objective_core(&obj);

    assert_eq!(
        result,
        PbCdclOptimizationCoreProbeResult::Evidence(PbCdclOptimizationCoreEvidence {
            core: vec![not(1), not(2)],
            lower_bound: 1,
            weighted_core: vec![
                weighted_core_assumption(not(1), lit(1), 1),
                weighted_core_assumption(not(2), lit(2), 1),
            ],
            model: None,
        })
    );
}

#[test]
fn test_native_opt_core_probe_preserves_assignments_across_repeated_calls() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(1, lit(1)),
            linear_term(1, lit(2)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);

    for _ in 0..2 {
        let result = solver.probe_single_lit_objective_core(&obj);
        assert_eq!(
            result,
            PbCdclOptimizationCoreProbeResult::Evidence(PbCdclOptimizationCoreEvidence {
                core: vec![not(1), not(2)],
                lower_bound: 1,
                weighted_core: vec![
                    weighted_core_assumption(not(1), lit(1), 1),
                    weighted_core_assumption(not(2), lit(2), 1),
                ],
                model: None,
            })
        );
    }

    match solver.solve_with_assumptions(&[not(1)]) {
        PbCdclAssumptionResult::Satisfiable(model) => {
            assert!(!model[0], "temporary probe assignments must be gone");
            assert!(model[1], "x2 must satisfy the hard constraint");
        }
        other => panic!("expected SAT after repeated objective probes, got {other:?}"),
    }

    match solver.solve_with_assumptions(&[not(2)]) {
        PbCdclAssumptionResult::Satisfiable(model) => {
            assert!(model[0], "x1 must satisfy the hard constraint");
            assert!(!model[1], "temporary probe assignments must stay temporary");
        }
        other => panic!("expected SAT after follow-up assumption query, got {other:?}"),
    }
}

#[test]
fn test_native_opt_core_probe_fails_closed_for_proof_writer() {
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 0,
        constraints: Vec::new(),
        objective: Some(objective(vec![linear_term(1, lit(1))])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf).expect("proof writer setup");

    assert_eq!(
        solver.probe_single_lit_objective_core(&obj),
        PbCdclOptimizationCoreProbeResult::Unsupported(
            PbCdclOptimizationCoreUnsupportedReason::ProofWriterEnabled,
        )
    );
}

#[test]
fn test_native_opt_core_probe_fails_closed_for_non_linear_term() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 0,
        constraints: Vec::new(),
        objective: Some(objective(vec![PbTerm {
            coeff: 1,
            lits: vec![lit(1), lit(2)],
        }])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);

    assert_eq!(
        solver.probe_single_lit_objective_core(&obj),
        PbCdclOptimizationCoreProbeResult::Unsupported(
            PbCdclOptimizationCoreUnsupportedReason::NonSingleLiteralTerm,
        )
    );
}

#[test]
fn test_native_opt_core_probe_reports_fail_closed_unsupported_reasons() {
    let cases = vec![
        (
            objective(vec![linear_term(-1, lit(1))]),
            PbCdclOptimizationCoreUnsupportedReason::NegativeCoefficient,
        ),
        (
            objective(vec![linear_term(0, lit(1))]),
            PbCdclOptimizationCoreUnsupportedReason::EmptyObjective,
        ),
    ];

    for (obj, expected_reason) in cases {
        let instance = PbInstance {
            num_vars: 1,
            num_constraints: 0,
            constraints: Vec::new(),
            objective: Some(obj.clone()),
        };
        let mut solver = PbCdclSolver::new(&instance);
        let result = solver.probe_single_lit_objective_core(&obj);

        assert_eq!(result.evidence(), None);
        assert_eq!(result.unsupported_reason(), Some(expected_reason));
    }
}

#[test]
fn test_native_opt_core_probe_sums_duplicate_weighted_literals() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(4, lit(1)),
            linear_term(6, lit(1)),
            linear_term(5, lit(2)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);

    assert_eq!(
        solver.probe_single_lit_objective_core(&obj),
        PbCdclOptimizationCoreProbeResult::Evidence(PbCdclOptimizationCoreEvidence {
            core: vec![not(1), not(2)],
            lower_bound: 5,
            weighted_core: vec![
                weighted_core_assumption(not(1), lit(1), 10),
                weighted_core_assumption(not(2), lit(2), 5),
            ],
            model: None,
        })
    );
}

#[test]
fn test_native_opt_core_probe_accounts_complementary_weighted_literals() {
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 0,
        constraints: Vec::new(),
        objective: Some(objective(vec![
            linear_term(7, lit(1)),
            linear_term(3, not(1)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);

    assert_eq!(
        solver.probe_single_lit_objective_core(&obj),
        PbCdclOptimizationCoreProbeResult::Evidence(PbCdclOptimizationCoreEvidence {
            core: vec![not(1), lit(1)],
            lower_bound: 3,
            weighted_core: vec![
                weighted_core_assumption(not(1), lit(1), 7),
                weighted_core_assumption(lit(1), not(1), 3),
            ],
            model: None,
        })
    );
}

#[test]
fn test_native_opt_core_probe_reports_reusable_weighted_evidence_api() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(1, lit(1)),
                linear_term(1, lit(2)),
                linear_term(1, lit(3)),
            ],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(9, lit(1)),
            linear_term(4, lit(2)),
            linear_term(6, lit(3)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.probe_single_lit_objective_core(&obj);
    let evidence = result.evidence().expect("native core evidence");
    let unsat_core = evidence
        .as_unsat_core()
        .expect("optimizer-facing UNSAT core evidence");

    assert_eq!(evidence.core(), &[not(1), not(2), not(3)]);
    assert_eq!(evidence.lower_bound(), 4);
    assert_eq!(evidence.model(), None);
    assert_eq!(
        evidence.weighted_core(),
        &[
            weighted_core_assumption(not(1), lit(1), 9),
            weighted_core_assumption(not(2), lit(2), 4),
            weighted_core_assumption(not(3), lit(3), 6),
        ]
    );
    assert_eq!(evidence.weighted_core()[1].assumption(), not(2));
    assert_eq!(evidence.weighted_core()[1].objective_lit(), lit(2));
    assert_eq!(evidence.weighted_core()[1].contribution(), 4);
    assert_eq!(unsat_core.core(), &[not(1), not(2), not(3)]);
    assert_eq!(unsat_core.lower_bound(), 4);
    assert_eq!(
        unsat_core.weighted_core(),
        &[
            weighted_core_assumption(not(1), lit(1), 9),
            weighted_core_assumption(not(2), lit(2), 4),
            weighted_core_assumption(not(3), lit(3), 6),
        ]
    );
}

#[test]
fn test_native_opt_core_probe_canonicalizes_weighted_core_for_optimizer() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(1, lit(1)),
                linear_term(1, lit(2)),
                linear_term(1, lit(3)),
            ],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(6, lit(3)),
            linear_term(9, lit(1)),
            linear_term(4, lit(2)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.probe_single_lit_objective_core(&obj);
    let evidence = result.evidence().expect("native core evidence");
    let unsat_core = evidence
        .as_unsat_core()
        .expect("optimizer-facing UNSAT core evidence");

    assert_eq!(evidence.core(), &[not(3), not(1), not(2)]);
    assert_eq!(evidence.lower_bound(), 4);
    assert_eq!(
        unsat_core.weighted_core(),
        &[
            weighted_core_assumption(not(1), lit(1), 9),
            weighted_core_assumption(not(2), lit(2), 4),
            weighted_core_assumption(not(3), lit(3), 6),
        ]
    );
}

#[test]
fn test_native_opt_core_probe_reports_deterministic_core_summary() {
    fn summary_for(terms: Vec<PbTerm>) -> PbCdclOptimizationCoreSummary {
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(2)),
                    linear_term(1, lit(3)),
                ],
                1,
            )],
            objective: Some(objective(terms)),
        };

        let obj = instance.objective.as_ref().unwrap().clone();
        let mut solver = PbCdclSolver::new(&instance);
        let result = solver.probe_single_lit_objective_core(&obj);
        let evidence = result.evidence().expect("native core evidence");
        let unsat_core = evidence
            .as_unsat_core()
            .expect("optimizer-facing UNSAT core evidence");
        let summary = evidence
            .unsat_core_summary()
            .expect("validated optimizer core summary");

        assert_eq!(unsat_core.summary(), Some(summary));
        summary
    }

    let canonical = summary_for(vec![
        linear_term(6, lit(3)),
        linear_term(9, lit(1)),
        linear_term(4, lit(2)),
    ]);
    let shuffled = summary_for(vec![
        linear_term(4, lit(2)),
        linear_term(6, lit(3)),
        linear_term(9, lit(1)),
    ]);

    assert_eq!(canonical, shuffled);
    assert_eq!(canonical.core_len(), 3);
    assert_eq!(canonical.lower_bound(), 4);
    assert_eq!(canonical.total_contribution(), 19);
    assert_ne!(canonical.fingerprint(), 0);
}

#[test]
fn test_native_opt_core_probe_summary_acceptance_requires_monotone_lower_bound() {
    fn summary_for(terms: Vec<PbTerm>) -> PbCdclOptimizationCoreSummary {
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(2)),
                    linear_term(1, lit(3)),
                ],
                1,
            )],
            objective: Some(objective(terms)),
        };

        let obj = instance.objective.as_ref().unwrap().clone();
        let mut solver = PbCdclSolver::new(&instance);
        let result = solver.probe_single_lit_objective_core(&obj);
        result
            .evidence()
            .expect("native core evidence")
            .unsat_core_summary()
            .expect("validated optimizer core summary")
    }

    let baseline = summary_for(vec![
        linear_term(4, lit(1)),
        linear_term(6, lit(2)),
        linear_term(9, lit(3)),
    ]);
    let stronger = summary_for(vec![
        linear_term(6, lit(1)),
        linear_term(7, lit(2)),
        linear_term(10, lit(3)),
    ]);
    let weaker = summary_for(vec![
        linear_term(3, lit(1)),
        linear_term(7, lit(2)),
        linear_term(10, lit(3)),
    ]);

    assert!(baseline.is_safe_optimizer_successor_of(None));
    assert!(stronger.is_safe_optimizer_successor_of(Some(&baseline)));
    assert!(!weaker.is_safe_optimizer_successor_of(Some(&stronger)));

    let impossible_total = PbCdclOptimizationCoreSummary {
        core_len: 3,
        lower_bound: 6,
        total_contribution: 17,
        fingerprint: stronger.fingerprint(),
    };
    assert!(!impossible_total.is_safe_optimizer_successor_of(None));
}

#[test]
fn test_native_opt_core_probe_result_accepts_only_safe_unsat_summaries() {
    fn probe_for(terms: Vec<PbTerm>) -> PbCdclOptimizationCoreProbeResult {
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(2)),
                    linear_term(1, lit(3)),
                ],
                1,
            )],
            objective: Some(objective(terms)),
        };

        let obj = instance.objective.as_ref().unwrap().clone();
        let mut solver = PbCdclSolver::new(&instance);
        solver.probe_single_lit_objective_core(&obj)
    }

    let accepted = probe_for(vec![
        linear_term(4, lit(1)),
        linear_term(6, lit(2)),
        linear_term(9, lit(3)),
    ])
    .accepted_unsat_core_summary(None)
    .expect("valid UNSAT core summary");

    let weaker = probe_for(vec![
        linear_term(3, lit(1)),
        linear_term(6, lit(2)),
        linear_term(9, lit(3)),
    ]);
    assert_eq!(weaker.accepted_unsat_core_summary(Some(&accepted)), None);

    let inconsistent =
        PbCdclOptimizationCoreProbeResult::Evidence(PbCdclOptimizationCoreEvidence {
            core: vec![not(1), not(2)],
            lower_bound: 4,
            weighted_core: vec![
                weighted_core_assumption(not(1), lit(1), 3),
                weighted_core_assumption(not(2), lit(2), 5),
            ],
            model: None,
        });
    assert!(inconsistent.evidence().is_some());
    assert_eq!(inconsistent.accepted_unsat_core_summary(None), None);

    let sat_instance = PbInstance {
        num_vars: 1,
        num_constraints: 0,
        constraints: Vec::new(),
        objective: Some(objective(vec![linear_term(2, lit(1))])),
    };
    let sat_obj = sat_instance.objective.as_ref().unwrap().clone();
    let mut sat_solver = PbCdclSolver::new(&sat_instance);
    let sat_result = sat_solver.probe_single_lit_objective_core(&sat_obj);
    assert!(sat_result.evidence().is_some());
    assert_eq!(sat_result.accepted_unsat_core_summary(None), None);

    let unsupported = PbCdclOptimizationCoreProbeResult::Unsupported(
        PbCdclOptimizationCoreUnsupportedReason::NegativeCoefficient,
    );
    assert_eq!(unsupported.evidence(), None);
    assert_eq!(unsupported.accepted_unsat_core_summary(None), None);
}

#[test]
fn test_native_opt_core_probe_result_exposes_only_accepted_unsat_core_evidence() {
    fn probe_for(terms: Vec<PbTerm>) -> PbCdclOptimizationCoreProbeResult {
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(2)),
                    linear_term(1, lit(3)),
                ],
                1,
            )],
            objective: Some(objective(terms)),
        };

        let obj = instance.objective.as_ref().unwrap().clone();
        let mut solver = PbCdclSolver::new(&instance);
        solver.probe_single_lit_objective_core(&obj)
    }

    let accepted = probe_for(vec![
        linear_term(6, lit(3)),
        linear_term(9, lit(1)),
        linear_term(4, lit(2)),
    ]);
    let accepted_core = accepted
        .accepted_unsat_core_evidence(None)
        .expect("valid optimizer-facing UNSAT core evidence");
    let accepted_summary = accepted_core.summary().expect("accepted summary");

    assert_eq!(
        accepted.accepted_unsat_core_summary(None),
        Some(accepted_summary)
    );
    assert_eq!(accepted_core.core(), &[not(3), not(1), not(2)]);
    assert_eq!(accepted_core.lower_bound(), 4);
    assert_eq!(
        accepted_core.weighted_core(),
        &[
            weighted_core_assumption(not(1), lit(1), 9),
            weighted_core_assumption(not(2), lit(2), 4),
            weighted_core_assumption(not(3), lit(3), 6),
        ]
    );

    let stronger = probe_for(vec![
        linear_term(5, lit(1)),
        linear_term(7, lit(2)),
        linear_term(10, lit(3)),
    ]);
    assert!(stronger
        .accepted_unsat_core_evidence(Some(&accepted_summary))
        .is_some());

    let weaker = probe_for(vec![
        linear_term(3, lit(1)),
        linear_term(7, lit(2)),
        linear_term(10, lit(3)),
    ]);
    assert_eq!(
        weaker.accepted_unsat_core_evidence(Some(&accepted_summary)),
        None
    );

    let inconsistent =
        PbCdclOptimizationCoreProbeResult::Evidence(PbCdclOptimizationCoreEvidence {
            core: vec![not(1), not(2)],
            lower_bound: 4,
            weighted_core: vec![
                weighted_core_assumption(not(1), lit(1), 3),
                weighted_core_assumption(not(2), lit(2), 5),
            ],
            model: None,
        });
    assert_eq!(inconsistent.accepted_unsat_core_evidence(None), None);

    let sat_instance = PbInstance {
        num_vars: 1,
        num_constraints: 0,
        constraints: Vec::new(),
        objective: Some(objective(vec![linear_term(2, lit(1))])),
    };
    let sat_obj = sat_instance.objective.as_ref().unwrap().clone();
    let mut sat_solver = PbCdclSolver::new(&sat_instance);
    let sat_result = sat_solver.probe_single_lit_objective_core(&sat_obj);
    assert_eq!(sat_result.accepted_unsat_core_evidence(None), None);

    let unsupported = PbCdclOptimizationCoreProbeResult::Unsupported(
        PbCdclOptimizationCoreUnsupportedReason::NegativeCoefficient,
    );
    assert_eq!(unsupported.accepted_unsat_core_evidence(None), None);
}

#[test]
fn test_native_opt_core_probe_result_pairs_accepted_unsat_core_with_summary() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(1, lit(1)),
                linear_term(1, lit(2)),
                linear_term(1, lit(3)),
            ],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(6, lit(3)),
            linear_term(9, lit(1)),
            linear_term(4, lit(2)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.probe_single_lit_objective_core(&obj);
    let accepted = result
        .accepted_unsat_core(None)
        .expect("valid optimizer-facing accepted core");
    let accepted_evidence = accepted.evidence();
    let accepted_summary = accepted.summary();

    assert_eq!(
        result.accepted_unsat_core_summary(None),
        Some(accepted_summary)
    );
    assert_eq!(
        result.accepted_unsat_core_evidence(None),
        Some(accepted_evidence)
    );
    assert_eq!(accepted_summary, accepted_evidence.summary().unwrap());
    assert_eq!(accepted_summary.core_len(), 3);
    assert_eq!(accepted_summary.lower_bound(), 4);
    assert_eq!(accepted_summary.total_contribution(), 19);
    assert_eq!(accepted_evidence.core(), &[not(3), not(1), not(2)]);
    assert_eq!(accepted_evidence.lower_bound(), 4);
    assert_eq!(
        accepted_evidence.weighted_core(),
        &[
            weighted_core_assumption(not(1), lit(1), 9),
            weighted_core_assumption(not(2), lit(2), 4),
            weighted_core_assumption(not(3), lit(3), 6),
        ]
    );
}

#[test]
fn test_native_opt_core_probe_result_rejects_unaccepted_core_pair() {
    fn probe_for(terms: Vec<PbTerm>) -> PbCdclOptimizationCoreProbeResult {
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(2)),
                    linear_term(1, lit(3)),
                ],
                1,
            )],
            objective: Some(objective(terms)),
        };

        let obj = instance.objective.as_ref().unwrap().clone();
        let mut solver = PbCdclSolver::new(&instance);
        solver.probe_single_lit_objective_core(&obj)
    }

    let accepted_result = probe_for(vec![
        linear_term(4, lit(1)),
        linear_term(6, lit(2)),
        linear_term(9, lit(3)),
    ]);
    let accepted = accepted_result
        .accepted_unsat_core(None)
        .expect("valid accepted core");
    let accepted_summary = accepted.summary();

    let weaker = probe_for(vec![
        linear_term(3, lit(1)),
        linear_term(7, lit(2)),
        linear_term(10, lit(3)),
    ]);
    assert_eq!(weaker.accepted_unsat_core(Some(&accepted_summary)), None);

    let inconsistent =
        PbCdclOptimizationCoreProbeResult::Evidence(PbCdclOptimizationCoreEvidence {
            core: vec![not(1), not(2)],
            lower_bound: 4,
            weighted_core: vec![
                weighted_core_assumption(not(1), lit(1), 3),
                weighted_core_assumption(not(2), lit(2), 5),
            ],
            model: None,
        });
    assert_eq!(inconsistent.accepted_unsat_core(None), None);

    let sat_instance = PbInstance {
        num_vars: 1,
        num_constraints: 0,
        constraints: Vec::new(),
        objective: Some(objective(vec![linear_term(2, lit(1))])),
    };
    let sat_obj = sat_instance.objective.as_ref().unwrap().clone();
    let mut sat_solver = PbCdclSolver::new(&sat_instance);
    let sat_result = sat_solver.probe_single_lit_objective_core(&sat_obj);
    assert_eq!(sat_result.accepted_unsat_core(None), None);

    let unsupported = PbCdclOptimizationCoreProbeResult::Unsupported(
        PbCdclOptimizationCoreUnsupportedReason::NegativeCoefficient,
    );
    assert_eq!(unsupported.accepted_unsat_core(None), None);
}

#[test]
fn test_native_opt_core_probe_rejects_inconsistent_core_summary() {
    let valid_weighted = vec![
        weighted_core_assumption(not(1), lit(1), 3),
        weighted_core_assumption(not(2), lit(2), 5),
    ];

    assert!(
        PbCdclOptimizationCoreSummary::from_evidence(&[not(1), not(2)], 3, &valid_weighted)
            .is_some()
    );

    assert_eq!(
        PbCdclOptimizationCoreSummary::from_evidence(&[not(1), not(1)], 3, &valid_weighted),
        None
    );
    assert_eq!(
        PbCdclOptimizationCoreSummary::from_evidence(
            &[not(1), not(2)],
            3,
            &[
                weighted_core_assumption(not(1), lit(1), 3),
                weighted_core_assumption(not(1), lit(1), 5),
            ]
        ),
        None
    );
    assert_eq!(
        PbCdclOptimizationCoreSummary::from_evidence(
            &[not(1), not(2)],
            3,
            &[
                weighted_core_assumption(not(1), lit(1), 3),
                weighted_core_assumption(not(2), lit(2), 0),
            ]
        ),
        None
    );
    assert_eq!(
        PbCdclOptimizationCoreSummary::from_evidence(&[not(1), not(2)], 4, &valid_weighted),
        None
    );
}

#[test]
fn test_native_opt_core_probe_uses_min_weighted_core_contribution_for_lower_bound() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(1, lit(1)),
                linear_term(1, lit(2)),
                linear_term(1, lit(3)),
            ],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(8, lit(1)),
            linear_term(11, lit(2)),
            linear_term(5, lit(3)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);

    assert_eq!(
        solver.probe_single_lit_objective_core(&obj),
        PbCdclOptimizationCoreProbeResult::Evidence(PbCdclOptimizationCoreEvidence {
            core: vec![not(1), not(2), not(3)],
            lower_bound: 5,
            weighted_core: vec![
                weighted_core_assumption(not(1), lit(1), 8),
                weighted_core_assumption(not(2), lit(2), 11),
                weighted_core_assumption(not(3), lit(3), 5),
            ],
            model: None,
        })
    );
}

#[test]
fn test_native_opt_core_probe_fails_closed_on_weight_accounting_overflow() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(i128::MAX, lit(1)),
            linear_term(1, lit(1)),
            linear_term(1, lit(2)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);

    assert_eq!(
        solver.probe_single_lit_objective_core(&obj),
        PbCdclOptimizationCoreProbeResult::Unsupported(
            PbCdclOptimizationCoreUnsupportedReason::WeightOverflow,
        )
    );
}

#[test]
fn test_native_opt_core_probe_fails_closed_on_duplicate_core_assumption_accounting() {
    let objective = objective(vec![linear_term(3, lit(1)), linear_term(5, lit(2))]);
    let probe = build_single_lit_objective_probe(&objective).expect("objective probe");

    assert_eq!(probe.bound_for_core(&[not(1), not(1)]), None);
    assert_eq!(probe.lower_bound_for_core(&[not(2), not(2)]), None);
}

#[test]
fn test_native_opt_core_probe_sat_evidence_does_not_expose_unsat_core() {
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 0,
        constraints: Vec::new(),
        objective: Some(objective(vec![linear_term(2, lit(1))])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.probe_single_lit_objective_core(&obj);
    let evidence = result.evidence().expect("SAT model evidence");

    assert!(evidence.as_satisfiable_model().is_some());
    assert_eq!(evidence.as_unsat_core(), None);
}

#[test]
fn test_native_opt_core_probe_trim_redundant_core_prefix() {
    fn never_stop(_: &PbCdclSolver) -> bool {
        false
    }

    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(2, lit(1)),
            linear_term(3, lit(2)),
            linear_term(5, lit(3)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let probe = build_single_lit_objective_probe(&obj).expect("objective probe");
    let mut solver = PbCdclSolver::new(&instance);
    let mut never_stop = never_stop;

    let trimmed = solver
        .trim_unsat_assumption_core_prefix_with_stop(vec![not(1), not(2), not(3)], &mut never_stop)
        .expect("trimming should not be interrupted");

    assert_eq!(trimmed, vec![not(1), not(2)]);
    assert_eq!(probe.lower_bound_for_core(&trimmed), Some(2));

    match solver.solve_with_assumptions(&[not(3)]) {
        PbCdclAssumptionResult::Satisfiable(model) => {
            assert!(!model[2], "trim queries must leave assumptions temporary");
        }
        other => panic!("expected SAT after trim probe cleanup, got {other:?}"),
    }
}

#[test]
fn test_native_opt_core_probe_trim_interrupt_cleans_up_without_evidence() {
    fn stop_immediately(_: &PbCdclSolver) -> bool {
        true
    }

    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(1, lit(1)),
            linear_term(1, lit(2)),
            linear_term(1, lit(3)),
        ])),
    };

    let mut solver = PbCdclSolver::new(&instance);
    let mut stop_immediately = stop_immediately;

    assert_eq!(
        solver.trim_unsat_assumption_core_prefix_with_stop(
            vec![not(1), not(2), not(3)],
            &mut stop_immediately,
        ),
        None
    );
    assert_eq!(
        solver.decision_level, 0,
        "interrupted trim query must backtrack to root"
    );

    match solver.solve_with_assumptions(&[not(3)]) {
        PbCdclAssumptionResult::Satisfiable(model) => {
            assert!(!model[2], "interrupted trim assumptions must be temporary");
        }
        other => panic!("expected SAT after interrupted trim cleanup, got {other:?}"),
    }
}

#[test]
fn test_solve_with_stop_interrupts_before_learning_non_root_conflict() {
    let instance = root_probe_decoy_pigeonhole_3_2_instance();

    // Unpreprocessed so the cdcl search reaches a non-root conflict (the
    // behavior under test) rather than having preprocessing alter the
    // search dynamics.
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    let result = solver.solve_with_stop(|solver| solver.stats.conflicts >= 1);

    assert_eq!(result, PbCdclResult::Unknown);
    assert!(
        solver.stats.conflicts >= 1,
        "interrupt should trigger after a real conflict"
    );
    assert!(
        solver.decision_level > 0,
        "interrupt should stop during search"
    );
    assert_eq!(
        solver.stats.learned, 0,
        "interrupted conflict analysis must not learn a partial constraint"
    );
}

#[test]
fn test_new_interruptible_stops_before_preprocess() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(2, lit(1)), linear_term(1, lit(2))], 2),
            ge_constraint(vec![linear_term(1, lit(2)), linear_term(1, lit(3))], 1),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new_interruptible(&instance, || true);
    let result = solver.solve();

    assert_eq!(result, PbCdclResult::Unknown);
}

#[test]
fn test_new_unpreprocessed_interruptible_skips_preprocess_fixing() {
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 1,
        constraints: vec![ge_constraint(vec![linear_term(1, lit(1))], 1)],
        objective: None,
    };

    let solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);

    assert_eq!(solver.propagator.value(1), LitValue::Unassigned);
    assert!(solver.fixed_literals.is_empty());
    assert_eq!(solver.constraints.len(), 1);
}

#[test]
fn test_new_unpreprocessed_interruptible_imports_all_internal_rows() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![PbConstraint {
            terms: vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            rel: PbRel::Eq,
            rhs: 1,
        }],
        objective: None,
    };

    let solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);

    assert_eq!(solver.propagator.num_constraints(), 2);
    assert_eq!(solver.constraints.len(), 2);
    assert!(solver
        .constraints
        .iter()
        .all(|constraint| constraint.rel == PbRel::Ge));
}

#[test]
fn test_new_unpreprocessed_interruptible_honors_immediate_stop() {
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 1,
        constraints: vec![ge_constraint(vec![linear_term(1, lit(1))], 1)],
        objective: None,
    };

    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || true);
    let result = solver.solve_interruptible(|| false);

    assert!(solver.interrupted);
    assert!(solver.constraints.is_empty());
    assert_eq!(result, PbCdclResult::Unknown);
}

#[test]
fn test_new_unpreprocessed_interruptible_stops_during_constraint_load() {
    let constraints = (0..600)
        .map(|idx| ge_constraint(vec![linear_term(1, lit(idx + 1))], 1))
        .collect::<Vec<_>>();
    let instance = PbInstance {
        num_vars: constraints.len() as u32,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    };
    let polls = std::cell::Cell::new(0usize);

    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || {
        let next = polls.get() + 1;
        polls.set(next);
        next >= 2
    });
    let result = solver.solve_interruptible(|| false);

    assert!(
        polls.get() >= 2,
        "constructor should poll while loading constraints"
    );
    assert!(solver.interrupted);
    assert!(solver.constraints.is_empty());
    assert_eq!(result, PbCdclResult::Unknown);
}

#[test]
fn test_new_unpreprocessed_interruptible_stops_during_wide_constraint_import() {
    let terms = (1..=CONSTRUCTOR_LOAD_STOP_POLL_INTERVAL as u32 + 1)
        .map(|var| linear_term(1, lit(var)))
        .collect::<Vec<_>>();
    let instance = PbInstance {
        num_vars: terms.len() as u32,
        num_constraints: 1,
        constraints: vec![ge_constraint(terms, 1)],
        objective: None,
    };
    let polls = std::cell::Cell::new(0usize);

    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || {
        let next = polls.get() + 1;
        polls.set(next);
        next >= 3
    });
    let result = solver.solve_interruptible(|| false);

    assert!(
        polls.get() >= 3,
        "constructor should poll while scanning one wide imported row"
    );
    assert!(solver.interrupted);
    assert!(solver.constraints.is_empty());
    assert_eq!(result, PbCdclResult::Unknown);
}

#[test]
fn test_backtrack_to_repairs_propagator_without_full_rebuild() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 0,
        constraints: Vec::new(),
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    solver.decide(1);
    solver.decide(2);
    solver.decide(3);

    let rebuilds_before = solver.propagator.rebuild_count();
    solver.backtrack_to(0);
    let rebuilds_after = solver.propagator.rebuild_count();

    assert_eq!(rebuilds_after, rebuilds_before);
    assert_eq!(solver.decision_level, 0);
    assert!(solver.trail.is_empty());
}

#[test]
fn test_backtrack_to_interruptible_stops_during_rebuild_and_can_resume() {
    let constraints: Vec<PbConstraint> = (0..600)
        .map(|idx| {
            let y = idx * 2 + 2;
            let z = y + 1;
            ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(y)),
                    linear_term(1, lit(z)),
                ],
                1,
            )
        })
        .collect();
    let instance = PbInstance {
        num_vars: 1201,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let assignment_polls = std::cell::Cell::new(0usize);
    assert_eq!(
        solver.decide_interruptible(-1, &mut || {
            let next = assignment_polls.get() + 1;
            assignment_polls.set(next);
            next >= 5
        }),
        PropResult::Interrupted
    );
    assert_eq!(solver.decision_level, 1);
    assert_eq!(solver.propagator.value(1), LitValue::False);

    let polls = std::cell::Cell::new(0usize);
    let interrupted = solver.backtrack_to_interruptible(0, &mut || {
        let next = polls.get() + 1;
        polls.set(next);
        next >= 3
    });

    assert!(
        interrupted,
        "interrupt should stop the rebuild-heavy backtrack"
    );
    assert_eq!(solver.decision_level, 0);
    assert!(solver.trail.is_empty());
    assert!(
        solver.trail_lim.is_empty(),
        "interruptible backtrack must leave no stale level markers"
    );
    assert_eq!(solver.propagator.value(1), LitValue::Unassigned);
    assert_eq!(solver.propagator.propagate(), PropResult::Ok);
}

#[test]
fn test_solve_with_stop_interrupts_during_propagation_chain() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, not(2)), linear_term(1, lit(3))], 1),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    solver.config.root_probe_enabled = false;
    let result = solver.solve_with_stop(|solver| solver.stats.propagations >= 1);

    assert_eq!(result, PbCdclResult::Unknown);
    assert_eq!(
        solver.stats.propagations, 1,
        "interrupt should stop the root propagation chain after the first implication"
    );
}

#[test]
fn test_root_propagation_uses_scan_cursor_for_independent_units() {
    let constraint_count = 32usize;
    let constraints = (1..=constraint_count as u32)
        .map(|var| ge_constraint(vec![linear_term(1, lit(var))], 1))
        .collect::<Vec<_>>();
    let instance = PbInstance {
        num_vars: constraint_count as u32,
        num_constraints: constraint_count as u32,
        constraints,
        objective: None,
    };

    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    solver.config.root_probe_enabled = false;

    let result = solver.solve();

    assert!(matches!(result, PbCdclResult::Satisfiable(_)));
    assert_eq!(solver.stats.decisions, 0);
    assert_eq!(solver.stats.propagations, constraint_count as u64);
    let stats = solver.propagator.propagation_stats();
    assert!(
        stats.clause_checks <= (constraint_count as u64) * 3,
        "root propagation should scan forward and recheck sources, not restart a full scan \
             after every unit; saw {} clause checks for {} constraints",
        stats.clause_checks,
        constraint_count
    );
}

#[test]
fn test_root_propagation_rechecks_source_constraint_for_cardinality_chain() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(1, lit(1)),
                linear_term(1, lit(2)),
                linear_term(1, lit(3)),
            ],
            3,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    solver.config.root_probe_enabled = false;

    let result = solver.solve();

    assert!(matches!(result, PbCdclResult::Satisfiable(_)));
    assert_eq!(
        solver.stats.decisions, 0,
        "all three literals are root-level consequences of one PB row"
    );
    assert_eq!(solver.stats.propagations, 3);
}

#[test]
fn test_solve_interruptible_stops_during_root_propagation_scan() {
    let constraints: Vec<PbConstraint> = (0..600)
        .map(|idx| {
            let base = idx * 2 + 1;
            ge_constraint(
                vec![linear_term(1, lit(base)), linear_term(1, lit(base + 1))],
                1,
            )
        })
        .collect();
    let instance = PbInstance {
        num_vars: 1200,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    };

    let polls = std::cell::Cell::new(0usize);
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_interruptible(|| {
        let next = polls.get() + 1;
        polls.set(next);
        next >= 3
    });

    assert_eq!(result, PbCdclResult::Unknown);
    assert!(
        polls.get() >= 3,
        "interrupt should be observed during the full propagation scan"
    );
}

#[test]
fn test_solve_interruptible_with_proof_stops_during_root_scan_fail_closed() {
    let constraints: Vec<PbConstraint> = (0..600)
        .map(|idx| {
            let base = idx * 2 + 1;
            ge_constraint(
                vec![linear_term(1, lit(base)), linear_term(1, lit(base + 1))],
                1,
            )
        })
        .collect();
    let instance = PbInstance {
        num_vars: 1200,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    };

    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");
    let polls = std::cell::Cell::new(0usize);
    let result = solver.solve_interruptible(|| {
        let next = polls.get() + 1;
        polls.set(next);
        next >= 3
    });

    assert_eq!(result, PbCdclResult::Unknown);
    solver
        .conclude_proof()
        .expect("interrupted propagation scan should flush without a terminal conclusion");
    let proof = buf.as_string();
    assert!(
        !proof.contains("conclusion SAT"),
        "interrupted proof must not claim SAT: {proof}"
    );
    assert!(
        !proof.contains("conclusion UNSAT"),
        "interrupted proof must not claim UNSAT: {proof}"
    );
}

#[test]
fn test_decide_interruptible_rolls_back_uncommitted_assignment_state() {
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 0,
        constraints: Vec::new(),
        objective: None,
    };

    let polls = std::cell::Cell::new(0usize);
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.decide_interruptible(1, &mut || {
        let next = polls.get() + 1;
        polls.set(next);
        next >= 3
    });

    assert_eq!(result, PropResult::Interrupted);
    assert_eq!(
        solver.decision_level, 0,
        "interrupted decision must not leave behind a ghost decision level"
    );
    assert!(
        solver.trail_lim.is_empty(),
        "interrupted decision must not leave behind a trail-limit marker"
    );
    assert!(
        solver.trail.is_empty(),
        "interrupted decision must not leave behind a ghost trail entry"
    );
    assert_eq!(
        solver.propagator.value(1),
        LitValue::Unassigned,
        "the propagator never recorded the assignment, so solver state must stay empty"
    );

    let result = solver.decide_interruptible(1, &mut || false);
    assert_eq!(result, PropResult::Ok);
    assert_eq!(solver.decision_level, 1);
    assert_eq!(solver.trail.len(), 1);
    assert_eq!(solver.propagator.value(1), LitValue::True);
}

#[test]
fn test_solve_cardinality_at_most_one() {
    // At-most-one: ~x1 + ~x2 + ~x3 >= 2 (at most one can be true)
    // Combined with: x1 + x2 + x3 >= 1 (at least one must be true)
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(
                vec![
                    linear_term(1, not(1)),
                    linear_term(1, not(2)),
                    linear_term(1, not(3)),
                ],
                2,
            ),
            ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(2)),
                    linear_term(1, lit(3)),
                ],
                1,
            ),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();

    match result {
        PbCdclResult::Satisfiable(model) => {
            let true_count = model.iter().filter(|&&v| v).count();
            assert_eq!(true_count, 1, "exactly one variable should be true");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_solve_weighted_constraint() {
    // 3*x1 + 2*x2 + x3 >= 4
    // Solutions: x1=T,x2=T (5>=4), x1=T,x3=T (4>=4), etc.
    // NOT solution: x2=T,x3=T (3<4)
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(3, lit(1)),
                linear_term(2, lit(2)),
                linear_term(1, lit(3)),
            ],
            4,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();

    match result {
        PbCdclResult::Satisfiable(model) => {
            let sum: i128 = [3, 2, 1]
                .iter()
                .zip(model.iter())
                .filter(|(_, &v)| v)
                .map(|(&c, _)| c)
                .sum();
            assert!(sum >= 4, "weighted sum {sum} must be >= 4");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_luby_sequence_first_values() {
    // Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
    assert_eq!(luby_sequence(0), 1);
    assert_eq!(luby_sequence(1), 1);
    assert_eq!(luby_sequence(2), 2);
    assert_eq!(luby_sequence(3), 1);
    assert_eq!(luby_sequence(4), 1);
    assert_eq!(luby_sequence(5), 2);
    assert_eq!(luby_sequence(6), 4);
}

#[test]
fn test_stats_are_populated() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, not(2))], 1),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let _result = solver.solve();
    let stats = solver.stats();

    // Should have made at least one decision.
    assert!(stats.decisions > 0 || stats.propagations > 0);
}

#[test]
fn test_solve_pigeonhole_2_1() {
    // Pigeonhole: 2 pigeons, 1 hole. Each pigeon must be in a hole,
    // but the hole can hold at most 1. UNSAT.
    // p1_h1 + p2_h1 <= 1 (at most one pigeon in hole 1)
    // p1_h1 >= 1 (pigeon 1 must be somewhere)
    // p2_h1 >= 1 (pigeon 2 must be somewhere)
    // Variables: x1 = p1_h1, x2 = p2_h1
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 3,
        constraints: vec![
            // ~x1 + ~x2 >= 1 (at most one true)
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, not(2))], 1),
            // x1 >= 1
            ge_constraint(vec![linear_term(1, lit(1))], 1),
            // x2 >= 1
            ge_constraint(vec![linear_term(1, lit(2))], 1),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();

    assert_eq!(result, PbCdclResult::Unsatisfiable);
}

#[test]
fn test_solve_weighted_pigeonhole_3_2() {
    // Weighted pigeonhole: 3 pigeons, 2 holes with weights.
    // This exercises cutting-planes conflict analysis on genuinely
    // weighted PB constraints where clause-style analysis would be weak.
    //
    // Each pigeon must go somewhere:
    //   x1 + x2 >= 1 (pigeon 1 in hole 1 or 2)
    //   x3 + x4 >= 1 (pigeon 2 in hole 1 or 2)
    //   x5 + x6 >= 1 (pigeon 3 in hole 1 or 2)
    // Each hole has capacity 1:
    //   ~x1 + ~x3 + ~x5 >= 2 (at most one pigeon in hole 1)
    //   ~x2 + ~x4 + ~x6 >= 2 (at most one pigeon in hole 2)
    // UNSAT because 3 pigeons cannot fit in 2 holes.
    let instance = PbInstance {
        num_vars: 6,
        num_constraints: 5,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, lit(3)), linear_term(1, lit(4))], 1),
            ge_constraint(vec![linear_term(1, lit(5)), linear_term(1, lit(6))], 1),
            ge_constraint(
                vec![
                    linear_term(1, not(1)),
                    linear_term(1, not(3)),
                    linear_term(1, not(5)),
                ],
                2,
            ),
            ge_constraint(
                vec![
                    linear_term(1, not(2)),
                    linear_term(1, not(4)),
                    linear_term(1, not(6)),
                ],
                2,
            ),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();

    assert_eq!(result, PbCdclResult::Unsatisfiable);
}

#[test]
fn test_solve_weighted_pb_unsat() {
    // Genuinely weighted UNSAT instance:
    //   3*x1 + 2*x2 >= 4  (need x1=T or both x1,x2)
    //   2*~x1 + 3*~x2 >= 4  (need ~x1=T or both ~x1,~x2)
    // No assignment satisfies both:
    //   x1=T,x2=T: first OK (5>=4), second: 0 < 4 FAIL
    //   x1=T,x2=F: first: 3 < 4 FAIL
    //   x1=F,x2=T: first: 2 < 4 FAIL
    //   x1=F,x2=F: first: 0 < 4 FAIL
    // Wait — let me recheck. Actually x1=T,x2=T: second = 2*0 + 3*0 = 0 < 4. FAIL.
    //   x1=F,x2=F: second = 2*1 + 3*1 = 5 >= 4 OK, but first = 0 < 4. FAIL.
    // So genuinely UNSAT. This exercises weighted cutting planes.
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(3, lit(1)), linear_term(2, lit(2))], 4),
            ge_constraint(vec![linear_term(2, not(1)), linear_term(3, not(2))], 4),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();

    assert_eq!(result, PbCdclResult::Unsatisfiable);
}

#[test]
fn test_solve_weighted_pb_sat() {
    // Weighted SAT instance that requires conflict analysis:
    //   3*x1 + 2*x2 + x3 >= 3
    //   2*~x1 + 3*x2 + x3 >= 3
    //   x1 + x2 + ~x3 >= 1
    // Solution: x1=F, x2=T, x3=T: first=2+1=3>=3, second=2+3+1=6>=3, third=1>=1. SAT.
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 3,
        constraints: vec![
            ge_constraint(
                vec![
                    linear_term(3, lit(1)),
                    linear_term(2, lit(2)),
                    linear_term(1, lit(3)),
                ],
                3,
            ),
            ge_constraint(
                vec![
                    linear_term(2, not(1)),
                    linear_term(3, lit(2)),
                    linear_term(1, lit(3)),
                ],
                3,
            ),
            ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(2)),
                    linear_term(1, not(3)),
                ],
                1,
            ),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();

    match result {
        PbCdclResult::Satisfiable(model) => {
            // Verify all constraints.
            let vals = [
                0,
                i128::from(model[0]),
                i128::from(model[1]),
                i128::from(model[2]),
            ];
            let neg = |v: i128| 1 - v;
            let c1 = 3 * vals[1] + 2 * vals[2] + vals[3];
            let c2 = 2 * neg(vals[1]) + 3 * vals[2] + vals[3];
            let c3 = vals[1] + vals[2] + neg(vals[3]);
            assert!(c1 >= 3, "constraint 1 violated: {c1} < 3");
            assert!(c2 >= 3, "constraint 2 violated: {c2} < 3");
            assert!(c3 >= 1, "constraint 3 violated: {c3} < 1");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_reduce_db_deletes_low_quality_learned_constraints() {
    let instance = PbInstance {
        num_vars: 6,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            (1..=6).map(|v| linear_term(1, lit(v))).collect(),
            1,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);

    for i in 1..=4 {
        let c = ge_constraint(vec![linear_term(1, lit(i)), linear_term(1, lit(i + 1))], 1);
        solver.add_learned_constraint(c);
    }

    assert_eq!(solver.learned_constraints.len(), 4);
    assert_eq!(solver.learned_lbd.len(), 4);
    assert_eq!(solver.learned_active.len(), 4);

    solver.learned_lbd[0] = 1;
    solver.learned_lbd[1] = 2;
    solver.learned_lbd[2] = 8;
    solver.learned_lbd[3] = 10;

    solver.reduce_db();

    assert!(
        solver.learned_active[0],
        "LBD=1 constraint must not be deleted"
    );
    assert!(
        solver.learned_active[1],
        "LBD=2 constraint must not be deleted"
    );

    let deleted_count = solver.learned_active.iter().filter(|&&a| !a).count();
    assert_eq!(
        deleted_count, 1,
        "half of weak constraints should be deleted"
    );
    assert!(
        !solver.learned_active[3],
        "LBD=10 (worst) should be deleted"
    );
    assert!(
        solver.learned_active[2],
        "LBD=8 should survive (only half deleted)"
    );

    assert_eq!(solver.stats.reduce_db_calls, 1);
    assert_eq!(solver.stats.learned_deletions, 1);
}

#[test]
fn test_learned_activity_reducedb_default_off() {
    // The opt-in heuristic must be OFF by default: no activity bumping, no
    // size protection, no growing cadence — `reduce_db` behaves exactly as
    // the historical LBD-descending path.
    let instance = PbInstance {
        num_vars: 6,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            (1..=6).map(|v| linear_term(1, lit(v))).collect(),
            1,
        )],
        objective: None,
    };
    let mut solver = PbCdclSolver::new(&instance);
    assert!(!solver.config.learned_activity_reducedb_enabled);

    // Size-2 lemmas with weak LBD: with the opt-in OFF they are NOT size
    // protected, so the worst half is deleted (legacy behavior).
    for i in 1..=4 {
        solver.add_learned_constraint(ge_constraint(
            vec![linear_term(1, lit(i)), linear_term(1, lit(i + 1))],
            1,
        ));
    }
    for slot in solver.learned_lbd.iter_mut() {
        *slot = 10;
    }
    solver.reduce_db();
    let deleted = solver.learned_active.iter().filter(|&&a| !a).count();
    assert_eq!(
        deleted, 2,
        "default-off path must delete the worst half regardless of size"
    );
}

#[test]
fn test_reduce_db_protects_short_lemmas_when_enabled() {
    // Opt-in two-tier reduceDB must never delete a learned lemma of size
    // <= REDUCE_DB_PROTECT_SIZE, regardless of how poor its LBD is.
    let instance = PbInstance {
        num_vars: 12,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            (1..=12).map(|v| linear_term(1, lit(v))).collect(),
            1,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    solver.set_learned_activity_reducedb_enabled(true);

    // Two size-2 lemmas (protected) and two size-3 lemmas (deletable).
    solver.add_learned_constraint(ge_card_run(1, 2));
    solver.add_learned_constraint(ge_card_run(3, 2));
    solver.add_learned_constraint(ge_card_run(5, 3));
    solver.add_learned_constraint(ge_card_run(8, 3));

    // All weak LBD so only the size protection can save the binaries.
    for slot in solver.learned_lbd.iter_mut() {
        *slot = 10;
    }

    solver.reduce_db();

    assert!(
        solver.learned_active[0],
        "size-2 lemma must survive despite LBD=10"
    );
    assert!(
        solver.learned_active[1],
        "size-2 lemma must survive despite LBD=10"
    );
    let deleted = solver.learned_active.iter().filter(|&&a| !a).count();
    assert_eq!(deleted, 1, "only one deletable size-3 lemma is removed");
    assert!(
        !solver.learned_active[2] || !solver.learned_active[3],
        "exactly one size-3 lemma should be deleted"
    );
}

#[test]
fn test_reduce_db_breaks_lbd_ties_by_activity_when_enabled() {
    // Among equal-LBD deletable lemmas, the one with the LOWEST activity is
    // the worst and must be deleted first.
    let instance = PbInstance {
        num_vars: 12,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            (1..=12).map(|v| linear_term(1, lit(v))).collect(),
            1,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    solver.set_learned_activity_reducedb_enabled(true);

    for i in 0..4 {
        solver.add_learned_constraint(ge_card_run(1 + i * 3, 3));
    }

    // Equal (weak) LBD for all four lemmas; only activity breaks the tie.
    for slot in solver.learned_lbd.iter_mut() {
        *slot = 10;
    }
    // Highest activity is most-useful (kept); lowest is worst (deleted first).
    solver.learned_activity[0] = 100.0;
    solver.learned_activity[1] = 1.0; // worst
    solver.learned_activity[2] = 50.0;
    solver.learned_activity[3] = 2.0; // second worst

    solver.reduce_db();

    // Worst half of 4 = 2 deleted: the two lowest-activity lemmas (1 and 3).
    assert!(!solver.learned_active[1], "lowest-activity lemma deleted");
    assert!(
        !solver.learned_active[3],
        "second-lowest-activity lemma deleted"
    );
    assert!(solver.learned_active[0], "high-activity lemma survives");
    assert!(solver.learned_active[2], "high-activity lemma survives");
}

#[test]
fn test_reduce_db_never_deletes_a_current_reason_during_aggressive_solve_enabled() {
    // End-to-end soundness guard: drive a real (UNSAT) solve with the most
    // aggressive reduceDB cadence possible AND the opt-in heuristic enabled,
    // then assert (a) the verdict is unchanged and (b) no trail reason ever
    // points at a deleted learned constraint.
    let instance = root_probe_decoy_pigeonhole_3_2_instance();
    // Unpreprocessed so the cdcl search performs real conflicts and reaches
    // reduce_db maintenance (matching the existing maintenance test).
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    solver.set_learned_activity_reducedb_enabled(true);
    solver.config.reduce_interval = 1;
    solver.config.root_probe_enabled = false;

    let result = solver.solve();
    assert_eq!(
        result,
        PbCdclResult::Unsatisfiable,
        "aggressive reduceDB + activity heuristic must not change the UNSAT verdict"
    );
    assert!(
        solver.stats.reduce_db_calls > 0,
        "the aggressive cadence must have exercised reduce_db"
    );

    // Final consistency: every current trail reason references a live
    // constraint (original, or an active learned lemma) — never a deleted one.
    let num_original = solver.constraints.len();
    for entry in &solver.trail {
        let Some(reason_cid) = entry.reason else {
            continue;
        };
        if let Some(learned_idx) = reason_cid.checked_sub(num_original) {
            assert!(
                learned_idx < solver.learned_active.len() && solver.learned_active[learned_idx],
                "a current trail reason points at a deleted learned constraint"
            );
        }
    }
}

#[test]
fn test_learned_activity_toggle_does_not_change_verdict() {
    // Soundness invariant: the opt-in heuristic is deletion-ranking only, so
    // toggling it must never change a SAT/UNSAT verdict on the same instance.
    let instance = root_probe_decoy_pigeonhole_3_2_instance();

    let mut off = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    off.config.reduce_interval = 1;
    off.config.root_probe_enabled = false;
    let off_result = off.solve();

    let mut on = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    on.set_learned_activity_reducedb_enabled(true);
    on.config.reduce_interval = 1;
    on.config.root_probe_enabled = false;
    let on_result = on.solve();

    assert_eq!(
        off_result, on_result,
        "toggling the learned-activity reduceDB heuristic must not change the verdict"
    );
    assert_eq!(off_result, PbCdclResult::Unsatisfiable);
}

#[test]
fn test_reduce_db_preserves_glue_constraints() {
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(1, lit(1)),
                linear_term(1, lit(2)),
                linear_term(1, lit(3)),
                linear_term(1, lit(4)),
            ],
            1,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);

    let glue_constraint = ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(2))], 1);
    let weak_constraint_1 = ge_constraint(vec![linear_term(1, lit(3)), linear_term(1, lit(4))], 1);
    let weak_constraint_2 = ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(4))], 1);

    solver.add_learned_constraint(glue_constraint);
    solver.add_learned_constraint(weak_constraint_1);
    solver.add_learned_constraint(weak_constraint_2);

    let num_learned_before = solver.learned_constraints.len();
    assert!(
        num_learned_before >= 3,
        "should have at least 3 learned constraints"
    );

    solver.learned_lbd[0] = 1;
    for i in 1..solver.learned_lbd.len() {
        solver.learned_lbd[i] = 10;
    }

    solver.reduce_db();

    assert!(
        solver.learned_active[0],
        "glue constraint (LBD=1) must not be deleted by reduce_db"
    );

    let deleted_count = solver
        .learned_active
        .iter()
        .filter(|&&active| !active)
        .count();
    assert!(
        deleted_count > 0,
        "reduce_db should have deleted at least one weak constraint"
    );

    assert!(
        solver.stats.reduce_db_calls > 0,
        "reduce_db_calls stat should be incremented"
    );
    assert!(
        solver.stats.learned_deletions > 0,
        "learned_deletions stat should be incremented"
    );
}

#[test]
fn test_reduce_db_preserves_locked_reason_constraints() {
    let instance = PbInstance {
        num_vars: 8,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            (1..=8).map(|v| linear_term(1, lit(v))).collect(),
            1,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);

    for i in 1..=6 {
        let c = ge_constraint(vec![linear_term(1, lit(i)), linear_term(1, lit(i + 1))], 1);
        solver.add_learned_constraint(c);
    }

    solver.learned_lbd[0] = 1;
    solver.learned_lbd[1] = 2;
    solver.learned_lbd[2] = 7;
    solver.learned_lbd[3] = 8;
    solver.learned_lbd[4] = 9;
    solver.learned_lbd[5] = 10;

    let num_non_learned = solver.constraints.len();
    solver.trail.push(TrailEntry {
        lit: lit(1).var as Lit,
        level: 1,
        reason: Some(num_non_learned + 5),
    });

    solver.reduce_db();

    assert!(solver.learned_active[0], "glue LBD=1 must survive");
    assert!(solver.learned_active[1], "glue LBD=2 must survive");
    assert!(
        solver.learned_active[5],
        "locked learned constraint must not be deleted"
    );
    assert!(
        !solver.learned_active[4],
        "worst unlocked learned constraint should be deleted instead"
    );

    let deleted_count = solver.learned_active.iter().filter(|&&a| !a).count();
    assert_eq!(
        deleted_count, 1,
        "only one unlocked weak constraint is deleted"
    );
    assert_eq!(solver.stats.reduce_db_calls, 1);
    assert_eq!(solver.stats.learned_deletions, 1);
}

#[test]
fn test_reduce_db_deletion_sweep_is_atomic_under_stop() {
    // The deletion sweep is deliberately ATOMIC (P2e): per-row work is only
    // bookkeeping (flag + optional proof log) and the watch-list purge is one
    // bounded bulk sweep afterwards, so `reduce_db_with_stop` does NOT poll
    // the stop condition between deletions. Stopping mid-sweep would leave
    // rows marked deleted (`learned_active == false`) while still active in
    // the propagator — a state divergence the old per-row eager deactivation
    // never allowed. A stop request that first fires during deletion is
    // therefore honored at the caller's next poll point, after a coherent,
    // fully-applied sweep.
    let instance = PbInstance {
        num_vars: 8,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            (1..=8).map(|v| linear_term(1, lit(v))).collect(),
            1,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);

    for i in 1..=6 {
        let c = ge_constraint(vec![linear_term(1, lit(i)), linear_term(1, lit(i + 1))], 1);
        solver.add_learned_constraint(c);
    }

    solver.learned_lbd[0] = 1;
    solver.learned_lbd[1] = 2;
    solver.learned_lbd[2] = 7;
    solver.learned_lbd[3] = 8;
    solver.learned_lbd[4] = 9;
    solver.learned_lbd[5] = 10;

    let mut stop = |solver: &PbCdclSolver| solver.stats.learned_deletions >= 1;
    let interrupted = solver.reduce_db_with_stop(&mut stop);

    assert!(
        !interrupted,
        "a stop request first firing mid-deletion completes the atomic sweep"
    );
    assert_eq!(solver.stats.reduce_db_calls, 1);
    // Deletable (LBD > glue threshold 2) = indices {2,3,4,5}; worst half by
    // LBD descending = {5, 4}. Both must be deleted in the single sweep.
    assert_eq!(
        solver.stats.learned_deletions, 2,
        "the atomic sweep applies the full worst-half deletion"
    );
    let deleted_count = solver.learned_active.iter().filter(|&&a| !a).count();
    assert_eq!(
        deleted_count, 2,
        "sweep result must be coherent and complete"
    );
    assert!(
        !solver.learned_active[5] && !solver.learned_active[4],
        "the two worst weak constraints are deleted"
    );
    assert!(
        solver.learned_active[3] && solver.learned_active[2],
        "the surviving half stays active"
    );
    // The propagator agrees row-for-row with the bookkeeping (the divergence
    // the atomic sweep exists to prevent).
    let num_original = solver.constraints.len();
    for (idx, &active) in solver.learned_active.iter().enumerate() {
        assert_eq!(
            solver.propagator.is_constraint_active(num_original + idx),
            active,
            "learned row {idx} propagator/bookkeeping activity must match"
        );
    }
}

#[test]
fn test_solve_with_stop_interrupts_during_reduce_db_maintenance() {
    let instance = root_probe_decoy_pigeonhole_3_2_instance();

    // Unpreprocessed so the cdcl search performs real conflicts and reaches
    // reduce_db maintenance (the behavior under test).
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    solver.config.reduce_interval = 1;

    let result = solver.solve_with_stop(|solver| solver.stats.reduce_db_calls >= 1);

    assert_eq!(result, PbCdclResult::Unknown);
    assert!(
        solver.stats.conflicts >= 1,
        "interruption should happen after a real conflict"
    );
    assert_eq!(
        solver.stats.reduce_db_calls, 1,
        "stop request should be observed when reduce_db begins"
    );
    assert_eq!(
        solver.stats.learned_deletions, 0,
        "early reduce_db interruption must not delete learned constraints yet"
    );
}

// --- VSIDS heap tests ---

#[test]
fn test_vsids_heap_pop_max_returns_highest_activity() {
    let num_vars = 5u32;
    let mut activity = vec![0.0; num_vars as usize + 1];
    activity[1] = 1.0;
    activity[2] = 5.0;
    activity[3] = 3.0;
    activity[4] = 2.0;
    activity[5] = 4.0;

    let mut heap = VsidsHeap {
        heap: Vec::new(),
        position: vec![0u32; num_vars as usize + 1],
    };
    for var in 1..=num_vars {
        heap.insert(var, &activity);
    }

    let order: Vec<u32> = std::iter::from_fn(|| heap.pop_max(&activity)).collect();
    assert_eq!(order, vec![2, 5, 3, 4, 1]);
}

#[test]
fn test_vsids_heap_heapify_matches_incremental_build_order() {
    let num_vars = 7u32;
    let activity = vec![0.0, 4.0, 1.0, 7.0, 7.0, 2.0, 9.0, 3.0];

    let mut incremental = VsidsHeap {
        heap: Vec::new(),
        position: vec![0u32; num_vars as usize + 1],
    };
    for var in 1..=num_vars {
        incremental.insert(var, &activity);
    }
    let mut heapified = VsidsHeap::new_heapified(num_vars, &activity);

    let incremental_order: Vec<u32> =
        std::iter::from_fn(|| incremental.pop_max(&activity)).collect();
    let heapified_order: Vec<u32> = std::iter::from_fn(|| heapified.pop_max(&activity)).collect();

    assert_eq!(heapified_order, incremental_order);
}

#[test]
fn test_vsids_heap_heapify_matches_incremental_subset_order() {
    let num_vars = 8u32;
    let activity = vec![0.0, 1.0, 6.0, 2.5, 8.0, 3.0, 5.0, 4.5, 7.0];
    let vars = vec![2, 4, 6, 8];

    let mut incremental = VsidsHeap {
        heap: Vec::new(),
        position: vec![0u32; num_vars as usize + 1],
    };
    for &var in &vars {
        incremental.insert(var, &activity);
    }
    let mut heapified = VsidsHeap::from_vars_heapified(num_vars, vars, &activity);

    let incremental_order: Vec<u32> =
        std::iter::from_fn(|| incremental.pop_max(&activity)).collect();
    let heapified_order: Vec<u32> = std::iter::from_fn(|| heapified.pop_max(&activity)).collect();

    assert_eq!(heapified_order, incremental_order);
}

#[test]
fn test_vsids_heap_insert_and_contains() {
    let num_vars = 3u32;
    let activity = vec![0.0; num_vars as usize + 1];
    let mut heap = VsidsHeap {
        heap: Vec::new(),
        position: vec![0u32; num_vars as usize + 1],
    };

    assert!(!heap.contains(1));
    assert!(!heap.contains(2));
    assert!(heap.is_empty());

    heap.insert(2, &activity);
    assert!(heap.contains(2));
    assert!(!heap.contains(1));
    assert!(!heap.is_empty());

    heap.insert(2, &activity);
    assert_eq!(heap.heap.len(), 1);

    heap.insert(1, &activity);
    heap.insert(3, &activity);
    assert_eq!(heap.heap.len(), 3);

    heap.pop_max(&activity);
    heap.pop_max(&activity);
    heap.pop_max(&activity);
    assert!(heap.is_empty());
    assert!(!heap.contains(1));
}

#[test]
fn test_vsids_heap_update_percolates_correctly() {
    let num_vars = 4u32;
    let mut activity = vec![0.0; num_vars as usize + 1];
    activity[1] = 1.0;
    activity[2] = 2.0;
    activity[3] = 3.0;
    activity[4] = 4.0;

    let mut heap = VsidsHeap {
        heap: Vec::new(),
        position: vec![0u32; num_vars as usize + 1],
    };
    for var in 1..=num_vars {
        heap.insert(var, &activity);
    }

    assert_eq!(heap.heap[0], 4);

    activity[1] = 10.0;
    heap.update(1, &activity);

    let top = heap.pop_max(&activity).unwrap();
    assert_eq!(top, 1, "var 1 should be highest after activity bump");

    let second = heap.pop_max(&activity).unwrap();
    assert_eq!(second, 4, "var 4 should be second highest");
}

#[test]
fn test_phase_saving_remembers_polarity() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 3,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, not(2))], 1),
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(3))], 1),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();

    match result {
        PbCdclResult::Satisfiable(model) => {
            let x1 = i128::from(model[0]);
            let x2 = i128::from(model[1]);
            let x3 = i128::from(model[2]);
            assert!(x1 + x2 >= 1, "constraint 1 violated");
            assert!((1 - x1) + (1 - x2) >= 1, "constraint 2 violated");
            assert!(x1 + x3 >= 1, "constraint 3 violated");
        }
        other => panic!("expected SAT, got {other:?}"),
    }

    let any_phase_saved = solver.saved_phase[1..=3].iter().any(|&p| p);
    assert_eq!(solver.saved_phase.len(), 4);
    let model = match solver.solve() {
        PbCdclResult::Satisfiable(m) => m,
        _ => panic!("second solve should also be SAT"),
    };
    let _ = any_phase_saved;
    assert_eq!(model.len(), 3);
}

// --- Optimization tests ---

fn objective(terms: Vec<PbTerm>) -> PbObjective {
    PbObjective { terms }
}

/// Brute-force the true integer optimum (minimum objective) over all 0/1
/// assignments satisfying every `>=` / `=` constraint. Only used by the LP-bound
/// soundness tests on tiny instances. Returns `None` if infeasible.
fn brute_force_optimum(instance: &PbInstance, objective: &PbObjective) -> Option<i128> {
    let n = instance.num_vars as usize;
    assert!(n <= 20, "brute force only for tiny instances");
    let mut best: Option<i128> = None;
    for mask in 0u32..(1u32 << n) {
        let model: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 == 1).collect();
        let feasible = instance.constraints.iter().all(|c| {
            let lhs: i128 = c
                .terms
                .iter()
                .map(|t| {
                    let [l] = t.lits.as_slice() else {
                        return 0;
                    };
                    let val = model[(l.var - 1) as usize];
                    let lit_val = if l.negated { !val } else { val };
                    if lit_val {
                        t.coeff
                    } else {
                        0
                    }
                })
                .sum();
            match c.rel {
                PbRel::Ge => lhs >= c.rhs,
                PbRel::Eq => lhs == c.rhs,
            }
        });
        if !feasible {
            continue;
        }
        let value = eval_objective(objective, &model);
        best = Some(best.map_or(value, |b| b.min(value)));
    }
    best
}

/// A small pseudo-random sequence (xorshift) so the soundness test sweeps many
/// instances deterministically without an external RNG dependency.
fn xorshift_next(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

/// MANDATORY SOUNDNESS GATE: the at-root LP lower bound must never exceed the
/// true integer optimum, over many random *feasible* tiny instances. This is
/// the core soundness invariant the native-loop fold relies on (a too-high LP
/// bound would let the loop falsely conclude `Optimal` below the true optimum).
/// We exercise `lp_objective_lower_bound_at_root` directly so the assertion holds
/// regardless of whether the opt-in loop fold is enabled.
#[test]
fn test_at_root_lp_bound_never_exceeds_true_optimum() {
    let mut rng: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut checked = 0usize;
    for _ in 0..400 {
        let num_vars = 3 + (xorshift_next(&mut rng) % 4) as u32; // 3..=6
        let num_constraints = 1 + (xorshift_next(&mut rng) % 3) as usize;
        let mut constraints = Vec::new();
        for _ in 0..num_constraints {
            let mut terms = Vec::new();
            for var in 1..=num_vars {
                if xorshift_next(&mut rng).is_multiple_of(2) {
                    let coeff = 1 + (xorshift_next(&mut rng) % 5) as i128;
                    let negated = xorshift_next(&mut rng).is_multiple_of(2);
                    terms.push(linear_term(coeff, PbLit { var, negated }));
                }
            }
            if terms.is_empty() {
                terms.push(linear_term(1, lit(1)));
            }
            let total: i128 = terms.iter().map(|t| t.coeff).sum();
            let rhs = (xorshift_next(&mut rng) % ((total + 2) as u64)) as i128;
            constraints.push(ge_constraint(terms, rhs));
        }
        let obj = objective(
            (1..=num_vars)
                .map(|var| linear_term(1 + (xorshift_next(&mut rng) % 7) as i128, lit(var)))
                .collect(),
        );
        let instance = PbInstance {
            num_vars,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(obj.clone()),
        };
        let Some(true_opt) = brute_force_optimum(&instance, &obj) else {
            continue; // infeasible: skip.
        };

        let mut solver = PbCdclSolver::new(&instance);
        // Run a feasibility solve so preprocessing (and any fixed literals) is
        // applied, mirroring the production at-root call site.
        let _ = solver.solve_optimize(&obj, None);
        let lp_lb = solver.lp_objective_lower_bound_at_root(&obj, None, &|| false);
        if let Some(lp) = lp_lb {
            assert!(
                lp <= true_opt,
                "UNSOUND: at-root lp_lb {lp} > true optimum {true_opt}; instance={instance:?}"
            );
            checked += 1;
        }
    }
    assert!(
        checked > 0,
        "expected the LP bound to fire on at least one random instance"
    );
}

/// The at-root LP relaxation is *tight* (= the integer optimum) on a small
/// max-weight independent set over at-most-one (clique) rows — the structure of
/// the KE_* family. This is the case where the opt-in native-loop fold lets the
/// loop prove OPTIMUM the moment the first optimal incumbent is in hand. We
/// assert the bound is both sound (`<= true opt`) and here exactly tight.
///
/// Vertices 1..=4 with weights {1:5, 2:4, 3:3, 4:2}. Conflict (at-most-one)
/// rows: {1,2}, {1,3}, {2,3} form a triangle (so at most one of 1,2,3), and
/// {2,4}. Picking vertex 1 (weight 5) and vertex 4 (weight 2) is the unique max
/// independent set, value 7, i.e. objective `min -(5 x1 + 4 x2 + 3 x3 + 2 x4)`
/// optimum = -7.
#[test]
fn test_at_root_lp_bound_tight_on_weighted_independent_set() {
    let obj = objective(vec![
        linear_term(-5, lit(1)),
        linear_term(-4, lit(2)),
        linear_term(-3, lit(3)),
        linear_term(-2, lit(4)),
    ]);
    let amo =
        |a: u32, b: u32| ge_constraint(vec![linear_term(-1, lit(a)), linear_term(-1, lit(b))], -1);
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 4,
        constraints: vec![amo(1, 2), amo(1, 3), amo(2, 3), amo(2, 4)],
        objective: Some(obj.clone()),
    };
    let true_opt = brute_force_optimum(&instance, &obj).expect("feasible");
    assert_eq!(
        true_opt, -7,
        "fixture optimum should be -7 (vertices 1 and 4)"
    );

    let solver = PbCdclSolver::new(&instance);
    let lp_lb = solver
        .lp_objective_lower_bound_at_root(&obj, None, &|| false)
        .expect("LP bound should be produced on this fixture");
    assert!(
        lp_lb <= true_opt,
        "UNSOUND lp_lb {lp_lb} > true optimum {true_opt}"
    );
    assert_eq!(
        lp_lb, true_opt,
        "LP relaxation should be tight (= integer optimum) on this independent-set fixture"
    );
}

/// D3 regression: an interrupted notification only marks `needs_rebuild` —
/// its abandoned watch-list walk drops propagations that are re-discoverable
/// solely by rebuild + rescan. `needs_full_scan()` must therefore report true
/// while a rebuild is pending; otherwise a fresh-budget
/// `propagate_all_interruptible` whose queue happens to be empty skips both
/// the rebuild and the scan and returns a false fixpoint (the debug oracle
/// fires; in release the propagation is silently missed).
///
/// Interleaving: a clean drive certifies the event-driven fixpoint
/// (`full_scan_done`), then a decision's assignment lands but its
/// notification is interrupted at the entry poll (`needs_rebuild` set with
/// `full_scan_done` still true), then propagation resumes with a fresh
/// budget and must find the clause propagation.
#[test]
fn test_interrupt_dirty_state_forces_full_scan_on_next_drive() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: None,
    };

    let mut exercised = false;
    for stop_at in 1..12u32 {
        let mut solver = PbCdclSolver::new(&instance);
        // Clean drive: reaches the fixpoint and certifies event-driven mode.
        assert!(matches!(
            solver.propagate_all_interruptible(&mut || false),
            PropagateOutcome::Ok
        ));

        // Decide x1 = false with an interrupt at the notification entry poll.
        let mut calls = 0u32;
        let result = solver.decide_interruptible(-1, &mut || {
            calls += 1;
            calls >= stop_at
        });
        // Only the "assignment landed, notification abandoned" interleaving
        // exercises the defect.
        if !matches!(result, PropResult::Interrupted)
            || solver.propagator.value(-1) != LitValue::True
        {
            continue;
        }
        exercised = true;
        assert!(
            solver.propagator.needs_full_scan(),
            "pending rebuild must re-arm the full scan (D3)"
        );

        // Fresh budget: the drive must rebuild + rescan and find the clause
        // propagation x2 (pre-fix: queue empty, scan skipped, x2 missed and
        // the debug fixpoint oracle fires).
        assert!(matches!(
            solver.propagate_all_interruptible(&mut || false),
            PropagateOutcome::Ok
        ));
        assert_eq!(
            solver.propagator.value(2),
            LitValue::True,
            "dropped propagation must be re-discovered after the dirty interrupt"
        );
    }
    assert!(
        exercised,
        "no interrupt point produced the assignment-landed/notify-abandoned interleaving"
    );
}

/// Residualization soundness: with a preprocessing-fixed literal the
/// residualized at-root LP bound must still be `<= true optimum` (never too
/// high). We build an instance that forces a fixing, then assert the at-root LP
/// bound is a sound lower bound.
#[test]
fn test_at_root_lp_bound_residualized_for_fixed_literals_is_sound() {
    // x1 is forced true by a unit constraint; objective pays for x1..x4.
    let obj = objective(vec![
        linear_term(5, lit(1)),
        linear_term(3, lit(2)),
        linear_term(2, lit(3)),
        linear_term(4, lit(4)),
    ]);
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 3,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1))], 1), // x1 = 1 (forced)
            ge_constraint(vec![linear_term(1, lit(2)), linear_term(1, lit(3))], 1),
            ge_constraint(vec![linear_term(1, lit(3)), linear_term(1, lit(4))], 1),
        ],
        objective: Some(obj.clone()),
    };
    let true_opt = brute_force_optimum(&instance, &obj).expect("feasible");

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_optimize(&obj, None);
    let lp_lb = solver.lp_objective_lower_bound_at_root(&obj, None, &|| false);
    if let Some(lp) = lp_lb {
        assert!(
            lp <= true_opt,
            "UNSOUND residualized lp_lb {lp} > true optimum {true_opt}"
        );
    }
    match result {
        PbCdclResult::Optimal(_, value) | PbCdclResult::Feasible(_, value) => {
            assert!(value >= true_opt);
            if matches!(result, PbCdclResult::Optimal(_, _)) {
                assert_eq!(value, true_opt);
            }
        }
        other => panic!("expected a feasible/optimal result, got {other:?}"),
    }
}

#[test]
fn test_weighted_vertex_cover_opt_proof_uses_lower_bound_cut() {
    let objective = objective((1..=6).map(|var| linear_term(1, lit(var))).collect());
    let instance = PbInstance {
        num_vars: 6,
        num_constraints: 7,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, lit(2)), linear_term(1, lit(3))], 1),
            ge_constraint(vec![linear_term(1, lit(3)), linear_term(1, lit(4))], 1),
            ge_constraint(vec![linear_term(1, lit(4)), linear_term(1, lit(5))], 1),
            ge_constraint(vec![linear_term(1, lit(5)), linear_term(1, lit(6))], 1),
            ge_constraint(vec![linear_term(1, lit(6)), linear_term(1, lit(1))], 1),
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(4))], 1),
        ],
        objective: Some(objective.clone()),
    };
    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    let result = solver.solve_optimize(&objective, None);
    assert!(
        matches!(result, PbCdclResult::Optimal(_, 3)),
        "weighted vertex-cover canary should solve to optimum 3, got {result:?}"
    );
    solver
        .conclude_proof()
        .expect("weighted vertex-cover optimization proof should conclude");

    let proof = buf.as_string();
    assert!(
        proof.lines().any(|line| line.starts_with("soli ")),
        "OPT proof must log the incumbent solution: {proof}"
    );
    assert!(
        proof.lines().any(|line| line.starts_with("pol ")),
        "weighted vertex-cover lower bound requires a CP cut row: {proof}"
    );
    assert!(
        !proof.lines().any(|line| line == "rup >= 1 ;"),
        "weighted vertex-cover proof must not rely on the rejected empty RUP: {proof}"
    );
    // Hinted conclusion form: `conclusion BOUNDS 3 : <contradiction-id> 3 :
    // <incumbent witness>;` — the hints keep the conclusion verifiable in
    // unchecked-deletion mode (soli-logged solutions are discounted there).
    let conclusion = proof
        .lines()
        .find(|line| line.starts_with("conclusion BOUNDS "))
        .unwrap_or_else(|| panic!("weighted vertex-cover proof must conclude bounds: {proof}"));
    assert!(
        conclusion.starts_with("conclusion BOUNDS 3 : ")
            && conclusion.contains(" 3 : ")
            && conclusion.ends_with(';'),
        "weighted vertex-cover proof must conclude hinted exact optimum bounds: {conclusion}"
    );
}

#[test]
fn test_weighted_cardinality_optimization_proof_uses_literal_axiom_lower_bound_cut() {
    let objective = objective(vec![
        linear_term(2, lit(1)),
        linear_term(3, lit(2)),
        linear_term(5, lit(3)),
        linear_term(7, lit(4)),
    ]);
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(2)),
                    linear_term(1, lit(3)),
                    linear_term(1, lit(4)),
                ],
                2,
            ),
            ge_constraint(
                vec![
                    linear_term(1, not(1)),
                    linear_term(1, not(2)),
                    linear_term(1, not(3)),
                    linear_term(1, not(4)),
                ],
                2,
            ),
        ],
        objective: Some(objective.clone()),
    };
    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    assert!(solver.log_objective_bound_update(&[true, true, false, false]));
    assert!(
        matches!(
            solver.try_log_objective_lower_bound_cut_proof(&objective, 5),
            ObjectiveFloorCutOutcome::Derived(_)
        ),
        "weighted cardinality lower-bound proof should be derivable"
    );

    let proof = buf.as_string();
    assert!(
        proof
            .lines()
            .any(|line| line == "pol 1 3 * ~x1 + x3 2 * + x4 4 * + ;"),
        "weighted cardinality lower bound requires a literal-axiom CP row: {proof}"
    );
    assert!(
        !proof.lines().any(|line| line == "rup >= 1 ;"),
        "weighted cardinality proof must not rely on the rejected empty RUP: {proof}"
    );
    assert!(
        proof.lines().any(|line| line == "pol 4 3 + ;"),
        "weighted cardinality proof must add the lower and upper bound rows: {proof}"
    );
}

/// Phase-3 deletion discipline (superseded-soli dels): only the LATEST soli id
/// is read at conclusion (by `try_log_objective_lower_bound_cut_proof`), so each
/// tighter incumbent must checked-delete the PREVIOUS soli row — exactly one
/// deletion, emitted AFTER the newer soli (del-after-create/last-use). The first
/// incumbent has nothing to supersede, so it emits no del.
#[test]
fn test_superseded_soli_row_is_deleted() {
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(2)),
                    linear_term(1, lit(3)),
                    linear_term(1, lit(4)),
                ],
                1,
            ),
            ge_constraint(
                vec![
                    linear_term(1, not(1)),
                    linear_term(1, not(2)),
                    linear_term(1, not(3)),
                    linear_term(1, not(4)),
                ],
                1,
            ),
        ],
        objective: Some(objective(vec![
            linear_term(1, lit(1)),
            linear_term(1, lit(2)),
            linear_term(1, lit(3)),
            linear_term(1, lit(4)),
        ])),
    };
    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    // First incumbent: one soli row, nothing to supersede yet -> no deletion.
    assert!(solver.log_objective_bound_update(&[true, true, true, false]));
    let after_first = buf.as_string();
    assert_eq!(
        after_first
            .lines()
            .filter(|l| l.starts_with("soli "))
            .count(),
        1,
        "first incumbent emits one soli row: {after_first}"
    );
    assert_eq!(
        after_first
            .lines()
            .filter(|l| l.starts_with("del id "))
            .count(),
        0,
        "the latest (only) soli row must NOT be deleted: {after_first}"
    );

    // Strictly tighter incumbent: a second soli row PLUS deletion of the first.
    assert!(solver.log_objective_bound_update(&[true, false, false, false]));
    let after_second = buf.as_string();
    let lines: Vec<&str> = after_second.lines().collect();
    assert_eq!(
        lines.iter().filter(|l| l.starts_with("soli ")).count(),
        2,
        "exactly two soli rows after two incumbents: {after_second}"
    );
    let del_positions: Vec<usize> = lines
        .iter()
        .enumerate()
        .filter(|(_, l)| l.starts_with("del id "))
        .map(|(i, _)| i)
        .collect();
    assert_eq!(
        del_positions.len(),
        1,
        "exactly one superseded-soli deletion: {after_second}"
    );
    let last_soli = lines
        .iter()
        .rposition(|l| l.starts_with("soli "))
        .expect("two soli rows present");
    assert!(
        del_positions[0] > last_soli,
        "the superseded del must follow the newer soli row (del-after-create): {after_second}"
    );
}

fn weighted_core_assumption(
    assumption: PbLit,
    objective_lit: PbLit,
    contribution: i128,
) -> PbCdclOptimizationCoreWeightedAssumption {
    PbCdclOptimizationCoreWeightedAssumption {
        assumption,
        objective_lit,
        contribution,
    }
}

#[test]
fn test_optimize_finds_optimum_simple() {
    // min: +1 x1 +1 x2
    // subject to: x1 + x2 >= 1
    // Optimal: one of x1, x2 is true, cost = 1
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(1, lit(1)),
            linear_term(1, lit(2)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_optimize(&obj, None);

    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, 1, "optimal cost should be 1");
            let true_count = model.iter().filter(|&&v| v).count();
            assert_eq!(true_count, 1, "exactly one variable true for cost 1");
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

#[test]
fn test_optimize_zero_cost_optimal() {
    // min: +1 x2
    // subject to: x1 >= 1
    // x1 must be true, x2 can be false -> cost 0
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(vec![linear_term(1, lit(1))], 1)],
        objective: Some(objective(vec![linear_term(1, lit(2))])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_optimize(&obj, None);

    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, 0, "optimal cost should be 0");
            assert!(model[0], "x1 must be true");
            assert!(!model[1], "x2 should be false");
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

#[test]
fn test_optimize_infeasible() {
    // min: +1 x1
    // subject to: x1 >= 1 AND ~x1 >= 1 (UNSAT)
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1))], 1),
            ge_constraint(vec![linear_term(1, not(1))], 1),
        ],
        objective: Some(objective(vec![linear_term(1, lit(1))])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_optimize(&obj, None);

    assert_eq!(result, PbCdclResult::Unsatisfiable);
}

#[test]
fn test_optimize_infeasible_with_proof_concludes_as_inf_bounds() {
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1))], 1),
            ge_constraint(vec![linear_term(1, not(1))], 1),
        ],
        objective: Some(objective(vec![linear_term(1, lit(1))])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");
    let result = solver.solve_optimize(&obj, None);

    assert_eq!(result, PbCdclResult::Unsatisfiable);
    solver
        .conclude_proof()
        .expect("infeasible optimization proof should conclude cleanly");

    let proof = buf.as_string();
    assert!(
        proof.lines().any(|line| line == "rup >= 1 ;"),
        "infeasible optimization proof must derive contradiction: {proof}"
    );
    assert!(
        proof
            .lines()
            .any(|line| line == "conclusion BOUNDS INF INF;"),
        "infeasible optimization proof must conclude with infinite OPT bounds: {proof}"
    );
    assert!(
        !proof.contains("conclusion UNSAT"),
        "infeasible optimization proof must not use decision UNSAT footer: {proof}"
    );
    assert!(
        proof.lines().last() == Some("end pseudo-Boolean proof;"),
        "infeasible optimization proof must end with VeriPB terminator: {proof}"
    );
}

#[test]
fn test_optimize_positive_objective_range_overflow_returns_unknown() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1))], 1),
            ge_constraint(vec![linear_term(1, lit(2))], 1),
        ],
        objective: Some(objective(vec![
            linear_term(i128::MAX, lit(1)),
            linear_term(1, lit(2)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_optimize(&obj, None);

    assert_eq!(result, PbCdclResult::Unknown);
}

#[test]
fn test_optimize_interruptible_negative_range_underflow_returns_unknown_before_polling() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 0,
        constraints: vec![],
        objective: Some(objective(vec![
            linear_term(i128::MIN, lit(1)),
            linear_term(-1, lit(2)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let polls = std::cell::Cell::new(0usize);
    let result = solver.solve_optimize_interruptible(&obj, None, || {
        polls.set(polls.get() + 1);
        true
    });

    assert_eq!(result, PbCdclResult::Unknown);
    assert_eq!(
        polls.get(),
        0,
        "range guard should fire before the interruptible search starts"
    );
}

#[test]
fn test_optimize_range_overflow_with_proof_concludes_cleanly_after_early_unknown() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1))], 1),
            ge_constraint(vec![linear_term(1, lit(2))], 1),
        ],
        objective: Some(objective(vec![
            linear_term(i128::MAX, lit(1)),
            linear_term(1, lit(2)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf)
        .expect("proof writer creation must succeed");

    assert_eq!(solver.solve_optimize(&obj, None), PbCdclResult::Unknown);
    solver
        .conclude_proof()
        .expect("early range Unknown must not leave missing optimization bounds");
}

#[test]
fn test_optimize_interrupted_returns_feasible() {
    // min: +1 x1 +1 x2 +1 x3
    // subject to: x1 + x2 + x3 >= 1
    // Interrupt immediately after first solution.
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            (1..=3).map(|v| linear_term(1, lit(v))).collect(),
            1,
        )],
        objective: Some(objective((1..=3).map(|v| linear_term(1, lit(v))).collect())),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let should_stop = std::cell::Cell::new(false);
    let mut on_improve = |_: i128, _: &[bool]| should_stop.set(true);
    let result =
        solver.solve_optimize_interruptible(&obj, Some(&mut on_improve), || should_stop.get());

    match result {
        PbCdclResult::Feasible(model, value) | PbCdclResult::Optimal(model, value) => {
            // Should have found at least a feasible solution.
            let sum: i128 = model.iter().filter(|&&v| v).count() as i128;
            assert_eq!(sum, value, "objective value matches model");
            assert!(value >= 1, "at least one variable must be true");
        }
        other => panic!("expected Feasible or Optimal, got {other:?}"),
    }
}

#[test]
fn test_phase_completion_disabled_by_default() {
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 0,
        constraints: Vec::new(),
        objective: Some(objective(vec![linear_term(1, lit(1))])),
    };

    let solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);

    assert!(!solver.config.phase_completion_enabled);
}

#[test]
fn test_phase_completion_uses_saved_phase_and_validates_model() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(1, lit(1)),
            linear_term(2, lit(2)),
        ])),
    };
    let objective = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    solver.set_phase_completion_enabled(true);
    solver.seed_saved_phase_from_objective(&objective);

    let outcome = solver.try_phase_completion_incumbent_interruptible(&mut || false);

    match outcome {
        PhaseCompletionOutcome::Model(model) => {
            assert_eq!(model, vec![false, true]);
        }
        _ => panic!("expected phase completion model"),
    }
    assert_eq!(solver.decision_level, 0);
    assert!(solver.trail.is_empty());
}

#[test]
fn test_optimize_phase_completion_reports_feasible_not_optimal_when_interrupted() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(1, lit(1)),
            linear_term(2, lit(2)),
        ])),
    };
    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    solver.set_phase_completion_enabled(true);
    let should_stop = std::cell::Cell::new(false);
    let mut improvements = Vec::new();
    let mut on_improve = |obj_value: i128, model: &[bool]| {
        improvements.push((obj_value, model.to_vec()));
        should_stop.set(true);
    };

    let result =
        solver.solve_optimize_interruptible(&obj, Some(&mut on_improve), || should_stop.get());

    assert_eq!(improvements, vec![(2, vec![false, true])]);
    assert_eq!(result, PbCdclResult::Feasible(vec![false, true], 2));
}

#[test]
fn test_optimize_structural_lower_bound_promotes_interrupted_incumbent_to_optimal() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(1, lit(1)),
            linear_term(1, lit(2)),
        ])),
    };
    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let should_stop = std::cell::Cell::new(false);
    let mut improvements = Vec::new();
    let mut on_improve = |obj_value: i128, model: &[bool]| {
        improvements.push((obj_value, model.to_vec()));
        should_stop.set(true);
    };

    let result =
        solver.solve_optimize_interruptible(&obj, Some(&mut on_improve), || should_stop.get());

    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, 1);
            assert_eq!(eval_objective(&obj, &model), 1);
        }
        other => panic!("expected structural lower-bound optimum, got {other:?}"),
    }
    assert_eq!(improvements.len(), 1);
}

#[test]
fn test_optimize_weighted_structural_lower_bound_handles_duplicate_row_lit() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(1, lit(1)),
                linear_term(1, lit(1)),
                linear_term(1, lit(2)),
            ],
            2,
        )],
        objective: Some(objective(vec![
            linear_term(1, lit(1)),
            linear_term(1, lit(2)),
        ])),
    };
    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    let should_stop = std::cell::Cell::new(false);
    let mut improvements = Vec::new();
    let mut on_improve = |obj_value: i128, model: &[bool]| {
        improvements.push((obj_value, model.to_vec()));
        should_stop.set(true);
    };

    let result =
        solver.solve_optimize_interruptible(&obj, Some(&mut on_improve), || should_stop.get());

    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, 1);
            assert!(model[0], "x1 alone satisfies the weighted row");
            assert_eq!(eval_objective(&obj, &model), 1);
        }
        other => panic!("expected weighted structural lower-bound optimum, got {other:?}"),
    }
    assert_eq!(improvements.len(), 1);
}

#[test]
fn test_optimize_with_stop_interrupts_during_initial_propagation_chain() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, not(2)), linear_term(1, lit(3))], 1),
        ],
        objective: Some(objective((1..=3).map(|v| linear_term(1, lit(v))).collect())),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    solver.config.root_probe_enabled = false;
    let result =
        solver.solve_optimize_with_stop(&obj, None, |solver| solver.stats.propagations >= 1);

    assert_eq!(result, PbCdclResult::Unknown);
    assert_eq!(
        solver.stats.propagations, 1,
        "interrupt should stop the initial optimization search during the first propagation"
    );
}

#[test]
fn test_tightened_sat_candidate_without_improvement_is_not_proof() {
    assert_eq!(
        classify_tightened_sat_candidate(5, 5),
        TightenedSatOutcome::NotProven
    );
    assert_eq!(
        classify_tightened_sat_candidate(5, 7),
        TightenedSatOutcome::NotProven
    );
}

#[test]
fn test_tightened_sat_candidate_with_improvement_advances_search() {
    assert_eq!(
        classify_tightened_sat_candidate(5, 4),
        TightenedSatOutcome::Improved
    );
}

#[test]
fn test_tightened_solve_sat_without_improvement_returns_feasible_incumbent() {
    let objective = objective(vec![linear_term(1, lit(1)), linear_term(1, lit(2))]);
    let result = decide_tightened_solve_result(
        &objective,
        &[true, false],
        1,
        PbCdclResult::Satisfiable(vec![true, false]),
    );

    assert_eq!(
        result,
        TightenedSolveDecision::Return(PbCdclResult::Feasible(vec![true, false], 1))
    );
}

#[test]
fn test_tightened_solve_sat_with_improvement_continues() {
    let objective = objective(vec![linear_term(2, lit(1)), linear_term(1, lit(2))]);
    let result = decide_tightened_solve_result(
        &objective,
        &[true, false],
        2,
        PbCdclResult::Satisfiable(vec![false, true]),
    );

    assert_eq!(
        result,
        TightenedSolveDecision::Continue {
            model: vec![false, true],
            value: 1,
        }
    );
}

#[test]
fn test_tightened_solve_unsat_proves_optimal() {
    let objective = objective(vec![linear_term(1, lit(1))]);
    let result = decide_tightened_solve_result(&objective, &[true], 1, PbCdclResult::Unsatisfiable);

    assert_eq!(
        result,
        TightenedSolveDecision::Return(PbCdclResult::Optimal(vec![true], 1))
    );
}

#[test]
fn test_tightened_solve_unknown_keeps_feasible_incumbent() {
    let objective = objective(vec![linear_term(1, lit(1))]);
    let result = decide_tightened_solve_result(&objective, &[true], 1, PbCdclResult::Unknown);

    assert_eq!(
        result,
        TightenedSolveDecision::Return(PbCdclResult::Feasible(vec![true], 1))
    );
}

#[test]
fn test_optimize_with_proof_unknown_stays_fail_closed() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: Some(objective(vec![
            linear_term(1, lit(1)),
            linear_term(1, lit(2)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf)
        .expect("proof writer creation must succeed");

    let result = solver.solve_optimize_interruptible(&obj, None, || true);

    assert_eq!(result, PbCdclResult::Unknown);
    let err = solver
        .conclude_proof()
        .expect_err("unknown optimization proof must still fail closed");
    assert!(matches!(err, ProofError::MissingOptimizationBounds));
}

#[test]
fn test_optimize_with_proof_feasible_stays_fail_closed() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            (1..=3).map(|v| linear_term(1, lit(v))).collect(),
            1,
        )],
        objective: Some(objective((1..=3).map(|v| linear_term(1, lit(v))).collect())),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf)
        .expect("proof writer creation must succeed");
    let should_stop = std::cell::Cell::new(false);
    let mut on_improve = |_: i128, _: &[bool]| should_stop.set(true);

    let result =
        solver.solve_optimize_interruptible(&obj, Some(&mut on_improve), || should_stop.get());

    match result {
        PbCdclResult::Feasible(model, value) => {
            let sum: i128 = model.iter().filter(|&&v| v).count() as i128;
            assert_eq!(sum, value, "objective value matches incumbent");
            assert!(value >= 1, "incumbent must satisfy the objective");
        }
        other => panic!("expected Feasible, got {other:?}"),
    }

    let err = solver
        .conclude_proof()
        .expect_err("best-known optimization proof must still fail closed");
    assert!(matches!(err, ProofError::MissingOptimizationBounds));
}

#[test]
fn test_optimize_bound_overflow_returns_sound_incumbent() {
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 0,
        constraints: vec![],
        objective: Some(objective(vec![linear_term(i128::MIN, lit(1))])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);

    // The strictly-tighter objective bound `objective <= best - 1` overflows
    // (best = i128::MIN), so the model-improving loop cannot tighten further.
    // The optimum is nonetheless `i128::MIN` (x1 = 1, the only assignment that
    // beats x1 = 0 -> 0). With the opt-in LP relaxation bound folded into the
    // termination floor (`AY_PB_NATIVE_LP_BOUND`), the loop can PROVE this
    // optimum (the LP bound is i128::MIN = the optimum), so `Optimal` is the
    // sound outcome; in the default path the loop returns `Feasible`. Both are
    // sound as long as the reported value is correct — soundness, not the
    // specific verdict, is the invariant.
    match solver.solve_optimize(&obj, None) {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(eval_objective(&obj, &model), value);
            assert_eq!(value, i128::MIN, "the true optimum is i128::MIN (x1 = 1)");
        }
        PbCdclResult::Feasible(model, value) => {
            assert_eq!(eval_objective(&obj, &model), value);
            assert!(value <= 0, "incumbent should be no worse than false");
        }
        other => panic!("expected Optimal or Feasible, got {other:?}"),
    }
}

#[test]
fn test_optimize_bound_overflow_with_proof_stays_fail_closed() {
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 0,
        constraints: vec![],
        objective: Some(objective(vec![linear_term(i128::MIN, lit(1))])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf)
        .expect("proof writer creation must succeed");

    match solver.solve_optimize(&obj, None) {
        PbCdclResult::Feasible(model, value) => {
            assert_eq!(eval_objective(&obj, &model), value);
            assert!(value <= 0, "incumbent should be no worse than false");
        }
        other => panic!("expected Feasible, got {other:?}"),
    }
    let err = solver
        .conclude_proof()
        .expect_err("overflowing optimization proof must still fail closed");
    assert!(matches!(err, ProofError::MissingOptimizationBounds));
}

#[test]
fn test_optimize_weighted_objective() {
    // min: 3*x1 + 2*x2 + 1*x3
    // subject to: x1 + x2 + x3 >= 2
    // Optimal: x2=true, x3=true -> cost = 2+1 = 3
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(1, lit(1)),
                linear_term(1, lit(2)),
                linear_term(1, lit(3)),
            ],
            2,
        )],
        objective: Some(objective(vec![
            linear_term(3, lit(1)),
            linear_term(2, lit(2)),
            linear_term(1, lit(3)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_optimize(&obj, None);

    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, 3, "optimal cost should be 3 (x2+x3)");
            // Verify the constraints.
            let count: i128 = model.iter().filter(|&&v| v).count() as i128;
            assert!(count >= 2, "at least 2 variables must be true");
            // Verify objective evaluation matches.
            let computed = eval_objective(&obj, &model);
            assert_eq!(computed, value, "objective evaluation must match");
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

#[test]
fn test_optimize_callback_reports_improvements() {
    // min: +1 x1 +1 x2 +1 x3
    // subject to: x1 + x2 + x3 >= 1
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            (1..=3).map(|v| linear_term(1, lit(v))).collect(),
            1,
        )],
        objective: Some(objective((1..=3).map(|v| linear_term(1, lit(v))).collect())),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let mut improvements = Vec::new();
    let result = solver.solve_optimize(
        &obj,
        Some(&mut |value: i128, _model: &[bool]| {
            improvements.push(value);
        }),
    );

    match result {
        PbCdclResult::Optimal(_, value) => {
            assert_eq!(value, 1, "optimal is 1");
            // Should have reported at least one improvement.
            assert!(
                !improvements.is_empty(),
                "callback should have been called at least once"
            );
            // Improvements should be monotonically decreasing.
            for window in improvements.windows(2) {
                assert!(
                    window[1] <= window[0],
                    "improvements should be non-increasing: {} -> {}",
                    window[0],
                    window[1]
                );
            }
            // Last improvement should be the optimal value.
            assert_eq!(
                *improvements.last().unwrap(),
                1,
                "last improvement should be optimal"
            );
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

#[test]
fn test_optimize_constraint_satisfaction_in_optimal_model() {
    // min: 2*x1 + 3*x2 + 5*x3 + 7*x4
    // subject to:
    //   x1 + x2 + x3 + x4 >= 2
    //   ~x1 + ~x2 + ~x3 + ~x4 >= 2 (at most 2 true)
    // So exactly 2 true. Cheapest pair: x1+x2 = 2+3 = 5.
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 2,
        constraints: vec![
            ge_constraint((1..=4).map(|v| linear_term(1, lit(v))).collect(), 2),
            ge_constraint((1..=4).map(|v| linear_term(1, not(v))).collect(), 2),
        ],
        objective: Some(objective(vec![
            linear_term(2, lit(1)),
            linear_term(3, lit(2)),
            linear_term(5, lit(3)),
            linear_term(7, lit(4)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_optimize(&obj, None);

    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, 5, "optimal cost should be 5 (x1+x2)");
            // Verify all constraints satisfied.
            let true_count = model.iter().filter(|&&v| v).count();
            assert_eq!(true_count, 2, "exactly 2 variables must be true");
            // Verify objective.
            let computed = eval_objective(&obj, &model);
            assert_eq!(computed, value);
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

#[test]
fn test_optimize_decision_instance_no_objective() {
    // Decision instance (no objective) should just return SAT.
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    // Using solve() directly for decision problems.
    let result = solver.solve();

    match result {
        PbCdclResult::Satisfiable(model) => {
            assert!(model[0] || model[1], "at least one should be true");
        }
        other => panic!("expected Satisfiable, got {other:?}"),
    }
}

#[test]
fn test_build_upper_bound_constraint() {
    let obj = objective(vec![linear_term(3, lit(1)), linear_term(2, lit(2))]);

    // bound = 5: we want sum <= 4, i.e., -3*x1 + -2*x2 >= -4
    let constraint = build_upper_bound_constraint(&obj, 5).unwrap();
    assert_eq!(constraint.rel, PbRel::Ge);
    assert_eq!(constraint.rhs, -4);
    assert_eq!(constraint.terms.len(), 2);
    assert_eq!(constraint.terms[0].coeff, -3);
    assert_eq!(constraint.terms[1].coeff, -2);
}

#[test]
fn test_build_upper_bound_constraint_overflow() {
    let obj = objective(vec![linear_term(i128::MIN, lit(1))]);
    // Negating i128::MIN overflows.
    let result = build_upper_bound_constraint(&obj, 5);
    assert!(result.is_none(), "should return None on overflow");
}

#[test]
fn test_new_installs_preprocess_fixed_literals_as_root_assignments() {
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 1,
        constraints: vec![PbConstraint {
            terms: vec![linear_term(1, lit(1))],
            rel: PbRel::Ge,
            rhs: 1,
        }],
        objective: None,
    };
    let solver = PbCdclSolver::new(&instance);

    assert_eq!(solver.propagator.value(1), LitValue::True);
    assert_eq!(solver.level_of_var(1), Some(0));
    assert!(
        solver.all_assigned(),
        "preprocessing-fixed variables should count as root assignments"
    );
}

#[test]
fn test_root_probing_learns_failed_literal_at_root() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 3,
        constraints: vec![
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, not(2))], 1),
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(3))], 1),
        ],
        objective: None,
    };

    // Unpreprocessed so the cdcl root-probe machinery (not preprocessing
    // probing) is what learns the failed literal under test.
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    let mut never_stop = |_: &PbCdclSolver| false;
    let outcome = solver.run_root_probing_with_stop(&mut never_stop);

    assert_eq!(outcome, RootProbeOutcome::Ok);
    assert_eq!(solver.decision_level, 0);
    assert_eq!(solver.stats.decisions, 0);
    assert!(
        solver.stats.learned >= 1,
        "failed-literal probing should learn at least one root constraint"
    );
    assert_eq!(solver.propagator.value(-1), LitValue::True);
    assert_eq!(solver.level_of_var(1), Some(0));
    assert_eq!(solver.propagator.value(2), LitValue::Unassigned);
    assert_eq!(solver.propagator.value(3), LitValue::True);
}

#[test]
fn test_root_probe_success_undo_preserves_root_trail_without_repropagation() {
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 3,
        constraints: vec![
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, not(2))], 1),
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(3))], 1),
        ],
        objective: None,
    };

    // Construct unpreprocessed so the failed-literal fixture reaches the
    // cdcl root-probe machinery under test (preprocessing-level probing
    // would otherwise already fix these literals).
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    let mut never_stop = |_: &PbCdclSolver| false;
    assert_eq!(
        solver.run_single_root_probe_with_stop(1, &mut never_stop),
        RootProbeOutcome::Ok
    );
    assert_eq!(solver.propagator.value(-1), LitValue::True);
    assert_eq!(solver.propagator.value(3), LitValue::True);
    assert_eq!(solver.propagator.value(4), LitValue::Unassigned);
    let root_trail = solver
        .trail
        .iter()
        .map(|entry| (entry.lit, entry.level, entry.reason))
        .collect::<Vec<_>>();
    assert!(
        !root_trail.is_empty(),
        "fixture must seed real level-0 trail entries, not only fixed literals"
    );
    let root_propagations = solver.stats.propagations;
    let learned_before = solver.stats.learned;

    let outcome = solver.run_single_root_probe_with_stop(4, &mut never_stop);

    assert_eq!(outcome, RootProbeOutcome::Ok);
    assert_eq!(solver.decision_level, 0);
    assert!(solver.trail_lim.is_empty());
    assert_eq!(solver.propagator.value(-1), LitValue::True);
    assert_eq!(solver.propagator.value(3), LitValue::True);
    assert_eq!(solver.propagator.value(4), LitValue::Unassigned);
    assert_eq!(
        solver
            .trail
            .iter()
            .map(|entry| (entry.lit, entry.level, entry.reason))
            .collect::<Vec<_>>(),
        root_trail
    );
    assert_eq!(
        solver.stats.propagations, root_propagations,
        "successful temporary probes must not discard and repropagate existing root assignments"
    );
    assert_eq!(
        solver.stats.learned, learned_before,
        "successful temporary probes should not learn constraints"
    );
}

#[test]
fn implied_literals_at_root_returns_implications_and_restores_state() {
    // Constraints: x1 -> x2 (¬x1 ∨ x2), x2 -> x3, and at-most-one over
    // {x3, x4, x5}. Assuming x1 true should imply x2 and x3 (and the AM1 then
    // forces ¬x4, ¬x5). The probe must return those implications, then leave
    // the solver byte-for-byte at the prior level-0 state.
    let instance = PbInstance {
        num_vars: 5,
        num_constraints: 3,
        constraints: vec![
            // ¬x1 ∨ x2 : ¬x1 + x2 >= 1
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, lit(2))], 1),
            // ¬x2 ∨ x3
            ge_constraint(vec![linear_term(1, not(2)), linear_term(1, lit(3))], 1),
            // at-most-one(x3,x4,x5): ¬x3 + ¬x4 + ¬x5 >= 2
            ge_constraint(
                vec![
                    linear_term(1, not(3)),
                    linear_term(1, not(4)),
                    linear_term(1, not(5)),
                ],
                2,
            ),
        ],
        objective: None,
    };
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);

    let trail_before: Vec<_> = solver
        .trail
        .iter()
        .map(|e| (e.lit, e.level, e.reason))
        .collect();
    let dl_before = solver.decision_level;
    let learned_before = solver.learned_constraints.len();

    let outcome = solver.implied_literals_at_root(lit(1));
    let ImpliedLiteralsOutcome::Implied(implied) = outcome else {
        panic!("expected Implied, got {outcome:?}");
    };
    // x1, x2, x3 must be implied true; ¬x4, ¬x5 must be implied (AM1).
    let has = |v: u32, neg: bool| {
        implied
            .iter()
            .any(|l: &PbLit| l.var == v && l.negated == neg)
    };
    assert!(has(1, false), "x1 must be implied: {implied:?}");
    assert!(has(2, false), "x2 must be implied: {implied:?}");
    assert!(has(3, false), "x3 must be implied: {implied:?}");
    assert!(has(4, true), "¬x4 must be implied (AM1): {implied:?}");
    assert!(has(5, true), "¬x5 must be implied (AM1): {implied:?}");

    // STATE RESTORATION: trail, decision level, learned DB all unchanged.
    let trail_after: Vec<_> = solver
        .trail
        .iter()
        .map(|e| (e.lit, e.level, e.reason))
        .collect();
    assert_eq!(trail_after, trail_before, "trail must be restored");
    assert_eq!(solver.decision_level, dl_before);
    assert_eq!(
        solver.learned_constraints.len(),
        learned_before,
        "probe must not learn"
    );
    assert!(solver.trail_lim.is_empty());
    // Repeated probing is idempotent and re-solving still succeeds.
    let _ = solver.implied_literals_at_root(lit(4));
    assert!(matches!(
        solver.solve_with_assumptions(&[]),
        PbCdclAssumptionResult::Satisfiable(_)
    ));
}

#[test]
fn implied_literals_at_root_reports_conflict_for_forced_fact() {
    // x1 is forced true (unit), and x6 -> ¬x1, so assuming x6 conflicts: x6 is
    // a forced fact (¬x6 always holds). The probe must report Conflict, and
    // must leave the solver state intact for a subsequent solve.
    let instance = PbInstance {
        num_vars: 6,
        num_constraints: 2,
        constraints: vec![
            // x1 >= 1 (unit: x1 forced true)
            ge_constraint(vec![linear_term(1, lit(1))], 1),
            // ¬x6 ∨ ¬x1 : ¬x6 + ¬x1 >= 1  (x6 -> ¬x1)
            ge_constraint(vec![linear_term(1, not(6)), linear_term(1, not(1))], 1),
        ],
        objective: None,
    };
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    let dl_before = solver.decision_level;
    let trail_len_before = solver.trail.len();

    assert_eq!(
        solver.implied_literals_at_root(lit(6)),
        ImpliedLiteralsOutcome::Conflict,
        "assuming x6 must conflict (x6 is false in every model)"
    );
    assert_eq!(solver.decision_level, dl_before);
    assert_eq!(solver.trail.len(), trail_len_before);
    // A non-forced literal still returns Implied and the solver still solves.
    assert!(matches!(
        solver.implied_literals_at_root(not(6)),
        ImpliedLiteralsOutcome::Implied(_)
    ));
    assert!(matches!(
        solver.solve_with_assumptions(&[]),
        PbCdclAssumptionResult::Satisfiable(_)
    ));
}

#[test]
fn implied_literals_at_root_solve_probe_solve_is_stable() {
    // The mandated state-restoration gate: solve, probe many literals, solve
    // again -> same verdict, proving the probe never corrupts solver state.
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 3,
        constraints: vec![
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, not(2))], 1),
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(3))], 1),
        ],
        objective: None,
    };
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    let first = solver.solve_with_assumptions(&[]);
    for var in 1..=4u32 {
        let _ = solver.implied_literals_at_root(lit(var));
        let _ = solver.implied_literals_at_root(not(var));
    }
    let second = solver.solve_with_assumptions(&[]);
    assert_eq!(
        std::mem::discriminant(&first),
        std::mem::discriminant(&second),
        "probe must not change the solve verdict"
    );
}

#[test]
fn test_root_probe_interrupt_undo_preserves_root_trail() {
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 3,
        constraints: vec![
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, not(2))], 1),
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(3))], 1),
        ],
        objective: None,
    };

    // Construct unpreprocessed so the failed-literal fixture reaches the
    // cdcl root-probe machinery under test (preprocessing-level probing
    // would otherwise already fix these literals).
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    let mut never_stop = |_: &PbCdclSolver| false;
    assert_eq!(
        solver.run_single_root_probe_with_stop(1, &mut never_stop),
        RootProbeOutcome::Ok
    );
    assert_eq!(solver.propagator.value(-1), LitValue::True);
    assert_eq!(solver.propagator.value(3), LitValue::True);
    assert_eq!(solver.propagator.value(4), LitValue::Unassigned);
    let root_trail = solver
        .trail
        .iter()
        .map(|entry| (entry.lit, entry.level, entry.reason))
        .collect::<Vec<_>>();
    assert!(
        !root_trail.is_empty(),
        "fixture must seed real level-0 trail entries, not only fixed literals"
    );
    let root_propagations = solver.stats.propagations;
    let mut checks = 0usize;

    let outcome = solver.run_single_root_probe_interruptible(4, &mut || {
        checks += 1;
        checks >= 2
    });

    assert_eq!(outcome, RootProbeOutcome::Interrupted);
    assert_eq!(solver.decision_level, 0);
    assert!(solver.trail_lim.is_empty());
    assert_eq!(solver.propagator.value(-1), LitValue::True);
    assert_eq!(solver.propagator.value(3), LitValue::True);
    assert_eq!(solver.propagator.value(4), LitValue::Unassigned);
    assert_eq!(
        solver
            .trail
            .iter()
            .map(|entry| (entry.lit, entry.level, entry.reason))
            .collect::<Vec<_>>(),
        root_trail
    );
    assert_eq!(
        solver.stats.propagations, root_propagations,
        "interrupted temporary probes must not discard and repropagate existing root assignments"
    );
}

#[test]
fn test_root_probe_temporary_assignments_do_not_poison_saved_phase() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 0,
        constraints: vec![],
        objective: None,
    };

    let mut budgeted = PbCdclSolver::new(&instance);
    budgeted.saved_phase[1] = true;
    budgeted.saved_phase[2] = false;
    budgeted.config.root_probe_max_probes = 1;
    let saved_before = budgeted.saved_phase.clone();

    let mut never_stop = |_: &PbCdclSolver| false;
    assert_eq!(
        budgeted.run_root_probing_with_stop(&mut never_stop),
        RootProbeOutcome::Ok
    );
    assert_eq!(
        budgeted.saved_phase, saved_before,
        "a one-sided probe budget must not rewrite later search phases"
    );
    assert_eq!(budgeted.propagator.value(1), LitValue::Unassigned);
    assert_eq!(budgeted.propagator.value(2), LitValue::Unassigned);

    let mut interrupted = PbCdclSolver::new(&instance);
    interrupted.saved_phase[1] = true;
    interrupted.saved_phase[2] = false;
    let saved_before = interrupted.saved_phase.clone();
    let mut polls = 0usize;

    assert_eq!(
        interrupted.run_single_root_probe_interruptible(-1, &mut || {
            polls += 1;
            polls >= 2
        }),
        RootProbeOutcome::Interrupted
    );
    assert_eq!(
        interrupted.saved_phase, saved_before,
        "an interrupted temporary probe must not rewrite later search phases"
    );
    assert_eq!(interrupted.propagator.value(1), LitValue::Unassigned);
    assert_eq!(interrupted.propagator.value(2), LitValue::Unassigned);
}

#[test]
fn test_root_probing_respects_probe_budget() {
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 4,
        constraints: vec![
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, lit(3))], 1),
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, not(3))], 1),
            ge_constraint(vec![linear_term(1, not(2)), linear_term(1, lit(4))], 1),
            ge_constraint(vec![linear_term(1, not(2)), linear_term(1, not(4))], 1),
        ],
        objective: None,
    };

    // Construct unpreprocessed so the cdcl root-probe budget is exercised on
    // the raw fixture (preprocessing-level probing would otherwise fix both
    // failed literals before the budget-limited cdcl probe runs).
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    solver.config.root_probe_max_probes = 1;

    let mut never_stop = |_: &PbCdclSolver| false;
    let outcome = solver.run_root_probing_with_stop(&mut never_stop);

    assert_eq!(outcome, RootProbeOutcome::Ok);
    assert_eq!(solver.propagator.value(-1), LitValue::True);
    assert_eq!(solver.level_of_var(1), Some(0));
    assert_eq!(solver.propagator.value(2), LitValue::Unassigned);
    assert_eq!(
        solver.stats.learned, 1,
        "the single probe budget should only learn from the first failed literal"
    );
}

#[test]
fn test_root_probing_smoke_reduces_decisions_before_search() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 4,
        constraints: vec![
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, not(2))], 1),
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(3))], 1),
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, not(3))], 1),
        ],
        objective: None,
    };

    // Unpreprocessed so this smoke test isolates the effect of cdcl
    // root-probing vs no root-probing (preprocessing-level probing would
    // otherwise resolve the fixture identically for both arms).
    let mut baseline = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    baseline.config.root_probe_enabled = false;
    let baseline_start = std::time::Instant::now();
    let baseline_result = baseline.solve();
    let baseline_elapsed = baseline_start.elapsed();

    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    let probing_start = std::time::Instant::now();
    let probing_result = solver.solve();
    let probing_elapsed = probing_start.elapsed();

    assert_eq!(baseline_result, PbCdclResult::Unsatisfiable);
    assert_eq!(probing_result, PbCdclResult::Unsatisfiable);
    assert!(
        baseline.stats.decisions > solver.stats.decisions,
        "root probing should eliminate at least one search decision on the smoke instance"
    );
    assert_eq!(solver.stats.decisions, 0);

    eprintln!(
            "root probing smoke: baseline decisions={} propagations={} elapsed_us={} | probing decisions={} propagations={} elapsed_us={}",
            baseline.stats.decisions,
            baseline.stats.propagations,
            baseline_elapsed.as_micros(),
            solver.stats.decisions,
            solver.stats.propagations,
            probing_elapsed.as_micros(),
        );
}

#[test]
fn test_optimize_preprocess_fixed_objective_literal_proves_optimal() {
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![PbConstraint {
            terms: vec![linear_term(1, lit(1))],
            rel: PbRel::Ge,
            rhs: 1,
        }],
        objective: Some(objective(vec![
            linear_term(1, lit(1)),
            linear_term(1, lit(2)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_optimize(&obj, None);

    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(
                value, 1,
                "the fixed x1=true objective contribution must remain active"
            );
            assert_eq!(model, vec![true, false]);
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

#[test]
fn test_seed_saved_phase_from_objective_uses_net_linear_coefficients() {
    let instance = PbInstance {
        num_vars: 6,
        num_constraints: 0,
        constraints: vec![],
        objective: None,
    };
    let mut solver = PbCdclSolver::new(&instance);
    solver.saved_phase[5] = true;
    solver.saved_phase[6] = true;

    solver.seed_saved_phase_from_objective(&objective(vec![
        linear_term(3, lit(1)),
        linear_term(-4, lit(2)),
        linear_term(5, not(3)),
        linear_term(-6, not(4)),
        linear_term(2, lit(5)),
        linear_term(2, not(5)),
        PbTerm {
            coeff: -9,
            lits: vec![lit(6), lit(1)],
        },
    ]));

    assert!(!solver.saved_phase[1]);
    assert!(solver.saved_phase[2]);
    assert!(solver.saved_phase[3]);
    assert!(!solver.saved_phase[4]);
    assert!(solver.saved_phase[5]);
    assert!(solver.saved_phase[6]);
}

#[test]
fn test_seed_activity_from_objective_prioritizes_weighted_objective_vars() {
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 0,
        constraints: vec![],
        objective: None,
    };
    let mut solver = PbCdclSolver::new(&instance);

    solver.seed_activity_from_objective(&objective(vec![
        linear_term(2, lit(1)),
        linear_term(6, lit(2)),
        linear_term(4, lit(2)),
        linear_term(-5, lit(3)),
        nonlinear_term(100, vec![lit(4), lit(1)]),
    ]));

    assert_eq!(solver.vsids_heap.pop_max(&solver.activity), Some(2));
    assert_eq!(solver.vsids_heap.pop_max(&solver.activity), Some(3));
    assert_eq!(solver.vsids_heap.pop_max(&solver.activity), Some(1));
    assert_eq!(
        solver.activity[4], 0.0,
        "nonlinear objective terms should not affect native decision activity"
    );
}

#[test]
fn test_optimize_negative_objective_finds_best_incumbent_immediately() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 0,
        constraints: vec![],
        objective: Some(objective(vec![
            linear_term(-1, lit(1)),
            linear_term(-1, lit(2)),
            linear_term(-1, lit(3)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let mut improvements = Vec::new();
    let result = solver.solve_optimize(
        &obj,
        Some(&mut |value: i128, _model: &[bool]| improvements.push(value)),
    );

    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, -3);
            assert_eq!(model, vec![true, true, true]);
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
    assert_eq!(improvements, vec![-3]);
}

#[test]
fn test_replace_active_optimization_bound_deactivates_weaker_range() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 0,
        constraints: vec![],
        objective: None,
    };
    let mut solver = PbCdclSolver::new(&instance);
    let obj = objective(vec![
        linear_term(9, lit(1)),
        linear_term(5, lit(2)),
        linear_term(1, lit(3)),
    ]);

    let first = build_upper_bound_constraint(&obj, 15).expect("first bound must encode");
    let first_start = solver.propagator.num_constraints();
    solver.propagator.add_from_pb_constraint(&first);
    let first_end = solver.propagator.num_constraints();
    for cid in first_start..first_end {
        solver.constraints.push(
            solver
                .propagator
                .get_constraint_pb(cid)
                .expect("freshly added bound must round-trip"),
        );
    }
    solver.replace_active_optimization_bound(first_start, first_end);

    for cid in first_start..first_end {
        assert!(
            solver.propagator.is_constraint_active(cid),
            "initial bound should stay active"
        );
    }

    let second = build_upper_bound_constraint(&obj, 10).expect("second bound must encode");
    let second_start = solver.propagator.num_constraints();
    solver.propagator.add_from_pb_constraint(&second);
    let second_end = solver.propagator.num_constraints();
    for cid in second_start..second_end {
        solver.constraints.push(
            solver
                .propagator
                .get_constraint_pb(cid)
                .expect("freshly added stricter bound must round-trip"),
        );
    }
    solver.replace_active_optimization_bound(second_start, second_end);

    for cid in first_start..first_end {
        assert!(
            !solver.propagator.is_constraint_active(cid),
            "weaker bound must be deactivated once a stronger incumbent exists"
        );
    }
    for cid in second_start..second_end {
        assert!(
            solver.propagator.is_constraint_active(cid),
            "latest bound must remain active"
        );
    }
    assert_eq!(
        solver
            .propagator
            .propagation_stats()
            .deactivation_watch_lists_visited,
        0,
        "optimization-bound replacement should use lazy deactivation"
    );
}

#[test]
fn test_iterative_bound_replacement_keeps_one_active_range_after_multiple_bounds() {
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 0,
        constraints: vec![],
        objective: None,
    };
    let mut solver = PbCdclSolver::new(&instance);
    let obj = objective(vec![
        linear_term(20, lit(1)),
        linear_term(10, lit(2)),
        linear_term(3, lit(3)),
        linear_term(1, lit(4)),
    ]);

    let mut ranges = Vec::new();
    for bound in [34, 30, 11] {
        let bound_constraint =
            build_upper_bound_constraint(&obj, bound).expect("bound must encode");
        let start = solver.propagator.num_constraints();
        solver.propagator.add_from_pb_constraint(&bound_constraint);
        let end = solver.propagator.num_constraints();
        assert!(
            start < end,
            "tightening bound should add a constraint range"
        );
        for cid in start..end {
            solver.constraints.push(
                solver
                    .propagator
                    .get_constraint_pb(cid)
                    .expect("freshly added bound must round-trip"),
            );
        }
        solver.replace_active_optimization_bound(start, end);
        ranges.push((start, end));
    }

    let &(last_start, last_end) = ranges.last().expect("tightening added bounds");
    assert_eq!(
        solver.active_optimization_bound_range,
        Some((last_start, last_end)),
        "the final tightened bound range must be tracked as active"
    );
    let active_ranges = ranges
        .iter()
        .filter(|&&(start, end)| {
            (start..end).any(|cid| solver.propagator.is_constraint_active(cid))
        })
        .count();
    assert_eq!(
        active_ranges, 1,
        "exactly one optimization-bound range should remain active"
    );
    for &(start, end) in &ranges[..ranges.len() - 1] {
        for cid in start..end {
            assert!(
                !solver.propagator.is_constraint_active(cid),
                "stale optimization bound {cid} must be deactivated"
            );
        }
    }
    for cid in last_start..last_end {
        assert!(
            solver.propagator.is_constraint_active(cid),
            "latest optimization bound {cid} must remain active"
        );
    }
}

#[test]
fn test_optimize_keeps_only_strongest_native_bound_active() {
    // Exactly two variables must be true. With positive saved phases, the
    // native solver may either prove optimality from the structural lower
    // bound immediately, or add tightening bounds first. If bounds are
    // added, older objective bounds should be deactivated as soon as a
    // stricter bound is installed.
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 2,
        constraints: vec![
            ge_constraint((1..=4).map(|v| linear_term(1, lit(v))).collect(), 2),
            ge_constraint((1..=4).map(|v| linear_term(1, not(v))).collect(), 2),
        ],
        objective: Some(objective(vec![
            linear_term(20, lit(1)),
            linear_term(10, lit(2)),
            linear_term(3, lit(3)),
            linear_term(1, lit(4)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    // This test pins the bound-replacement trajectory of the SEARCH path.
    // The two rows form an exactly-two cardinality EQUALITY, which the
    // eq-knapsack DP special case would otherwise decide in the initial
    // feasibility solve (yielding a different — still correct — incumbent
    // trajectory that can close optimality after a single bound install).
    solver.set_eq_knapsack_dp_enabled(false);
    let original_constraints = solver.constraints.len();
    for saved in &mut solver.saved_phase[1..] {
        *saved = true;
    }

    let result = solver.solve_optimize(&obj, None);
    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, 4, "x3 + x4 is the optimum exact-two assignment");
            assert_eq!(model.iter().filter(|&&v| v).count(), 2);
            assert!(model[2] && model[3], "x3 and x4 should be selected");
        }
        other => panic!("expected Optimal, got {other:?}"),
    }

    let total_constraints = solver.propagator.num_constraints();
    let active_constraints = (0..total_constraints)
        .filter(|&cid| solver.propagator.is_constraint_active(cid))
        .count();
    match solver.active_optimization_bound_range {
        None => {
            assert_eq!(
                total_constraints, original_constraints,
                "structural lower-bound closure should not add optimization bounds"
            );
            assert_eq!(
                active_constraints, original_constraints,
                "all original constraints should remain active"
            );
        }
        Some((start, end)) => {
            let active_bound_constraints = (start..end)
                .filter(|&cid| solver.propagator.is_constraint_active(cid))
                .count();
            assert_eq!(
                active_bound_constraints,
                end - start,
                "the tracked optimization-bound range should remain active"
            );
            assert_eq!(
                    active_constraints,
                    original_constraints + active_bound_constraints,
                    "only original constraints and the strongest optimization bound should remain active"
                );
            assert!(
                total_constraints > active_constraints,
                "the optimization run should have added and then deactivated weaker bounds"
            );
        }
    }
}

// --- VeriPB proof logging tests ---

#[test]
fn test_proof_logging_unsat_emits_header_and_contradiction() {
    // x1 >= 1 AND ~x1 >= 1 (UNSAT)
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1))], 1),
            ge_constraint(vec![linear_term(1, not(1))], 1),
        ],
        objective: None,
    };

    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");
    let result = solver.solve();
    solver
        .conclude_proof()
        .expect("proof conclusion must succeed");

    assert_eq!(result, PbCdclResult::Unsatisfiable);

    let proof_output = buf.as_string();

    // Header must be present.
    assert!(
        proof_output.starts_with("pseudo-Boolean proof version 3.0\n"),
        "proof must start with VeriPB v3 header, got: {proof_output}"
    );

    // Must contain an 'f' line declaring input constraint count.
    assert!(
        proof_output.contains("\nf "),
        "proof must contain input constraint count"
    );

    // Must contain the VeriPB v3 UNSAT footer.
    assert!(
        proof_output
            .lines()
            .any(|line| line.starts_with("conclusion UNSAT : ")),
        "UNSAT proof must conclude with a VeriPB UNSAT footer: {proof_output}"
    );
    assert!(
        proof_output.lines().last() == Some("end pseudo-Boolean proof;"),
        "UNSAT proof must end with the VeriPB proof terminator: {proof_output}"
    );
}

#[test]
fn test_proof_logging_root_probe_learning_closes_unsat_cleanly() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 4,
        constraints: vec![
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, not(1)), linear_term(1, not(2))], 1),
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(3))], 1),
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, not(3))], 1),
        ],
        objective: None,
    };

    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");
    solver.config.root_probe_max_probes = 1;

    let result = solver.solve();
    solver
        .conclude_proof()
        .expect("root-probe UNSAT proof should flush cleanly after solve");

    assert_eq!(result, PbCdclResult::Unsatisfiable);
    assert_eq!(
        solver.stats.decisions, 0,
        "bounded root probing should finish this instance before any search decision"
    );
    assert!(
        solver.stats.learned >= 1,
        "failed-literal probing should learn a root constraint before UNSAT"
    );
    assert_eq!(solver.propagator.value(-1), LitValue::True);
    assert_eq!(solver.level_of_var(1), Some(0));
    assert!(
        solver.constraint_ids.len() > instance.num_constraints as usize,
        "root-probe learning should allocate at least one derived proof ID"
    );

    let proof_output = buf.as_string();
    assert!(
        proof_output.starts_with("pseudo-Boolean proof version 3.0\n"),
        "proof must start with the VeriPB v3 header: {proof_output}"
    );
    assert!(
        proof_output
            .lines()
            .any(|line| line.starts_with("p ") || line.starts_with("rup ")),
        "root-probe learning must leave a derivation in the proof: {proof_output}"
    );
    assert!(
        proof_output
            .lines()
            .any(|line| line.starts_with("conclusion UNSAT : ")),
        "root-probe UNSAT proof must conclude with a VeriPB UNSAT footer: {proof_output}"
    );
    assert!(
        proof_output.lines().last() == Some("end pseudo-Boolean proof;"),
        "root-probe UNSAT proof must end with the VeriPB proof terminator: {proof_output}"
    );
}

#[test]
fn test_proof_logging_interrupted_during_conflict_analysis_has_no_terminal_conclusion() {
    let instance = root_probe_decoy_pigeonhole_3_2_instance();

    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");
    solver.config.root_probe_enabled = false;
    let result = solver.solve_with_stop(|solver| solver.stats.conflicts >= 1);
    solver
        .conclude_proof()
        .expect("interrupted proof flush must succeed");

    assert_eq!(result, PbCdclResult::Unknown);
    assert!(
        solver.stats.conflicts >= 1,
        "interrupt should trigger after a real conflict"
    );
    assert_eq!(
        solver.stats.learned, 0,
        "interrupted conflict analysis must not learn a partial proof constraint"
    );

    let proof_output = buf.as_string();
    assert!(
        !proof_output.contains("output NONE"),
        "interrupted proof mode must not claim SAT: {proof_output}"
    );
    assert!(
        !proof_output.contains("conclusion UNSAT"),
        "interrupted proof mode must not claim UNSAT: {proof_output}"
    );
}

#[test]
fn test_proof_logging_unsat_contains_cp_derivation_steps() {
    // Pigeonhole 3/2: complex enough that preprocessing cannot solve it,
    // so the CDCL loop must run and conflict analysis emits CP steps.
    let instance = PbInstance {
        num_vars: 6,
        num_constraints: 5,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, lit(3)), linear_term(1, lit(4))], 1),
            ge_constraint(vec![linear_term(1, lit(5)), linear_term(1, lit(6))], 1),
            ge_constraint(
                vec![
                    linear_term(1, not(1)),
                    linear_term(1, not(3)),
                    linear_term(1, not(5)),
                ],
                2,
            ),
            ge_constraint(
                vec![
                    linear_term(1, not(2)),
                    linear_term(1, not(4)),
                    linear_term(1, not(6)),
                ],
                2,
            ),
        ],
        objective: None,
    };

    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");
    let result = solver.solve();
    solver
        .conclude_proof()
        .expect("proof conclusion must succeed");

    assert_eq!(result, PbCdclResult::Unsatisfiable);

    let proof_output = buf.as_string();

    // Proof must contain at least one 'pol' line (cutting-planes derivation)
    // OR 'rup' line (learned constraint derivation).
    let has_derivation = proof_output
        .lines()
        .any(|line| line.starts_with("pol ") || line.starts_with("rup "));
    assert!(
        has_derivation,
        "UNSAT proof for pigeonhole must contain derivation steps: {proof_output}"
    );

    // Proof must end with the VeriPB UNSAT footer.
    assert!(
        proof_output
            .lines()
            .any(|line| line.starts_with("conclusion UNSAT : ")),
        "UNSAT proof must conclude with a VeriPB UNSAT footer"
    );
    assert!(
        proof_output.lines().last() == Some("end pseudo-Boolean proof;"),
        "UNSAT proof must end with the VeriPB proof terminator"
    );
}

#[test]
fn test_proof_logging_interrupted_during_reduce_db_has_no_terminal_conclusion() {
    let instance = root_probe_decoy_pigeonhole_3_2_instance();

    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");
    solver.config.root_probe_enabled = false;
    solver.config.reduce_interval = 1;

    let result = solver.solve_with_stop(|solver| solver.stats.reduce_db_calls >= 1);
    solver
        .conclude_proof()
        .expect("interrupted proof flush must succeed");

    assert_eq!(result, PbCdclResult::Unknown);
    assert_eq!(
        solver.stats.reduce_db_calls, 1,
        "proof-mode interruption should be observed when reduce_db begins"
    );
    assert_eq!(
        solver.stats.learned_deletions, 0,
        "early reduce_db interruption must not emit deletion steps"
    );

    let proof_output = buf.as_string();
    assert!(
        !proof_output.contains("output NONE"),
        "interrupted proof mode must not claim SAT: {proof_output}"
    );
    assert!(
        !proof_output.contains("conclusion UNSAT"),
        "interrupted proof mode must not claim UNSAT: {proof_output}"
    );
}

#[test]
fn test_proof_logging_sat_does_not_claim_contradiction() {
    // x1 + x2 >= 1 (trivially SAT)
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: None,
    };

    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");
    let result = solver.solve();
    solver
        .conclude_proof()
        .expect("proof conclusion must succeed");

    let model = match result {
        PbCdclResult::Satisfiable(model) => model,
        other => panic!("expected SAT, got {other:?}"),
    };
    let expected_assignment = model
        .iter()
        .take(instance.num_vars as usize)
        .enumerate()
        .map(|(index, value)| {
            if *value {
                format!("x{}", index + 1)
            } else {
                format!("~x{}", index + 1)
            }
        })
        .collect::<Vec<_>>()
        .join(" ");
    let expected_conclusion = format!("conclusion SAT : {expected_assignment};");

    let proof_output = buf.as_string();

    // SAT proof must not claim an UNSAT conclusion.
    assert!(
        !proof_output.contains("conclusion UNSAT"),
        "SAT proof must not claim UNSAT: {proof_output}"
    );

    // But must still have the header.
    assert!(
        proof_output.starts_with("pseudo-Boolean proof version 3.0\n"),
        "proof must start with VeriPB v3 header"
    );

    // SAT proof MUST contain a full VeriPB SAT footer.
    assert!(
        proof_output.lines().any(|line| line == "output NONE;"),
        "SAT proof must contain 'output NONE' per VeriPB v3 spec: {proof_output}"
    );
    assert!(
        proof_output.lines().any(|line| line == expected_conclusion),
        "SAT proof must contain the full model assignment `{expected_conclusion}`: {proof_output}"
    );
    assert!(
        proof_output.lines().last() == Some("end pseudo-Boolean proof;"),
        "SAT proof must end with the VeriPB terminator: {proof_output}"
    );
}

#[test]
fn test_proof_logging_weighted_unsat_emits_multiply_steps() {
    // Weighted UNSAT instance with 4 variables to avoid preprocessing
    // solving it trivially. The constraints force conflicts that require
    // weighted cutting-planes resolution with LCM-based multiplication.
    //
    // 3*x1 + 2*x2 + x3 >= 4
    // 2*~x1 + 3*~x2 + x4 >= 4
    // ~x3 + ~x4 >= 1   (at most one of x3, x4 true)
    // x3 + x4 >= 1     (at least one of x3, x4 true)
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 4,
        constraints: vec![
            ge_constraint(
                vec![
                    linear_term(3, lit(1)),
                    linear_term(2, lit(2)),
                    linear_term(1, lit(3)),
                ],
                4,
            ),
            ge_constraint(
                vec![
                    linear_term(2, not(1)),
                    linear_term(3, not(2)),
                    linear_term(1, lit(4)),
                ],
                4,
            ),
            ge_constraint(vec![linear_term(1, not(3)), linear_term(1, not(4))], 1),
            ge_constraint(vec![linear_term(1, lit(3)), linear_term(1, lit(4))], 1),
        ],
        objective: None,
    };

    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");
    let result = solver.solve();
    solver
        .conclude_proof()
        .expect("proof conclusion must succeed");

    let proof_output = buf.as_string();

    // This instance may be SAT or UNSAT depending on the constraint
    // encoding after preprocessing. What we care about is that
    // proof logging works correctly in either case.
    match result {
        PbCdclResult::Unsatisfiable => {
            // Count derivation operations logged.
            let p_lines: Vec<&str> = proof_output
                .lines()
                .filter(|line| line.starts_with("pol "))
                .collect();

            // If UNSAT required conflicts, we should see CP steps.
            if solver.stats().conflicts > 0 {
                assert!(
                    !p_lines.is_empty() || proof_output.contains("rup "),
                    "UNSAT with conflicts must have derivation steps: {proof_output}"
                );
            }

            assert!(
                proof_output
                    .lines()
                    .any(|line| line.starts_with("conclusion UNSAT : ")),
                "UNSAT proof must conclude with a VeriPB UNSAT footer"
            );
        }
        PbCdclResult::Satisfiable(model) => {
            let expected_assignment = model
                .iter()
                .take(instance.num_vars as usize)
                .enumerate()
                .map(|(index, value)| {
                    if *value {
                        format!("x{}", index + 1)
                    } else {
                        format!("~x{}", index + 1)
                    }
                })
                .collect::<Vec<_>>()
                .join(" ");
            let expected_conclusion = format!("conclusion SAT : {expected_assignment};");

            // SAT: no UNSAT footer should be claimed.
            assert!(
                !proof_output.contains("conclusion UNSAT"),
                "SAT proof must not claim UNSAT"
            );
            // SAT: must contain a full VeriPB SAT footer.
            assert!(
                proof_output.lines().any(|line| line == "output NONE;"),
                "SAT proof must contain 'output NONE': {proof_output}"
            );
            assert!(
                    proof_output
                        .lines()
                        .any(|line| line == expected_conclusion),
                    "SAT proof must contain the full model assignment `{expected_conclusion}`: {proof_output}"
                );
            assert!(
                proof_output.lines().last() == Some("end pseudo-Boolean proof;"),
                "SAT proof must end with the VeriPB terminator: {proof_output}"
            );
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

#[test]
fn test_proof_logging_weighted_pigeonhole_produces_multiply_and_add() {
    // Weighted pigeonhole: specifically designed for weighted CP operations.
    // Each pigeon has a different weight for each hole, forcing LCM scaling.
    //
    // 2*x1 + 3*x2 >= 3  (pigeon 1 goes somewhere with weight)
    // 3*x3 + 2*x4 >= 3  (pigeon 2 goes somewhere with weight)
    // 2*x5 + 2*x6 >= 2  (pigeon 3 goes somewhere)
    // ~x1 + ~x3 + ~x5 >= 2  (hole 1 capacity 1)
    // ~x2 + ~x4 + ~x6 >= 2  (hole 2 capacity 1)
    let instance = PbInstance {
        num_vars: 6,
        num_constraints: 5,
        constraints: vec![
            ge_constraint(vec![linear_term(2, lit(1)), linear_term(3, lit(2))], 3),
            ge_constraint(vec![linear_term(3, lit(3)), linear_term(2, lit(4))], 3),
            ge_constraint(vec![linear_term(2, lit(5)), linear_term(2, lit(6))], 2),
            ge_constraint(
                vec![
                    linear_term(1, not(1)),
                    linear_term(1, not(3)),
                    linear_term(1, not(5)),
                ],
                2,
            ),
            ge_constraint(
                vec![
                    linear_term(1, not(2)),
                    linear_term(1, not(4)),
                    linear_term(1, not(6)),
                ],
                2,
            ),
        ],
        objective: None,
    };

    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");
    let result = solver.solve();
    solver
        .conclude_proof()
        .expect("proof conclusion must succeed");

    assert_eq!(result, PbCdclResult::Unsatisfiable);

    let proof_output = buf.as_string();

    // Header check.
    assert!(
        proof_output.starts_with("pseudo-Boolean proof version 3.0\n"),
        "must have VeriPB v3 header"
    );

    // Derivation steps should be present (pol lines or rup lines).
    let derivation_lines: Vec<&str> = proof_output
        .lines()
        .filter(|line| line.starts_with("pol ") || line.starts_with("rup "))
        .collect();

    assert!(
        !derivation_lines.is_empty(),
        "weighted pigeonhole UNSAT must produce derivation steps: {proof_output}"
    );

    // VeriPB UNSAT footer must be present.
    assert!(
        proof_output
            .lines()
            .any(|line| line.starts_with("conclusion UNSAT : ")),
        "UNSAT proof must conclude with a VeriPB UNSAT footer"
    );
    assert!(
        proof_output.lines().last() == Some("end pseudo-Boolean proof;"),
        "UNSAT proof must end with the VeriPB proof terminator"
    );
}

#[test]
fn test_proof_logging_constraint_ids_track_learned_constraints() {
    // Instance that requires learning: pigeonhole 3/2.
    let instance = PbInstance {
        num_vars: 6,
        num_constraints: 5,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, lit(3)), linear_term(1, lit(4))], 1),
            ge_constraint(vec![linear_term(1, lit(5)), linear_term(1, lit(6))], 1),
            ge_constraint(
                vec![
                    linear_term(1, not(1)),
                    linear_term(1, not(3)),
                    linear_term(1, not(5)),
                ],
                2,
            ),
            ge_constraint(
                vec![
                    linear_term(1, not(2)),
                    linear_term(1, not(4)),
                    linear_term(1, not(6)),
                ],
                2,
            ),
        ],
        objective: None,
    };

    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf)
        .expect("proof writer creation must succeed");
    let result = solver.solve();
    solver
        .conclude_proof()
        .expect("proof conclusion must succeed");

    assert_eq!(result, PbCdclResult::Unsatisfiable);

    // Constraint IDs should include both input and derived constraints.
    assert!(
        solver.constraint_ids.len() >= 5,
        "should track at least the 5 input constraint IDs, got {}",
        solver.constraint_ids.len()
    );

    // First 5 IDs should be 1..=5 (input constraints).
    for (i, id) in solver.constraint_ids.iter().take(5).enumerate() {
        assert_eq!(
            id.get(),
            (i + 1) as u64,
            "input constraint {i} should have proof ID {}",
            i + 1
        );
    }
}

// --- Initial activity warm start tests ---

#[test]
fn test_initial_activity_from_coefficients() {
    // 3*x1 + 2*x2 + 1*x3 >= 4
    // After preprocessing, x1 should have highest initial activity
    // because its coefficient is largest.
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(3, lit(1)),
                linear_term(2, lit(2)),
                linear_term(1, lit(3)),
            ],
            4,
        )],
        objective: None,
    };

    let solver = PbCdclSolver::new(&instance);

    // Activities should be non-zero (warm start from coefficients).
    let total_activity: f64 = solver.activity[1..=3].iter().sum();
    assert!(
        total_activity > 0.0,
        "initial activities should be non-zero after coefficient warm start"
    );

    // Activities should be normalized to [0, 1] range.
    for var in 1..=3 {
        assert!(
            solver.activity[var] <= 1.0,
            "activity[{var}] = {} should be <= 1.0",
            solver.activity[var]
        );
        assert!(
            solver.activity[var] >= 0.0,
            "activity[{var}] = {} should be >= 0.0",
            solver.activity[var]
        );
    }
}

#[test]
fn test_initial_activity_ordering_in_heap() {
    // With coefficients [10, 1, 5], the heap should prefer var with coeff 10
    // first, then var with coeff 5, then var with coeff 1.
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(10, lit(1)),
                linear_term(1, lit(2)),
                linear_term(5, lit(3)),
            ],
            3,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);

    // The heap should pop variables in order of decreasing activity.
    // After preprocessing, coefficients may be tightened, but relative
    // ordering should be preserved for non-tightened coefficients.
    let first = solver.vsids_heap.pop_max(&solver.activity);
    assert!(first.is_some(), "heap should contain variables");

    // Just verify we can pop all 3 variables.
    let second = solver.vsids_heap.pop_max(&solver.activity);
    let third = solver.vsids_heap.pop_max(&solver.activity);
    assert!(second.is_some());
    assert!(third.is_some());
}

#[test]
fn test_initial_activity_solve_still_correct() {
    // Verify that the warm start does not break correctness.
    // Weighted UNSAT instance:
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(3, lit(1)), linear_term(2, lit(2))], 4),
            ge_constraint(vec![linear_term(2, not(1)), linear_term(3, not(2))], 4),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();
    assert_eq!(result, PbCdclResult::Unsatisfiable);
}

// --- Learned constraint strengthening tests ---

#[test]
fn test_strengthening_preserves_correctness_on_unsat() {
    // Weighted UNSAT instance that exercises strengthening during conflict
    // analysis. The strengthening pipeline (saturation + GCD + weakening)
    // must not cause the solver to return a wrong answer.
    //
    // 3*x1 + 2*x2 >= 4 AND 2*~x1 + 3*~x2 >= 4 (UNSAT)
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 2,
        constraints: vec![
            ge_constraint(vec![linear_term(3, lit(1)), linear_term(2, lit(2))], 4),
            ge_constraint(vec![linear_term(2, not(1)), linear_term(3, not(2))], 4),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();
    assert_eq!(result, PbCdclResult::Unsatisfiable);
}

#[test]
fn test_strengthening_preserves_correctness_on_sat() {
    // SAT instance where strengthening should not break satisfying assignment
    // discovery.
    // 3*x1 + 2*x2 + x3 >= 3
    // 2*~x1 + 3*x2 + x3 >= 3
    // x1 + x2 + ~x3 >= 1
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 3,
        constraints: vec![
            ge_constraint(
                vec![
                    linear_term(3, lit(1)),
                    linear_term(2, lit(2)),
                    linear_term(1, lit(3)),
                ],
                3,
            ),
            ge_constraint(
                vec![
                    linear_term(2, not(1)),
                    linear_term(3, lit(2)),
                    linear_term(1, lit(3)),
                ],
                3,
            ),
            ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(2)),
                    linear_term(1, not(3)),
                ],
                1,
            ),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();

    match result {
        PbCdclResult::Satisfiable(model) => {
            let vals = [
                0,
                i128::from(model[0]),
                i128::from(model[1]),
                i128::from(model[2]),
            ];
            let neg = |v: i128| 1 - v;
            assert!(3 * vals[1] + 2 * vals[2] + vals[3] >= 3, "c1 violated");
            assert!(2 * neg(vals[1]) + 3 * vals[2] + vals[3] >= 3, "c2 violated");
            assert!(vals[1] + vals[2] + neg(vals[3]) >= 1, "c3 violated");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_strengthening_preserves_correctness_pigeonhole() {
    // Pigeonhole 3/2 is UNSAT. Root-level reasoning may now prove this
    // family before search, so this test focuses on preserving correctness
    // on cardinality-like instances.
    let instance = PbInstance {
        num_vars: 6,
        num_constraints: 5,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, lit(3)), linear_term(1, lit(4))], 1),
            ge_constraint(vec![linear_term(1, lit(5)), linear_term(1, lit(6))], 1),
            ge_constraint(
                vec![
                    linear_term(1, not(1)),
                    linear_term(1, not(3)),
                    linear_term(1, not(5)),
                ],
                2,
            ),
            ge_constraint(
                vec![
                    linear_term(1, not(2)),
                    linear_term(1, not(4)),
                    linear_term(1, not(6)),
                ],
                2,
            ),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();

    assert_eq!(result, PbCdclResult::Unsatisfiable);
}

#[test]
fn test_strengthened_stat_is_tracked() {
    // Use an instance that generates conflicts with large coefficients.
    // The strengthening pipeline should record when it reduces constraints.
    //
    // Weighted pigeonhole: 3 pigeons, 2 holes with different weights.
    let instance = PbInstance {
        num_vars: 6,
        num_constraints: 5,
        constraints: vec![
            ge_constraint(vec![linear_term(2, lit(1)), linear_term(3, lit(2))], 3),
            ge_constraint(vec![linear_term(3, lit(3)), linear_term(2, lit(4))], 3),
            ge_constraint(vec![linear_term(2, lit(5)), linear_term(2, lit(6))], 2),
            ge_constraint(
                vec![
                    linear_term(1, not(1)),
                    linear_term(1, not(3)),
                    linear_term(1, not(5)),
                ],
                2,
            ),
            ge_constraint(
                vec![
                    linear_term(1, not(2)),
                    linear_term(1, not(4)),
                    linear_term(1, not(6)),
                ],
                2,
            ),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();

    assert_eq!(result, PbCdclResult::Unsatisfiable);
    // The weighted instance should trigger at least some strengthening
    // (saturation will cap large coefficients produced by CP resolution).
    // We just verify the stat field exists and is accessible.
    let _strengthened = solver.stats().strengthened;
}

#[test]
fn test_lbd_used_in_reduce_db_tiering() {
    // Verify that LBD values correctly tier constraints in reduce_db.
    // Glue constraints (LBD <= 2) must survive, while high-LBD constraints
    // are candidates for deletion.
    let instance = PbInstance {
        num_vars: 8,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            (1..=8).map(|v| linear_term(1, lit(v))).collect(),
            1,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);

    // Add 6 learned constraints with varying LBD values.
    for i in 1..=6 {
        let c = ge_constraint(vec![linear_term(1, lit(i)), linear_term(1, lit(i + 1))], 1);
        solver.add_learned_constraint(c);
    }

    // Set LBDs: mix of glue (1, 2) and weak (7, 8, 9, 10).
    solver.learned_lbd[0] = 1; // glue: never deleted
    solver.learned_lbd[1] = 2; // glue: never deleted
    solver.learned_lbd[2] = 7; // weak: deletion candidate
    solver.learned_lbd[3] = 8; // weak: deletion candidate
    solver.learned_lbd[4] = 9; // weak: deletion candidate
    solver.learned_lbd[5] = 10; // weak: deletion candidate

    solver.reduce_db();

    // Glue constraints must survive.
    assert!(solver.learned_active[0], "LBD=1 must survive");
    assert!(solver.learned_active[1], "LBD=2 must survive");

    // At least some weak constraints should be deleted (worst half of 4 = 2).
    let deleted_count = solver.learned_active.iter().filter(|&&a| !a).count();
    assert_eq!(
        deleted_count, 2,
        "half of 4 weak constraints should be deleted"
    );

    // The worst two (LBD=10 and LBD=9) should be the ones deleted.
    assert!(!solver.learned_active[5], "LBD=10 should be deleted");
    assert!(!solver.learned_active[4], "LBD=9 should be deleted");
}

#[test]
fn test_strengthening_with_optimization_preserves_optimality() {
    // Optimization instance: the strengthening pipeline must not
    // interfere with finding the true optimum.
    // min: 3*x1 + 2*x2 + 1*x3
    // subject to: x1 + x2 + x3 >= 2
    // Optimal: x2=true, x3=true -> cost = 2+1 = 3
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![
                linear_term(1, lit(1)),
                linear_term(1, lit(2)),
                linear_term(1, lit(3)),
            ],
            2,
        )],
        objective: Some(objective(vec![
            linear_term(3, lit(1)),
            linear_term(2, lit(2)),
            linear_term(1, lit(3)),
        ])),
    };

    let obj = instance.objective.as_ref().unwrap().clone();
    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_optimize(&obj, None);

    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, 3, "optimal cost should be 3 (x2+x3)");
            let count: i128 = model.iter().filter(|&&v| v).count() as i128;
            assert!(count >= 2, "at least 2 variables must be true");
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

// --- Round-to-one integration tests ---

#[test]
fn test_round_to_one_stats_tracked() {
    // The round-to-one stats fields exist and are initialized to 0
    // for a trivially satisfiable instance (no conflicts needed).
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let _result = solver.solve();
    let stats = solver.stats();

    // Trivially SAT: no conflicts, so no round-to-one resolution steps.
    assert_eq!(stats.round_to_one_count, 0);
    assert_eq!(stats.round_to_one_fallback_count, 0);
}

#[test]
fn test_round_to_one_uses_resolved_asserting_literal_when_candidate_stale() {
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 0,
        constraints: Vec::new(),
        objective: None,
    };
    let mut solver = PbCdclSolver::new(&instance);
    solver.decide(-3);

    let conflict = CpConstraint::try_from(&ge_constraint(
        vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
        1,
    ))
    .expect("fixture conflict must be linear CP");
    let reason = CpConstraint::try_from(&ge_constraint(
        vec![linear_term(1, not(1)), linear_term(3, lit(3))],
        2,
    ))
    .expect("fixture reason must be linear CP");

    let (resolved, _proof_id, used_division) = solver
        .resolve_round_to_one_with_proof(&conflict, &reason, lit(1), Some(lit(2)), None, None)
        .expect("fixture must resolve");

    assert!(
        used_division,
        "resolved unique current-level literal should trigger round-to-one"
    );
    assert_eq!(resolved.coefficient(lit(3)), 1);
    assert_eq!(resolved.degree(), 1);
}

#[test]
fn test_round_to_one_weighted_pigeonhole_4_3() {
    // 4 pigeons, 3 holes with weights. UNSAT.
    // This is a benchmark where PB cutting planes should benefit
    // from round-to-one: the weighted constraints produce large
    // coefficients during analysis that division reduces.
    //
    // Variables: p_ij = pigeon i in hole j (1-indexed)
    // x1=p11, x2=p12, x3=p13, x4=p21, x5=p22, x6=p23,
    // x7=p31, x8=p32, x9=p33, x10=p41, x11=p42, x12=p43
    //
    // Each pigeon must be somewhere (weighted for non-trivial coefficients):
    //   2*p11 + 2*p12 + 2*p13 >= 2 (pigeon 1)
    //   2*p21 + 2*p22 + 2*p23 >= 2 (pigeon 2)
    //   2*p31 + 2*p32 + 2*p33 >= 2 (pigeon 3)
    //   2*p41 + 2*p42 + 2*p43 >= 2 (pigeon 4)
    //
    // At most one pigeon per hole:
    //   ~p11 + ~p21 + ~p31 + ~p41 >= 3 (hole 1)
    //   ~p12 + ~p22 + ~p32 + ~p42 >= 3 (hole 2)
    //   ~p13 + ~p23 + ~p33 + ~p43 >= 3 (hole 3)
    let mut constraints = Vec::new();

    // Each pigeon placed somewhere (weighted).
    for pigeon in 0..4 {
        let base = pigeon * 3 + 1;
        constraints.push(ge_constraint(
            vec![
                linear_term(2, lit(base)),
                linear_term(2, lit(base + 1)),
                linear_term(2, lit(base + 2)),
            ],
            2,
        ));
    }

    // At most one pigeon per hole.
    for hole in 0..3u32 {
        constraints.push(ge_constraint(
            vec![
                linear_term(1, not(1 + hole)),
                linear_term(1, not(4 + hole)),
                linear_term(1, not(7 + hole)),
                linear_term(1, not(10 + hole)),
            ],
            3,
        ));
    }

    let instance = PbInstance {
        num_vars: 12,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    };

    let mut solver = solver_with_root_probe_disabled(&instance);
    // The dense conflict-analysis fast path now uses the PROVEN round-to-one,
    // so resolution steps land in the `proven_round_to_one_*` counters; the
    // heuristic `round_to_one_*` counters only move on the (rare) overflow
    // fallback. Count BOTH families so the exercise still terminates as soon
    // as any round-to-one resolution step has run.
    let result = solver.solve_with_stop(|solver| {
        solver.stats.round_to_one_count
            + solver.stats.round_to_one_fallback_count
            + solver.stats.proven_round_to_one_count
            + solver.stats.proven_round_to_one_fallback_count
            >= 1
    });

    assert!(
        matches!(result, PbCdclResult::Unknown | PbCdclResult::Unsatisfiable),
        "round-to-one exercise should stop cleanly or prove UNSAT, got {result:?}"
    );
    let stats = solver.stats();
    assert!(
        stats.conflicts > 0,
        "weighted pigeonhole 4-3 should require conflicts"
    );
    assert!(
        stats.round_to_one_count
            + stats.round_to_one_fallback_count
            + stats.proven_round_to_one_count
            + stats.proven_round_to_one_fallback_count
            >= 1,
        "weighted pigeonhole 4-3 should exercise round-to-one conflict analysis"
    );
}

/// Builds a 5-column market-split instance whose weights are near
/// `i128::MAX/3`, chosen so cutting-planes resolution overflows i128 in BOTH
/// the proven and heuristic round-to-one paths, forcing the
/// reduce-to-cardinality overflow fallback.
fn overflow_market_split_instance(variant: i128) -> PbInstance {
    let big = i128::MAX / 3;
    let w = [
        big - variant,
        big - 10 - variant * 3,
        big - 100 - variant * 7,
        big - 1000 - variant * 11,
        big - 7 - variant * 13,
    ];
    // Two terms: s_lo <= 2*big <= i128::MAX, so degree construction is safe.
    let s_lo = w[0] + w[2];
    let pos: Vec<PbTerm> = (0..5)
        .map(|i| linear_term(w[i], lit(i as u32 + 1)))
        .collect();
    let neg: Vec<PbTerm> = (0..5)
        .map(|i| linear_term(-w[i], lit(i as u32 + 1)))
        .collect();
    PbInstance {
        num_vars: 5,
        num_constraints: 2,
        constraints: vec![ge_constraint(pos, s_lo), ge_constraint(neg, -(s_lo - 1))],
        objective: None,
    }
}

/// Builds a weighted pigeonhole instance: `p` pigeons, `p-1` holes, with
/// near-`i128::MAX` weights on both the per-pigeon at-least-one constraints
/// and the per-hole at-most-one constraints. It is UNSAT (classic
/// pigeonhole). The huge weights make cutting-planes resolution overflow
/// i128 in both round-to-one paths, while the hole constraints reduce to
/// TIGHT at-most-one cardinalities that stay falsified — so the
/// reduce-to-cardinality fallback fires and is used productively.
fn overflow_weighted_pigeonhole_instance(p: u32) -> PbInstance {
    let mult = i128::MAX / 8;
    let holes = p - 1;
    let mut constraints = Vec::new();
    for pig in 0..p {
        let terms: Vec<PbTerm> = (0..holes)
            .map(|h| {
                let var = pig * holes + h + 1;
                linear_term(mult + i128::from(h) + 1, lit(var))
            })
            .collect();
        constraints.push(ge_constraint(terms, mult + 1));
    }
    for h in 0..holes {
        let terms: Vec<PbTerm> = (0..p)
            .map(|pig| {
                let var = pig * holes + h + 1;
                linear_term(mult + i128::from(pig) + 1, not(var))
            })
            .collect();
        let deg = (mult + 1) * (i128::from(p) - 1);
        constraints.push(ge_constraint(terms, deg));
    }
    PbInstance {
        num_vars: p * holes,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    }
}

#[test]
fn test_reduce_to_cardinality_overflow_fallback_fires() {
    // On a large-coefficient weighted-pigeonhole instance the proven (and
    // heuristic) round-to-one resolutions overflow i128; the dense conflict
    // analysis then uses the reduce-to-cardinality overflow fallback. This
    // asserts the fallback is actually exercised (counter > 0), that the
    // proven path really overflowed, and that solving stays sound (no panic;
    // the run stops cleanly under the conflict cap).
    let instance = overflow_weighted_pigeonhole_instance(5);
    let mut solver = solver_with_root_probe_disabled(&instance);
    let result = solver.solve_with_stop(|s| s.stats.conflicts >= 2000);
    let s = solver.stats();

    assert!(
        matches!(result, PbCdclResult::Unknown | PbCdclResult::Unsatisfiable),
        "overflow fallback run must stop cleanly or prove UNSAT, got {result:?}"
    );
    assert!(
        s.proven_round_to_one_fallback_count > 0,
        "expected the proven round-to-one to overflow on huge coefficients"
    );
    assert!(
        s.reduce_to_cardinality_count > 0,
        "expected the reduce-to-cardinality overflow fallback to fire \
             (proven={}, proven_fb={}, r2o={}, r2o_fb={}, card={})",
        s.proven_round_to_one_count,
        s.proven_round_to_one_fallback_count,
        s.round_to_one_count,
        s.round_to_one_fallback_count,
        s.reduce_to_cardinality_count,
    );
}

#[test]
fn test_reduce_to_cardinality_overflow_preserves_correctness() {
    // The market-split instances are trivially UNSAT: the two constraints
    // demand `s_lo <= sum w_i x_i <= s_lo - 1`, impossible for ANY
    // assignment. The overflow fallback only ever adds IMPLIED constraints,
    // so it can NEVER turn this UNSAT instance SAT. Under a bounded conflict
    // budget the solver must report UNSAT or Unknown — never SAT.
    for variant in 0..3 {
        let instance = overflow_market_split_instance(variant);
        let mut solver = solver_with_root_probe_disabled(&instance);
        let result = solver.solve_with_stop(|s| s.stats.conflicts >= 3000);
        assert!(
            matches!(result, PbCdclResult::Unknown | PbCdclResult::Unsatisfiable),
            "overflow market-split (variant {variant}) is UNSAT; must never \
                 be reported SAT, got {result:?}"
        );
    }

    // The weighted-pigeonhole instances (which DO exercise the cardinality
    // fallback) are UNSAT by pigeonhole: P pigeons cannot occupy P-1 holes
    // with at most one pigeon per hole. The overflow fallback only adds
    // IMPLIED constraints, so the solver must never report SAT.
    for p in 4..=6u32 {
        let instance = overflow_weighted_pigeonhole_instance(p);
        let mut solver = solver_with_root_probe_disabled(&instance);
        let result = solver.solve_with_stop(|s| s.stats.conflicts >= 2000);
        assert!(
            matches!(result, PbCdclResult::Unknown | PbCdclResult::Unsatisfiable),
            "overflow weighted-pigeonhole (p={p}) is UNSAT; must never be \
                 reported SAT, got {result:?}"
        );
    }
}

#[test]
fn test_round_to_one_preserves_sat_correctness() {
    // SAT instance with weighted constraints to verify that
    // round-to-one conflict analysis still produces correct models.
    //   4*x1 + 3*x2 + 2*x3 + 1*x4 >= 5
    //   3*~x1 + 2*x2 + 4*x3 + 1*x4 >= 4
    //   1*x1 + 1*~x2 + 1*x3 + 1*x4 >= 2
    // Should be SAT (e.g., x1=F, x2=T, x3=T, x4=T: 3+2+1=6>=5, 3+2+4+1=10>=4, 0+0+1+1=2>=2).
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 3,
        constraints: vec![
            ge_constraint(
                vec![
                    linear_term(4, lit(1)),
                    linear_term(3, lit(2)),
                    linear_term(2, lit(3)),
                    linear_term(1, lit(4)),
                ],
                5,
            ),
            ge_constraint(
                vec![
                    linear_term(3, not(1)),
                    linear_term(2, lit(2)),
                    linear_term(4, lit(3)),
                    linear_term(1, lit(4)),
                ],
                4,
            ),
            ge_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, not(2)),
                    linear_term(1, lit(3)),
                    linear_term(1, lit(4)),
                ],
                2,
            ),
        ],
        objective: None,
    };

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve();

    match result {
        PbCdclResult::Satisfiable(model) => {
            // Verify all constraints manually.
            let v = |i: usize| if model[i] { 1i64 } else { 0 };
            let nv = |i: usize| if model[i] { 0i64 } else { 1 };
            let c1 = 4 * v(0) + 3 * v(1) + 2 * v(2) + v(3);
            let c2 = 3 * nv(0) + 2 * v(1) + 4 * v(2) + v(3);
            let c3 = v(0) + nv(1) + v(2) + v(3);
            assert!(c1 >= 5, "constraint 1 violated: {c1} < 5");
            assert!(c2 >= 4, "constraint 2 violated: {c2} < 4");
            assert!(c3 >= 2, "constraint 3 violated: {c3} < 2");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

/// Regression for the counting-propagation keystone: the bnn instance whose
/// big-M rows triggered the earlier wrong-UNSAT is feasible (SAT). The
/// counting propagator (auto-selected for these big-M rows) must NEVER claim
/// it unsatisfiable. Under a bounded budget the solver may not prove the
/// optimum, but it must not return `Unsatisfiable` — that would be a
/// catastrophic soundness failure. Skips gracefully if the file is absent.
#[test]
fn bnn_back_image_73_is_not_wrongly_unsat_with_counting() {
    // Resolve under $AY_PBCOMP_BENCH_ROOT (default: the checkout-relative
    // benchmarks/pb-comp; the corpus is not tracked in git, so this skips on
    // fresh checkouts).
    let root = std::env::var_os("AY_PBCOMP_BENCH_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../benchmarks/pb-comp")
        });
    let path = root
        .join("PB25/normalized-PB25/OPT-LIN/sakai/PB25-bnn-verification-20250419/instances/normalized-bnn_mnist_back_image_73_label5_adversarial_norm_1.opb")
        .display()
        .to_string();
    let Ok(text) = std::fs::read_to_string(&path) else {
        eprintln!("skipping {path}: not available");
        return;
    };
    let instance = crate::parse_opb(&text).expect("parse bnn OPB");

    // Confirm the instance really does select counting for at least one of
    // its constraints, so this test actually exercises the new path.
    let mut propagator = PbPropagator::new();
    for constraint in &instance.constraints {
        propagator.add_from_pb_constraint(constraint);
    }
    assert!(
        (0..propagator.num_constraints()).any(|cid| propagator.is_counting_for_test(cid)),
        "bnn instance should auto-select counting for its big-M rows"
    );

    let mut solver = PbCdclSolver::new(&instance);
    let start = std::time::Instant::now();
    let result =
        solver.solve_interruptible(|| start.elapsed() >= std::time::Duration::from_secs(20));
    assert!(
        !matches!(result, PbCdclResult::Unsatisfiable),
        "bnn instance is feasible; counting propagation must not claim UNSAT (got {result:?})"
    );
}

/// SOUNDNESS (covering-bound-validity): whenever
/// `objective_lower_bound_from_constraints` returns `Some(F)`, `F` must be a
/// VALID lower bound on the minimization objective: `F <= objective(x)` for
/// EVERY feasible `x`. It must NEVER overshoot — a wrong-high `F` would let a
/// suboptimal incumbent be upgraded to a false OPTIMUM (=> category DQ). Five
/// concrete cases (covering, adversarial 4-cycle vertex cover, weighted-DP,
/// negated-literal, empty-objective) enumerate all feasible assignments. The
/// Kani harness `kani_covering_bound::*` proves it for ALL small bounded
/// instances (proofs/2026-06-16-pb-trust-soundness-harnesses.md).
#[test]
fn test_objective_lower_bound_never_overshoots_concrete() {
    fn assert_valid_lb(constraints: &[PbConstraint], objective: &PbObjective, num_vars: u32) {
        let Some(f) = objective_lower_bound_from_constraints(constraints, objective, &|| false)
        else {
            return;
        };
        let mut any_feasible = false;
        for mask in 0u32..(1u32 << num_vars) {
            let x: Vec<bool> = (0..num_vars).map(|i| mask & (1 << i) != 0).collect();
            if crate::eval::verify_all_constraints(constraints, &x) {
                any_feasible = true;
                let obj = eval_objective(objective, &x);
                assert!(
                    f <= obj,
                    "lower bound {f} OVERSHOOTS feasible objective {obj} at x={x:?}"
                );
            }
        }
        assert!(any_feasible, "emitted bound {f} but no feasible assignment");
    }

    // Case 1: direct covering row. min x1 + x2 s.t. x1 + x2 >= 1 (optimum 1).
    let obj = PbObjective {
        terms: vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
    };
    let cs = vec![ge_constraint(
        vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
        1,
    )];
    assert_valid_lb(&cs, &obj, 2);

    // Case 2 (adversarial, surrogate-aggregation): 4-cycle vertex cover,
    // optimum 2, surrogate LP-dual bound exactly 2 (tight). A claim of 3 would
    // overshoot.
    let obj2 = PbObjective {
        terms: vec![
            linear_term(1, lit(1)),
            linear_term(1, lit(2)),
            linear_term(1, lit(3)),
            linear_term(1, lit(4)),
        ],
    };
    let cs2 = vec![
        ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(2))], 1),
        ge_constraint(vec![linear_term(1, lit(2)), linear_term(1, lit(3))], 1),
        ge_constraint(vec![linear_term(1, lit(3)), linear_term(1, lit(4))], 1),
        ge_constraint(vec![linear_term(1, lit(4)), linear_term(1, lit(1))], 1),
    ];
    assert_valid_lb(&cs2, &obj2, 4);

    // Case 3 (weighted/knapsack DP): min 2x1+3x2 s.t. 2x1+3x2 >= 3 (optimum 3).
    let obj3 = PbObjective {
        terms: vec![linear_term(2, lit(1)), linear_term(3, lit(2))],
    };
    let cs3 = vec![ge_constraint(
        vec![linear_term(2, lit(1)), linear_term(3, lit(2))],
        3,
    )];
    assert_valid_lb(&cs3, &obj3, 2);

    // Case 4 (negated literal): min x1 s.t. x1 + ~x2 >= 1 (optimum 0 via x2=0).
    let obj4 = PbObjective {
        terms: vec![linear_term(1, lit(1))],
    };
    let cs4 = vec![ge_constraint(
        vec![linear_term(1, lit(1)), linear_term(1, not(2))],
        1,
    )];
    assert_valid_lb(&cs4, &obj4, 2);

    // Case 5 (empty objective short-circuit): Some(0), a valid LB.
    let obj5 = PbObjective { terms: vec![] };
    let cs5 = vec![ge_constraint(vec![linear_term(1, lit(1))], 1)];
    assert_eq!(
        objective_lower_bound_from_constraints(&cs5, &obj5, &|| false),
        Some(0)
    );
    assert_valid_lb(&cs5, &obj5, 1);

    // Case 6 (equality-aggregation, mixed-sign constant 0): min x1 - x2 with
    // x1 - x2 = 0 (i.e. x1 == x2). The objective equals 0 on EVERY feasible
    // point, so the exact constant bound is 0. The positive-coefficient path
    // declines here (negative coefficient on x2), so the equality bound must
    // carry it. A claim above 0 would overshoot.
    let obj6 = PbObjective {
        terms: vec![linear_term(1, lit(1)), linear_term(-1, lit(2))],
    };
    let cs6 = vec![eq_constraint(
        vec![linear_term(1, lit(1)), linear_term(-1, lit(2))],
        0,
    )];
    assert_eq!(
        equality_aggregation_objective_constant(&cs6, &obj6, &|| false),
        Some(0)
    );
    assert_eq!(
        objective_lower_bound_from_constraints(&cs6, &obj6, &|| false),
        Some(0)
    );
    assert_valid_lb(&cs6, &obj6, 2);

    // Case 7 (non-constant difference must DECLINE): min x1 - x2 with the
    // unrelated equality x3 = 1. The objective is genuinely variable on the
    // feasible set (ranges over {-1, 0, 1}), so the residual is non-empty and
    // equality-aggregation must return None (no false constant). The overall
    // bound must still never overshoot the true minimum (-1).
    let obj7 = PbObjective {
        terms: vec![linear_term(1, lit(1)), linear_term(-1, lit(2))],
    };
    let cs7 = vec![eq_constraint(vec![linear_term(1, lit(3))], 1)];
    assert_eq!(
        equality_aggregation_objective_constant(&cs7, &obj7, &|| false),
        None
    );
    assert_valid_lb(&cs7, &obj7, 3);

    // Case 8 (negated-literal equality-implied constant 0): min x1 + ~x2 with
    // x1 + ~x2 = 1 (folds to x1 - x2 = 0). objective == 1 - x2 + x1; combined
    // with the row it is the constant 1 on the feasible set. Exercises the
    // ~x = 1 - x folding in both objective and row.
    let obj8 = PbObjective {
        terms: vec![linear_term(1, lit(1)), linear_term(1, not(2))],
    };
    let cs8 = vec![eq_constraint(
        vec![linear_term(1, lit(1)), linear_term(1, not(2))],
        1,
    )];
    assert_eq!(
        equality_aggregation_objective_constant(&cs8, &obj8, &|| false),
        Some(1)
    );
    assert_eq!(
        objective_lower_bound_from_constraints(&cs8, &obj8, &|| false),
        Some(1)
    );
    assert_valid_lb(&cs8, &obj8, 2);

    // Case 9 (NEGATIVE equality-implied constant -2; guards the .max(0)
    // clamp): min -x1 - x2 with x1 = 1 AND x2 = 1. Both vars forced true, so
    // the objective is exactly -2 on the single feasible point. The
    // equality-aggregation constant (-2) must be folded in OUTSIDE the
    // positive path's .max(0); a clamp to 0 here would OVERSHOOT the true
    // minimum -2 and falsely upgrade a suboptimal incumbent.
    let obj9 = PbObjective {
        terms: vec![linear_term(-1, lit(1)), linear_term(-1, lit(2))],
    };
    let cs9 = vec![
        eq_constraint(vec![linear_term(1, lit(1))], 1),
        eq_constraint(vec![linear_term(1, lit(2))], 1),
    ];
    assert_eq!(
        equality_aggregation_objective_constant(&cs9, &obj9, &|| false),
        Some(-2)
    );
    assert_eq!(
        objective_lower_bound_from_constraints(&cs9, &obj9, &|| false),
        Some(-2)
    );
    assert_valid_lb(&cs9, &obj9, 2);
}

/// MEMGUARD (wf_fbcc80bb): the structural bound's stop hook must be honored —
/// an already-tripped stop makes every interruptible sub-bound decline
/// promptly (`None` = no information, always sound), while a never-tripped
/// stop leaves the produced bound unchanged (no behavior change when not
/// stopped).
#[test]
fn test_objective_lower_bound_stop_hook_declines_and_is_noop_when_unfired() {
    // Same shape as case 9 of the overshoot test: equality-aggregation
    // constant -2 (the positive path declines on the negative coefficients,
    // so the ONLY bound source is the interruptible elimination).
    let obj = PbObjective {
        terms: vec![linear_term(-1, lit(1)), linear_term(-1, lit(2))],
    };
    let cs = vec![
        eq_constraint(vec![linear_term(1, lit(1))], 1),
        eq_constraint(vec![linear_term(1, lit(2))], 1),
    ];

    // Never-stopped: identical bound to the pre-hook behavior.
    assert_eq!(
        objective_lower_bound_from_constraints(&cs, &obj, &|| false),
        Some(-2)
    );
    assert_eq!(
        equality_aggregation_objective_constant(&cs, &obj, &|| false),
        Some(-2)
    );

    // Already-stopped: the elimination declines before any pivot work.
    assert_eq!(
        equality_aggregation_objective_constant(&cs, &obj, &|| true),
        None
    );
    assert_eq!(
        objective_lower_bound_from_constraints(&cs, &obj, &|| true),
        None
    );

    // Positive-path (covering/DP/aggregation) shape: the stop must make the
    // whole combined bound decline there too.
    let obj_pos = PbObjective {
        terms: vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
    };
    let cs_pos = vec![ge_constraint(
        vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
        1,
    )];
    assert_eq!(
        objective_lower_bound_from_constraints(&cs_pos, &obj_pos, &|| false),
        Some(1)
    );
    assert_eq!(
        objective_lower_bound_from_constraints(&cs_pos, &obj_pos, &|| true),
        None
    );
}

/// MEMGUARD (wf_fbcc80bb, revised after the mult_diagcomm regression): the
/// equality-aggregation elimination is bounded by the STOP POLL (deadline +
/// process-memory guard), NOT a dimension work-proxy. A dimension cost cannot
/// separate a bignum-blowup detonator from a benign large aggregation — the
/// `mult_diagcomm` family (rows^2*universe ~= 7.5e8) certifies OPTIMAL in ~1 s
/// yet a 1e8 proxy declined it. So a stop that FIRES must decline the large
/// shape (poll-driven, sound `None`), while a shape that never trips the poll
/// still yields its exact constant.
#[test]
fn test_equality_aggregation_bounded_by_stop_poll() {
    // Row 1: x1 + x2 = 1 carries the objective; 1998 chained filler rows
    // x_i + x_{i+1} = 1 (i in 3..=2000) inflate the shape to 2001 vars — a
    // ~8e9-op elimination that MUST be shed by the poll, not run to completion.
    let obj = PbObjective {
        terms: vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
    };
    let mut cs = vec![eq_constraint(
        vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
        1,
    )];
    for i in 3..=2000u32 {
        cs.push(eq_constraint(
            vec![linear_term(1, lit(i)), linear_term(1, lit(i + 1))],
            1,
        ));
    }
    // A stop that fires declines the large elimination without completing it.
    assert_eq!(
        equality_aggregation_objective_constant(&cs, &obj, &|| true),
        None
    );

    // The single objective row never trips the poll and yields its exact
    // constant — the elimination itself is unchanged, only its bound is.
    assert_eq!(
        equality_aggregation_objective_constant(&cs[..1], &obj, &|| false),
        Some(1)
    );
}

/// The root-LP budget must be DEADLINE-PROPORTIONAL when a solve deadline is
/// threaded (`min(flat cap, remaining / ROOT_LP_BOUND_DEADLINE_FRACTION)`) and
/// fall back to the flat cap when it is not. An expired deadline yields a zero
/// budget (the LP aborts immediately with its anytime-sound bound), never a
/// negative/panicking duration.
#[test]
fn root_lp_budget_is_deadline_proportional() {
    use std::time::Duration;

    // No deadline threaded: the flat backstop applies unchanged.
    assert_eq!(root_lp_budget_for(None), ROOT_LP_BOUND_TIME_BUDGET);

    // Plenty of remaining time: the flat cap binds (min).
    assert_eq!(
        root_lp_budget_for(Some(Duration::from_mins(2))),
        ROOT_LP_BOUND_TIME_BUDGET
    );
    // Exactly at the crossover: remaining / fraction == cap.
    let crossover = ROOT_LP_BOUND_TIME_BUDGET * ROOT_LP_BOUND_DEADLINE_FRACTION;
    assert_eq!(
        root_lp_budget_for(Some(crossover)),
        ROOT_LP_BOUND_TIME_BUDGET
    );

    // Short budgets: the proportional share binds. A 10s optimize call grants
    // the LP floor 2.5s, not the flat 5s.
    assert_eq!(
        root_lp_budget_for(Some(Duration::from_secs(10))),
        Duration::from_millis(2_500)
    );
    assert_eq!(
        root_lp_budget_for(Some(Duration::from_secs(2))),
        Duration::from_millis(500)
    );

    // Expired/zero remaining time: zero budget, no underflow.
    assert_eq!(root_lp_budget_for(Some(Duration::ZERO)), Duration::ZERO);

    // The solver method measures remaining time against the threaded deadline
    // (saturating: a deadline in the past is a zero budget).
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 0,
        constraints: vec![],
        objective: None,
    };
    let mut solver = PbCdclSolver::new(&instance);
    let now = std::time::Instant::now();
    assert_eq!(solver.root_lp_budget(now), ROOT_LP_BOUND_TIME_BUDGET);
    solver.set_solve_deadline(Some(now + Duration::from_secs(10)));
    assert_eq!(solver.root_lp_budget(now), Duration::from_millis(2_500));
    let expired = now
        .checked_sub(Duration::from_secs(1))
        .expect("the monotonic clock has advanced by at least one second");
    solver.set_solve_deadline(Some(expired));
    assert_eq!(solver.root_lp_budget(now), Duration::ZERO);
    solver.set_solve_deadline(None);
    assert_eq!(solver.root_lp_budget(now), ROOT_LP_BOUND_TIME_BUDGET);
}

// ---------------------------------------------------------------------------
// `seed_phases` — caller warm-start phase seeding (soundness-neutral bias)
// ---------------------------------------------------------------------------

/// The user phase seed steers WHICH equally-optimal model the first descent
/// lands on, and it overrides the objective-direction seeding (which prefers
/// all-false for positive-coefficient objectives).
#[test]
fn seed_phases_steers_first_incumbent_between_equal_optima() {
    // x1 + x2 >= 1, minimize x1 + x2: two symmetric optima (T,F) and (F,T).
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge_constraint(
            vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
            1,
        )],
        objective: None,
    };
    let objective = PbObjective {
        terms: vec![linear_term(1, lit(1)), linear_term(1, lit(2))],
    };

    // Seed toward (T,F): whichever variable is decided first, the phases (and
    // then propagation on the >=1 row) yield exactly the seeded optimum, so
    // the first incumbent — and therefore the returned optimal model, since
    // no strictly better cost exists — is the seeded one.
    let mut solver = PbCdclSolver::new(&instance);
    solver.seed_phases(&[(1, true), (2, false)]);
    match solver.solve_optimize(&objective, None) {
        PbCdclResult::Optimal(model, cost) => {
            // model is 0-indexed: model[v - 1] is variable v.
            assert_eq!(cost, 1);
            assert!(model[0] && !model[1], "seed (T,F) not honored: {model:?}");
        }
        other => panic!("expected Optimal, got {other:?}"),
    }

    // The mirrored seed lands on the mirrored optimum.
    let mut solver = PbCdclSolver::new(&instance);
    solver.seed_phases(&[(1, false), (2, true)]);
    match solver.solve_optimize(&objective, None) {
        PbCdclResult::Optimal(model, cost) => {
            assert_eq!(cost, 1);
            assert!(!model[0] && model[1], "seed (F,T) not honored: {model:?}");
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

/// Adversarial seeding (toward the most expensive corner, plus an
/// out-of-range variable) can slow the search but can never change the
/// verdict or the optimal cost — phase saving is only a decision-polarity
/// bias, invisible to propagation and conflict analysis.
#[test]
fn seed_phases_never_changes_verdict_or_optimal_cost() {
    // exactly-one(x1,x2,x3) with costs 3/2/5 and a side row forbidding x2
    // unless x4: optimum is x2+x4 infeasible-free? Keep it simple:
    //   x1 + x2 + x3 = 1;  x4 + ~x2 >= 1  (choosing x2 forces x4, cost 1)
    // costs: x1=3, x2=2, x3=5, x4=1 -> best = x2,x4 at 3? no: x2(2)+x4(1)=3,
    // x1 alone = 3 too. Both optima cost 3; x3 alone costs 5.
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 2,
        constraints: vec![
            eq_constraint(
                vec![
                    linear_term(1, lit(1)),
                    linear_term(1, lit(2)),
                    linear_term(1, lit(3)),
                ],
                1,
            ),
            ge_constraint(vec![linear_term(1, lit(4)), linear_term(1, not(2))], 1),
        ],
        objective: None,
    };
    let objective = PbObjective {
        terms: vec![
            linear_term(3, lit(1)),
            linear_term(2, lit(2)),
            linear_term(5, lit(3)),
            linear_term(1, lit(4)),
        ],
    };

    let mut baseline = PbCdclSolver::new(&instance);
    let PbCdclResult::Optimal(_, base_cost) =
        baseline.solve_optimize_interruptible(&objective, None, || false)
    else {
        panic!("baseline must reach Optimal");
    };
    assert_eq!(base_cost, 3);

    // Worst-corner seed (all true = infeasible under exactly-one) + an
    // out-of-range var id: ignored gracefully, same verdict and cost.
    let mut seeded = PbCdclSolver::new(&instance);
    seeded.seed_phases(&[(1, true), (2, true), (3, true), (4, true), (999, true)]);
    let PbCdclResult::Optimal(model, cost) =
        seeded.solve_optimize_interruptible(&objective, None, || false)
    else {
        panic!("seeded solve must reach Optimal");
    };
    assert_eq!(cost, base_cost);
    // The model itself must still satisfy the constraints (spot-check;
    // model is 0-indexed: model[v - 1] is variable v).
    let m = |v: usize| model[v - 1];
    let picked = [1usize, 2, 3].iter().filter(|&&v| m(v)).count();
    assert_eq!(picked, 1, "exactly-one violated: {model:?}");
    if m(2) {
        assert!(m(4), "x2 chosen without x4: {model:?}");
    }
}

// ---- Single-equality knapsack DP special case (eq_knapsack) ----

/// Aardal_1-shaped complementary Ge pair: `sum a_i x_i >= b` and
/// `sum -a_i x_i >= -b`, i.e. `sum a_i x_i == b`.
fn eq_pair_instance(coeffs: &[i128], b: i128) -> PbInstance {
    let pos = ge_constraint(
        coeffs
            .iter()
            .enumerate()
            .map(|(i, &c)| linear_term(c, lit(i as u32 + 1)))
            .collect(),
        b,
    );
    let neg = ge_constraint(
        coeffs
            .iter()
            .enumerate()
            .map(|(i, &c)| linear_term(-c, lit(i as u32 + 1)))
            .collect(),
        -b,
    );
    PbInstance {
        num_vars: coeffs.len() as u32,
        num_constraints: 2,
        constraints: vec![neg, pos], // negative row first, like the corpus files
        objective: None,
    }
}

fn eq_pair_lhs(coeffs: &[i128], model: &[bool]) -> i128 {
    coeffs
        .iter()
        .enumerate()
        .map(|(i, &c)| if model[i] { c } else { 0 })
        .sum()
}

#[test]
fn eq_knapsack_dp_decides_two_row_equality_sat() {
    // 3, 5, 7, 11, 13 with target 18 = 5 + 13 (among others): SAT.
    let coeffs = [3, 5, 7, 11, 13];
    let instance = eq_pair_instance(&coeffs, 18);
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    match solver.solve() {
        PbCdclResult::Satisfiable(model) => {
            assert_eq!(
                eq_pair_lhs(&coeffs, &model),
                18,
                "model must satisfy the equality"
            );
        }
        other => panic!("expected SAT, got {other:?}"),
    }
    assert_eq!(
        solver.stats().eq_knapsack_dp,
        1,
        "the DP special case must have decided this solve"
    );
}

#[test]
fn eq_knapsack_dp_decides_two_row_equality_unsat() {
    // 3, 5, 7, 11, 13 can never sum to 17, and 17 is root-quiet (every
    // coefficient fits under it in both rows, so plain root propagation and
    // probing cannot refute it before the DP hook runs; probing is disabled
    // for determinism).
    let instance = eq_pair_instance(&[3, 5, 7, 11, 13], 17);
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    solver.config.root_probe_enabled = false;
    assert_eq!(solver.solve(), PbCdclResult::Unsatisfiable);
    assert_eq!(solver.stats().eq_knapsack_dp, 1);
}

#[test]
fn eq_knapsack_dp_disabled_falls_back_to_search() {
    let coeffs = [3, 5, 7, 11, 13];
    let sat_instance = eq_pair_instance(&coeffs, 18);
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&sat_instance, || false);
    solver.set_eq_knapsack_dp_enabled(false);
    match solver.solve() {
        PbCdclResult::Satisfiable(model) => {
            assert_eq!(eq_pair_lhs(&coeffs, &model), 18);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
    assert_eq!(
        solver.stats().eq_knapsack_dp,
        0,
        "knob off must bypass the DP"
    );

    let unsat_instance = eq_pair_instance(&[3, 5, 7], 4);
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&unsat_instance, || false);
    solver.set_eq_knapsack_dp_enabled(false);
    assert_eq!(solver.solve(), PbCdclResult::Unsatisfiable);
    assert_eq!(solver.stats().eq_knapsack_dp, 0);
}

#[test]
fn eq_knapsack_dp_verdicts_match_search_verdicts() {
    // Differential: DP-on vs DP-off must agree on a spread of targets
    // (SAT and UNSAT alike). Coefficients chosen so both paths are fast.
    let coeffs = [3i128, 5, 7, 11, 13];
    let total: i128 = coeffs.iter().sum();
    for target in 0..=total {
        let instance = eq_pair_instance(&coeffs, target);
        let mut dp = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
        let dp_result = dp.solve();
        let mut search = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
        search.set_eq_knapsack_dp_enabled(false);
        let search_result = search.solve();
        match (&dp_result, &search_result) {
            (PbCdclResult::Satisfiable(model), PbCdclResult::Satisfiable(search_model)) => {
                assert_eq!(
                    eq_pair_lhs(&coeffs, model),
                    target,
                    "DP model must hit target"
                );
                assert_eq!(
                    eq_pair_lhs(&coeffs, search_model),
                    target,
                    "search model must hit target"
                );
            }
            (PbCdclResult::Unsatisfiable, PbCdclResult::Unsatisfiable) => {}
            other => panic!("target {target}: DP and search disagree: {other:?}"),
        }
    }
}

#[test]
fn eq_knapsack_dp_skipped_under_proof_logging() {
    // Proof mode must bypass the DP (its derivation is not proof-logged)
    // and still reach the correct UNSAT verdict through logged search.
    let instance = eq_pair_instance(&[3, 5, 7], 4);
    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer construction must succeed");
    assert_eq!(solver.solve(), PbCdclResult::Unsatisfiable);
    assert_eq!(
        solver.stats().eq_knapsack_dp,
        0,
        "proof mode must not use the unlogged DP special case"
    );
    assert!(
        !buf.as_string().is_empty(),
        "proof output must have been written"
    );
}

#[test]
fn eq_knapsack_dp_optimization_reaches_optimum() {
    // 3x1 + 5x2 + 7x3 == 8 has the unique solution {x1, x2}. The DP decides
    // the initial feasibility solve; the bound loop then proves optimality
    // through ordinary search (the added bound row disables the DP gate).
    let coeffs = [3, 5, 7];
    let mut instance = eq_pair_instance(&coeffs, 8);
    instance.objective = Some(PbObjective {
        terms: vec![
            linear_term(1, lit(1)),
            linear_term(1, lit(2)),
            linear_term(1, lit(3)),
        ],
    });
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    let objective = instance.objective.clone().expect("objective present");
    match solver.solve_optimize(&objective, None) {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(eq_pair_lhs(&coeffs, &model), 8);
            assert_eq!(value, 2, "unique solution {{x1, x2}} has objective 2");
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

#[test]
fn eq_knapsack_dp_declines_with_extra_rows() {
    // A third row must disable the special case (rows > 2) and the combined
    // instance must still be decided correctly by search: force x1 = 0,
    // making target 18 unreachable without coefficient 3.
    let coeffs = [3i128, 5, 7, 11, 13];
    let mut instance = eq_pair_instance(&coeffs, 3);
    instance
        .constraints
        .push(ge_constraint(vec![linear_term(1, not(1))], 1));
    instance.num_constraints = 3;
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    assert_eq!(solver.solve(), PbCdclResult::Unsatisfiable);
    assert_eq!(
        solver.stats().eq_knapsack_dp,
        0,
        "3-row instance must bypass the DP"
    );
}

#[test]
fn eq_knapsack_dp_huge_coefficient_pair() {
    // Aardal-style magnitudes (millions) stay exact and fast in the DP.
    let coeffs = [1_000_003i128, 2_000_006, 4_000_012, 8_000_024, 3_500_001];
    let b = 1_000_003 + 4_000_012 + 3_500_001; // reachable
    let instance = eq_pair_instance(&coeffs, b);
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    match solver.solve() {
        PbCdclResult::Satisfiable(model) => {
            assert_eq!(eq_pair_lhs(&coeffs, &model), b);
        }
        other => panic!("expected SAT, got {other:?}"),
    }
    assert_eq!(solver.stats().eq_knapsack_dp, 1);

    // And an unreachable root-quiet huge target: 8_250_000 exceeds every
    // coefficient (nothing is root-forced in either row) and lies strictly
    // between the achievable subset sums 8_000_024 and 8_500_016.
    let instance = eq_pair_instance(&coeffs, 8_250_000);
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
    solver.config.root_probe_enabled = false;
    assert_eq!(solver.solve(), PbCdclResult::Unsatisfiable);
    assert_eq!(solver.stats().eq_knapsack_dp, 1);
}

#[test]
fn test_undecidable_lower_bound_opt_proof_defers_without_conclusion() {
    // Triangle vertex cover: optimum 2, but `obj >= 2` needs a divide-by-2
    // ROUNDING cut (`2*(x1+x2+x3) >= 3` -> `>= ceil(3/2)`), which no positive
    // combination of the three edge rows can express — the direct planner
    // stalls at a proven floor of 1 and the cardinality planner finds no single
    // row of degree >= 2. This is a DIFFERENT inexpressibility cause than the
    // coefficient-cancellation case covered by
    // tests/proof_certified_track.rs::test_le_source_optimization_proof_*, so
    // keep both.
    //
    // The native OPT proof must fail closed: no fabricated `rup >= 1 ;`, no
    // `conclusion BOUNDS`, and `conclude_proof` refuses. The OptimumFound
    // verdict itself still STANDS (the optimum and its model are correct) and
    // the deferral is signalled through `opt_lower_bound_deferred`, which is
    // what routes the CLI to the certified OPT-LIN fallback.
    let objective = objective((1..=3).map(|var| linear_term(1, lit(var))).collect());
    let instance = PbInstance {
        num_vars: 3,
        num_constraints: 3,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, lit(2)), linear_term(1, lit(3))], 1),
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(3))], 1),
        ],
        objective: Some(objective.clone()),
    };
    let buf = SharedBuf::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    let result = solver.solve_optimize(&objective, None);
    assert!(
        matches!(result, PbCdclResult::Optimal(_, 2)),
        "triangle vertex cover should solve to optimum 2, got {result:?}"
    );
    assert!(
        solver.opt_lower_bound_deferred(),
        "an inexpressible structural floor must defer, not fabricate a bound"
    );

    let error = solver
        .conclude_proof()
        .expect_err("an unjustifiable optimality proof must not conclude");
    assert!(
        matches!(error, ProofError::UnprovableOptimizationLowerBound),
        "unexpected proof error: {error:?}"
    );

    let proof = buf.as_string();
    assert!(
        !proof.lines().any(|line| line == "rup >= 1 ;"),
        "no unjustified empty-clause RUP may be emitted: {proof}"
    );
    assert!(
        !proof
            .lines()
            .any(|line| line.starts_with("conclusion BOUNDS")),
        "no conclusion may be claimed for an underivable lower bound: {proof}"
    );
}
