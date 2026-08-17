// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PB26-oriented public-surface regressions.
//!
//! These tests stay on `ay-pb`'s acceptance/integration boundary:
//! - optimization witnesses and interruption semantics via the public portfolio
//! - unsupported-coefficient parse detection at the parser API seam
//! - proof logging safety under interruption

use std::io::{self, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use ay_pb::{
    eval_objective, eval_objective_exact, objective_range_fits_i64, parse_opb, parse_wbo,
    portfolio, verify_all_constraints, ParseError, PbCdclResult, PbCdclSolver, PbConstraint,
    PbInstance, PbLit, PbObjective, PbOutputWriter, PbRel, PbSolution, PbStatus, PbTerm,
};

fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

fn not(var: u32) -> PbLit {
    PbLit { var, negated: true }
}

fn term(coeff: i128, lit: PbLit) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![lit],
    }
}

fn ge_constraint(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}

fn exactly_one_large_optimization_instance(num_vars: u32) -> PbInstance {
    let at_least_one = ge_constraint((1..=num_vars).map(|v| term(1, lit(v))).collect(), 1);
    let at_most_one = ge_constraint(
        (1..=num_vars).map(|v| term(1, not(v))).collect(),
        i128::from(num_vars) - 1,
    );
    let objective = PbObjective {
        terms: (1..=num_vars).map(|v| term(1, lit(v))).collect(),
    };

    PbInstance {
        num_vars,
        num_constraints: 2,
        constraints: vec![at_least_one, at_most_one],
        objective: Some(objective),
    }
}

fn testscheduling_scale_feasible_root_precheck_instance() -> PbInstance {
    parse_opb(concat!(
        "* #variable= 993048 #constraint= 1964067 #equal= 833 intsize= 17\n",
        "min: +1 x14 +2 x13 +4 x12 +8 x11 +16 x10 +32 x9 +64 x8 +128 x7 +256 x6 +512 x5 +1024 x4 +2048 x3 +4096 x2 +8192 x1 ;\n",
        "+1 x15 >= 1 ;\n",
        "+1 x14 +2 x13 +4 x12 +8 x11 +16 x10 +32 x9 +64 x8 +128 x7 +256 x6 +512 x5 +1024 x4 +2048 x3 +4096 x2 +8192 x1 -1 x16 -2 x17 -4 x18 -8 x19 -16 x20 -32 x21 -64 x22 -128 x23 -256 x24 -512 x25 -1024 x26 -2048 x27 -4096 x28 -8192 x29 -16844 x30 >= -16383 ;\n",
        "-1 x14 -2 x13 -4 x12 -8 x11 -16 x10 -32 x9 -64 x8 -128 x7 -256 x6 -512 x5 -1024 x4 -2048 x3 -4096 x2 -8192 x1 +1 x16 +2 x17 +4 x18 +8 x19 +16 x20 +32 x21 +64 x22 +128 x23 +256 x24 +512 x25 +1024 x26 +2048 x27 +4096 x28 +8192 x29 +15923 x30 >= -460 ;\n",
        "+1 x31 +1 x30 -2 x32 >= 0 ;\n",
        "-1 x31 -1 x30 +1 x32 >= -1 ;\n",
        "+1 x33 +1 x32 >= 1 ;\n",
    ))
    .expect("synthetic TestScheduling-scale fixture should parse")
}

fn assert_full_valid_incumbent(
    instance: &PbInstance,
    objective: &PbObjective,
    obj_value: i128,
    assignment: &[bool],
    context: &str,
) {
    assert_eq!(
        assignment.len(),
        instance.num_vars as usize,
        "{context}: incumbent must assign every original PB variable"
    );
    assert!(
        verify_all_constraints(&instance.constraints, assignment),
        "{context}: incumbent must satisfy every original PB constraint; assignment={assignment:?}"
    );
    assert_eq!(
        eval_objective(objective, assignment),
        obj_value,
        "{context}: incumbent objective must be recomputed from the full assignment"
    );
}

fn render_solution(solution: &PbSolution) -> String {
    let mut output = Vec::new();
    let mut writer = PbOutputWriter::new(&mut output);
    writer
        .write_full_result(solution)
        .expect("rendering PB output should succeed");
    String::from_utf8(output).expect("PB output should be valid UTF-8")
}

fn rendered_solution_literals(rendered: &str) -> Vec<String> {
    rendered
        .lines()
        .filter(|line| line.starts_with('v'))
        .flat_map(|line| line.split_whitespace().skip(1))
        .map(ToOwned::to_owned)
        .collect()
}

#[derive(Clone, Default)]
struct SharedBuffer(Arc<Mutex<Vec<u8>>>);

impl SharedBuffer {
    fn as_string(&self) -> String {
        String::from_utf8(
            self.0
                .lock()
                .expect("proof buffer mutex should not be poisoned")
                .clone(),
        )
        .expect("proof output should be valid UTF-8")
    }
}

impl Write for SharedBuffer {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0
            .lock()
            .expect("proof buffer mutex should not be poisoned")
            .extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[test]
fn test_interrupted_optimization_portfolio_returns_best_known_witness() {
    let instance = exactly_one_large_optimization_instance(51);
    let objective = instance
        .objective
        .as_ref()
        .expect("optimization instance should carry an objective");
    let start = Instant::now();
    let term_flag = AtomicBool::new(false);
    let mut callback_calls = 0usize;
    let mut callback_model_len = 0usize;
    let mut callback_objective = None;

    let mut on_improve = |obj_value: i128, model: &[bool]| {
        callback_calls += 1;
        callback_model_len = model.len();
        callback_objective = Some(obj_value);
        if callback_calls == 1 {
            term_flag.store(true, Ordering::Relaxed);
        }
    };

    let result = portfolio::solve_optimization_portfolio(
        &instance,
        objective,
        Some(Duration::from_secs(5)),
        start,
        &term_flag,
        &mut on_improve,
    );

    assert!(
        callback_calls >= 1,
        "optimization portfolio should report at least one incumbent before interruption"
    );
    assert_eq!(
        callback_model_len, 51,
        "native optimization callback must provide a full PB witness"
    );
    assert_eq!(callback_objective, Some(1));
    // The surrogate-aggregation lower bound now certifies the incumbent optimal even
    // under interruption: for `min sum x s.t. sum x >= 1` the bound is ceil(1/1) = 1,
    // which equals the incumbent, so the witness is reported as OPTIMUM FOUND (a
    // strict, correct improvement over the previous unproven SATISFIABLE). The
    // best-known-witness behaviour this test guards (a full, verified 51-var witness
    // returned on interrupt) is unchanged.
    assert_eq!(result.status, PbStatus::OptimumFound);
    assert_eq!(result.objective, Some(1));
    assert_eq!(result.assignment.len(), 51);
    assert!(
        verify_all_constraints(&instance.constraints, &result.assignment),
        "returned incumbent must satisfy every original PB constraint"
    );
    assert_eq!(
        eval_objective(objective, &result.assignment),
        1,
        "returned incumbent objective must match the public witness"
    );
    assert_eq!(
        result.assignment.iter().filter(|&&bit| bit).count(),
        1,
        "the exactly-one constraint should force a single true variable"
    );

    let rendered = render_solution(&result);
    let lines: Vec<&str> = rendered.lines().collect();
    let rendered_literals = rendered_solution_literals(&rendered);
    assert_eq!(lines[0], "o 1");
    assert_eq!(lines[1], "s OPTIMUM FOUND");
    assert!(
        rendered.lines().any(|line| line.starts_with("v ")),
        "interrupted incumbent with a witness must emit at least one v-line: {rendered}"
    );
    assert_eq!(
        rendered_literals.len(),
        51,
        "competition witness output should cover all 51 PB variables across wrapped v-lines"
    );
    assert_eq!(
        rendered_literals
            .iter()
            .filter(|lit| !lit.starts_with('-'))
            .count(),
        1,
        "exactly one positive witness literal should remain in the emitted assignment"
    );
}

#[test]
fn test_testscheduling_scale_root_precheck_does_not_frame_feasible_opt_as_unsat() {
    let instance = testscheduling_scale_feasible_root_precheck_instance();
    let objective = instance
        .objective
        .as_ref()
        .expect("synthetic TestScheduling-scale row should carry an objective");
    let term_flag = AtomicBool::new(false);
    let mut improvements = Vec::new();

    let outcome = portfolio::solve_optimization_portfolio_with_timings(
        &instance,
        objective,
        Some(Duration::from_secs(5)),
        Instant::now(),
        &term_flag,
        &mut |obj_value, assignment| improvements.push((obj_value, assignment.to_vec())),
    );
    let result = outcome.solution;

    assert_ne!(
        result.status,
        PbStatus::Unsatisfiable,
        "TestScheduling-scale feasible input has no proof-backed UNSAT basis; root-precheck/exact shortcuts must fail closed, timings={:?}",
        outcome.timings
    );
    assert_eq!(
        result.status,
        PbStatus::OptimumFound,
        "synthetic feasible input should solve to optimum, timings={:?}",
        outcome.timings
    );
    assert_eq!(result.objective, Some(0));
    assert_full_valid_incumbent(
        &instance,
        objective,
        0,
        &result.assignment,
        "TestScheduling-scale root-precheck regression",
    );
    assert_eq!(
        eval_objective_exact(objective, &result.assignment),
        Ok(0),
        "exact objective recomputation should confirm the zero-cost witness"
    );
    for (obj_value, assignment) in improvements {
        assert_full_valid_incumbent(
            &instance,
            objective,
            obj_value,
            &assignment,
            "TestScheduling-scale incumbent callback",
        );
    }
}

#[test]
fn test_unsupported_coefficient_parse_errors_are_detectable_for_competition_mapping() {
    // i128::MAX is 170141183460469231731687303715884105727; the literals below are
    // i128::MAX + 1, the first magnitude that exceeds the (now i128-wide) supported
    // coefficient range and must still surface as UNSUPPORTED/overflow.
    let opb_err = parse_opb(
        "* #variable= 1 #constraint= 1\n+170141183460469231731687303715884105728 x1 >= 1 ;\n",
    )
    .expect_err("overflowing OPB coefficients must be rejected");
    let wbo_err = parse_wbo("soft: 10 ;\n[170141183460469231731687303715884105728] +1 x1 >= 1 ;\n")
        .expect_err("overflowing WBO weights must be rejected");

    for err in [opb_err, wbo_err] {
        assert!(
            err.is_unsupported_coefficient(),
            "PB competition callers should be able to map overflow to UNSUPPORTED: {err}"
        );
        assert_eq!(err.line(), 2);
        assert!(
            matches!(err, ParseError::CoefficientOverflow { .. }),
            "current parser should surface overflow via the compatibility variant: {err:?}"
        );
    }
}

#[test]
fn test_optimization_portfolio_rejects_objective_range_overflow() {
    // +i128::MAX on x1 and +1 on x2: each coefficient fits the (now i128-wide)
    // supported range and parses, but their sum (i128::MAX + 1) overflows the i128
    // objective accumulator, so the achievable objective range no longer fits.
    let instance = parse_opb(
        "* #variable= 2 #constraint= 1\nmin: +170141183460469231731687303715884105727 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n",
    )
    .expect("boundary objective coefficients should parse");
    let objective = instance
        .objective
        .as_ref()
        .expect("optimization instance should carry an objective");
    assert!(
        !objective_range_fits_i64(objective),
        "objective range must reject assignments whose value would saturate i128 output"
    );

    let term_flag = AtomicBool::new(false);
    let mut improvements = 0usize;
    let result = portfolio::solve_optimization_portfolio(
        &instance,
        objective,
        Some(Duration::from_secs(5)),
        Instant::now(),
        &term_flag,
        &mut |_, _| {
            improvements += 1;
        },
    );

    assert_eq!(result.status, PbStatus::Unsupported);
    assert_eq!(result.objective, None);
    assert!(result.assignment.is_empty());
    assert_eq!(
        improvements, 0,
        "unsupported objectives must not emit incumbents"
    );

    let rendered = render_solution(&result);
    assert_eq!(rendered, "s UNSUPPORTED\n");
}

#[test]
fn test_public_exact_objective_eval_preserves_wide_sum() {
    let objective = PbObjective {
        terms: vec![term(i128::from(i64::MAX), lit(1)), term(1, lit(2))],
    };

    assert_eq!(
        eval_objective_exact(&objective, &[true, true]),
        Ok(i128::from(i64::MAX) + 1)
    );
}

#[test]
fn test_proof_writer_interruption_does_not_emit_sat_or_unsat_conclusion() {
    let instance = parse_opb("* #variable= 1 #constraint= 1\n+1 x1 >= 1 ;\n")
        .expect("simple proof instance should parse");
    let sink = SharedBuffer::default();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, sink.clone())
        .expect("proof writer should initialize");

    let result = solver.solve_interruptible(|| true);
    assert_eq!(result, PbCdclResult::Unknown);
    solver
        .conclude_proof()
        .expect("flushing an interrupted proof should not error");

    let rendered = sink.as_string();
    let lines: Vec<&str> = rendered.lines().collect();
    assert_eq!(
        lines.len(),
        2,
        "an immediately interrupted proof should emit only the VeriPB header skeleton: {rendered}"
    );
    assert_eq!(lines[0], "pseudo-Boolean proof version 3.0");
    assert!(
        lines[1].starts_with("f "),
        "proof output must include the input-constraint count header: {rendered}"
    );
    assert!(
        !rendered.contains("output NONE"),
        "interrupted proof mode must not claim SAT: {rendered}"
    );
    assert!(
        !rendered.contains("conclusion UNSAT"),
        "interrupted proof mode must not claim UNSAT: {rendered}"
    );
}

/// Loads a bundled OPB instance from `tests/instances/`.
fn load_bundled_instance(name: &str) -> PbInstance {
    let path = format!("{}/tests/instances/{name}", env!("CARGO_MANIFEST_DIR"));
    let content =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("failed to read {path}: {e}"));
    parse_opb(&content).unwrap_or_else(|e| panic!("failed to parse {path}: {e}"))
}

/// Drives the optimization portfolio on a bundled instance and asserts a PROVEN
/// optimum equal to `expected_opt`, with a witness that satisfies every original
/// constraint and whose objective matches.
fn assert_portfolio_proves_optimum(file: &str, expected_opt: i128) {
    let instance = load_bundled_instance(file);
    let objective = instance
        .objective
        .as_ref()
        .unwrap_or_else(|| panic!("{file}: must carry a minimization objective"));
    let term_flag = AtomicBool::new(false);

    let result = portfolio::solve_optimization_portfolio(
        &instance,
        objective,
        Some(Duration::from_secs(45)),
        Instant::now(),
        &term_flag,
        &mut |_obj_value, _assignment| {},
    );

    // NOTE: the injcomp family is now closed DIRECTLY by the structural
    // Hall/cardinality certificate (`optimize::injcomp`), which proves the
    // optimum from a re-verified construction WITHOUT an anytime descent — so no
    // incumbent is streamed before the proof (exactly like the König /
    // clique-coloring structural paths). The essential property re-asserted here
    // is the PROVEN optimum + verified witness.
    assert_eq!(
        result.status,
        PbStatus::OptimumFound,
        "{file}: must be PROVEN optimal (structural injcomp cert; was SATISFIABLE before)"
    );
    assert_eq!(
        result.objective,
        Some(expected_opt),
        "{file}: optimum must be {expected_opt} (Exact and RoundingSat agree)"
    );
    assert!(
        verify_all_constraints(&instance.constraints, &result.assignment),
        "{file}: proven-optimal witness must satisfy every original PB constraint"
    );
    assert_eq!(
        eval_objective(objective, &result.assignment),
        expected_opt,
        "{file}: witness objective must equal the proven optimum {expected_opt}"
    );
}

/// Regression: the `injcomp` injection family (real PB24 OPT-LIN). Native-OLL
/// finds the optimal incumbent quickly but its plain stratified descent cannot
/// PROVE optimality in budget. These instances are now closed by the structural
/// Hall/cardinality certificate (`optimize::injcomp`): an EXACT recognizer of the
/// layered injective-composition family pairs the proven layered Hall lower bound
/// (`#M1 edges <= m`, each composition layer `<= s_t`) with a re-verified
/// diagonal upper bound, emitting OPTIMUM only when both meet. Before these
/// changes both instances returned SATISFIABLE; they must now return the proven
/// optimum (cross-checked against Exact and RoundingSat).
///
/// `size_12` is a `3layers_maxall` member (opt `-2m = -22`); `size_18` is a
/// `3layers_maxfirst` member (opt `-m = -17`).
#[test]
fn test_injcomp_size12_structural_cert_proves_optimum() {
    assert_portfolio_proves_optimum("injcomp_opt_3layers_maxall_lastlayerdecr1_size_12.opb", -22);
}

#[test]
fn test_injcomp_size18_structural_cert_proves_optimum() {
    assert_portfolio_proves_optimum(
        "injcomp_opt_3layers_maxfirst_lastlayerdecr1_size_18.opb",
        -17,
    );
}

/// Locates the PB25 BNN-verification instance the earlier wrong-UNSAT regression
/// came from. Overridable via `AY_PB_BNN_OPB`; otherwise resolved under the
/// checkout-relative `benchmarks/pb-comp`.
/// Returns `None` (test skips) when the multi-megabyte instance
/// is not present, so CI without the benchmark tree stays green.
fn find_bnn_back_image_73_norm1() -> Option<std::path::PathBuf> {
    if let Some(p) = std::env::var_os("AY_PB_BNN_OPB").map(std::path::PathBuf::from) {
        if p.is_file() {
            return Some(p);
        }
    }
    // B14: the AY_PBCOMP_BENCH_ROOT override nothing set is deleted; a
    // relocated corpus is a symlink at the checkout-relative path.
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../benchmarks/pb-comp");
    let fallback = root.join(
        "PB25/normalized-PB25/OPT-LIN/sakai/\
         PB25-bnn-verification-20250419/instances/\
         normalized-bnn_mnist_back_image_73_label5_adversarial_norm_1.opb",
    );
    fallback.is_file().then_some(fallback)
}

/// SOUNDNESS REGRESSION: the BNN-verification family blows up the SAT encoding and
/// is genuinely hard for the native cutting-planes engine, which cannot find even a
/// feasible point in budget. The one outcome that must NEVER happen is a spurious
/// UNSATISFIABLE (an earlier wrong-UNSAT came from exactly this family). Whatever
/// the verdict — UNKNOWN, SATISFIABLE, or a verified OPTIMUM — it must not be
/// UNSATISFIABLE, because the instance is satisfiable (Exact and RoundingSat both
/// find feasible points / prove OPTIMUM). Runs with a short budget so it stays a
/// fast guard; skips when the benchmark instance is absent.
#[test]
fn test_bnn_back_image_73_norm1_never_wrong_unsat() {
    let Some(path) = find_bnn_back_image_73_norm1() else {
        eprintln!("skipping bnn wrong-UNSAT guard: instance not present");
        return;
    };
    let content = std::fs::read_to_string(&path).expect("bnn instance should be readable");
    let instance = parse_opb(&content).expect("bnn instance should parse");
    let objective = instance
        .objective
        .as_ref()
        .expect("bnn instance carries a minimization objective");
    let term_flag = AtomicBool::new(false);

    let result = portfolio::solve_optimization_portfolio(
        &instance,
        objective,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
        &mut |_obj_value, _assignment| {},
    );

    assert_ne!(
        result.status,
        PbStatus::Unsatisfiable,
        "bnn instance is satisfiable; the solver must never report a (wrong) UNSAT"
    );
    // If any definitive incumbent/optimum was returned it must be a real witness.
    if matches!(
        result.status,
        PbStatus::Satisfiable | PbStatus::OptimumFound
    ) {
        assert!(
            verify_all_constraints(&instance.constraints, &result.assignment),
            "any returned bnn witness must satisfy every original PB constraint"
        );
    }
}
