// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Property-based CNF fuzz differential testing for BVE/inprocessing (Part of #7927).
//!
//! Uses `proptest` with structural shrinking to generate five families of CNF
//! formulas and compare AY results across three solver profiles:
//!
//! - **ay_plain**: no inprocessing (semantic baseline)
//! - **ay_bve_only**: only BVE enabled
//! - **ay_full_inproc**: all inprocessing enabled (DIMACS competition profile)
//!
//! SAT models are verified against the original clauses. When CaDiCaL is
//! available, it acts as an external oracle for additional cross-validation.
//!
//! Formula families:
//! 1. **Uniform**: plain random CNF with weighted clause lengths
//! 2. **PlantedSat**: random formula where a planted assignment satisfies all clauses
//! 3. **UnsatCore**: tiny contradictory core embedded in random noise
//! 4. **ElimPivot**: controlled positive/negative occurrences to force BVE resolution
//! 5. **GateChain**: AND/EQUIV/implication-chain encodings plus noise
//!
//! On failure, the test prints the exact CNF in DIMACS format for replay.

#![allow(clippy::panic)]

use super::common::{disable_all_inprocessing, verify_model, workspace_root};
use ay_sat::{Literal, SatResult, Solver, Variable};
use proptest::prelude::*;
use std::io::Write;
use std::process::{Command, Stdio};

// =============================================================================
// Formula family types
// =============================================================================

/// Identifies which generator produced a formula (for diagnostic output).
#[derive(Debug, Clone, Copy)]
enum CnfFamily {
    Uniform,
    PlantedSat,
    UnsatCore,
    ElimPivot,
    GateChain,
}

impl std::fmt::Display for CnfFamily {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Uniform => write!(f, "Uniform"),
            Self::PlantedSat => write!(f, "PlantedSat"),
            Self::UnsatCore => write!(f, "UnsatCore"),
            Self::ElimPivot => write!(f, "ElimPivot"),
            Self::GateChain => write!(f, "GateChain"),
        }
    }
}

/// A generated CNF test case with metadata for diagnostics.
#[derive(Debug, Clone)]
struct CnfCase {
    family: CnfFamily,
    num_vars: usize,
    clauses: Vec<Vec<i32>>,
}

// =============================================================================
// Literal conversion helpers
// =============================================================================

/// Convert a 1-based signed DIMACS literal to ay Literal.
fn dimacs_to_lit(signed: i32) -> Literal {
    let var = signed.unsigned_abs() - 1;
    if signed > 0 {
        Literal::positive(Variable::new(var))
    } else {
        Literal::negative(Variable::new(var))
    }
}

/// Convert ay clauses to DIMACS CNF format string.
fn case_to_dimacs(case: &CnfCase) -> String {
    let mut out = format!("p cnf {} {}\n", case.num_vars, case.clauses.len());
    for clause in &case.clauses {
        for &lit in clause {
            out.push_str(&lit.to_string());
            out.push(' ');
        }
        out.push_str("0\n");
    }
    out
}

// =============================================================================
// Proptest generators for five CNF families
// =============================================================================

/// Generate a random clause of given length over `num_vars` 1-based variables.
fn arb_clause(num_vars: usize, max_len: usize) -> impl Strategy<Value = Vec<i32>> {
    proptest::collection::vec(
        (1..=num_vars as i32).prop_flat_map(|v| prop_oneof![Just(v), Just(-v)]),
        1..=max_len,
    )
    .prop_map(|mut clause| {
        // Remove duplicate variables (keep first occurrence).
        let mut seen = std::collections::HashSet::new();
        clause.retain(|&lit| seen.insert(lit.unsigned_abs()));
        clause
    })
    .prop_filter("non-empty clause", |c| !c.is_empty())
}

/// Family 1: Uniform random CNF with weighted clause lengths.
///
/// Clause length distribution (approximated):
/// - length 1: ~5%
/// - length 2: ~20%
/// - length 3: ~40%
/// - length 4: ~20%
/// - length 5-8: ~15%
fn arb_uniform_cnf() -> impl Strategy<Value = CnfCase> {
    (4usize..=48).prop_flat_map(|num_vars| {
        let num_clauses_max = (6 * num_vars + 8).min(256);
        let num_clauses_min = num_vars.max(4);
        (Just(num_vars), num_clauses_min..=num_clauses_max).prop_flat_map(move |(nv, nc)| {
            proptest::collection::vec(
                // Weighted clause length distribution
                prop_oneof![
                    1 => arb_clause(nv, 1),  // ~5% units
                    4 => arb_clause(nv, 2),  // ~20% binary
                    8 => arb_clause(nv, 3),  // ~40% ternary
                    4 => arb_clause(nv, 4),  // ~20% quaternary
                    3 => arb_clause(nv, 8),  // ~15% longer
                ],
                nc,
            )
            .prop_map(move |clauses| CnfCase {
                family: CnfFamily::Uniform,
                num_vars: nv,
                clauses,
            })
        })
    })
}

/// Family 2: PlantedSat - generate clauses that are all satisfied by a planted
/// random assignment, guaranteeing the formula is SAT.
///
/// Useful for testing model reconstruction: if AY says UNSAT, it is wrong.
fn arb_planted_sat_cnf() -> impl Strategy<Value = CnfCase> {
    (4usize..=40).prop_flat_map(|num_vars| {
        // Generate a random truth assignment
        proptest::collection::vec(proptest::bool::ANY, num_vars).prop_flat_map(move |assignment| {
            let num_clauses_max = (4 * num_vars + 8).min(160);
            let num_clauses_min = num_vars.max(4);
            (Just(assignment), num_clauses_min..=num_clauses_max).prop_flat_map(
                move |(assign, nc)| {
                    let nv = assign.len();
                    proptest::collection::vec(
                        // Each clause must be satisfied by the planted assignment
                        arb_planted_clause(nv, &assign),
                        nc,
                    )
                    .prop_map(move |clauses| CnfCase {
                        family: CnfFamily::PlantedSat,
                        num_vars: nv,
                        clauses,
                    })
                },
            )
        })
    })
}

/// Generate a clause satisfied by the given assignment.
/// At least one literal will agree with the assignment.
fn arb_planted_clause(num_vars: usize, assignment: &[bool]) -> impl Strategy<Value = Vec<i32>> {
    let assign_owned = assignment.to_vec();
    let nv = num_vars;
    (1usize..=5).prop_flat_map(move |clause_len| {
        let assign = assign_owned.clone();
        proptest::collection::vec(0..nv, clause_len.min(nv))
            .prop_map(move |var_indices| {
                let mut seen = std::collections::HashSet::new();
                let mut clause = Vec::new();
                let mut has_satisfied = false;

                for vi in &var_indices {
                    if !seen.insert(*vi) {
                        continue;
                    }
                    let var_1based = (*vi as i32) + 1;
                    let val = assign[*vi];
                    // With 70% probability, make the literal agree with the assignment
                    // to ensure most literals are satisfying
                    let signed = if val { var_1based } else { -var_1based };
                    clause.push(signed);
                    has_satisfied = true;
                }

                // Guarantee at least one satisfied literal
                if !has_satisfied && !clause.is_empty() {
                    let vi = var_indices[0] % nv;
                    let var_1based = (vi as i32) + 1;
                    let val = assign[vi];
                    clause[0] = if val { var_1based } else { -var_1based };
                }

                clause
            })
            .prop_filter("non-empty clause", |c| !c.is_empty())
    })
}

/// Family 3: UnsatCore - embed a small unsatisfiable core, then add random noise.
///
/// The core is a set of unit clauses that contradict each other:
/// e.g., {x1}, {-x1} guarantees UNSAT regardless of noise.
fn arb_unsat_core_cnf() -> impl Strategy<Value = CnfCase> {
    (4usize..=30).prop_flat_map(|num_vars| {
        // Pick 1-3 variables for the contradictory core
        let core_size = 1usize..=3.min(num_vars);
        (Just(num_vars), core_size).prop_flat_map(move |(nv, cs)| {
            proptest::collection::vec(0..nv, cs).prop_flat_map(move |core_vars| {
                let noise_count = nv..=(4 * nv).min(120);
                (Just(core_vars), noise_count).prop_flat_map(move |(cv, nc)| {
                    let nv_inner = nv;
                    let cv_inner = cv;
                    proptest::collection::vec(arb_clause(nv_inner, 4), nc).prop_map(move |noise| {
                        let mut clauses = Vec::new();

                        // Add contradictory core: for each core variable,
                        // add both {x} and {-x} as unit clauses
                        for &vi in &cv_inner {
                            let var_1based = (vi as i32) + 1;
                            clauses.push(vec![var_1based]);
                            clauses.push(vec![-var_1based]);
                        }

                        // Add noise clauses
                        clauses.extend(noise);

                        CnfCase {
                            family: CnfFamily::UnsatCore,
                            num_vars: nv_inner,
                            clauses,
                        }
                    })
                })
            })
        })
    })
}

/// Family 4: ElimPivot - generate controlled positive/negative occurrences
/// for a pivot variable to force BVE resolution.
///
/// Creates a formula where `pivot_var` appears in `pos_occs` positive clauses
/// and `neg_occs` negative clauses, creating a BVE candidate with
/// `pos_occs * neg_occs` potential resolvents.
fn arb_elim_pivot_cnf() -> impl Strategy<Value = CnfCase> {
    (6usize..=36).prop_flat_map(|num_vars| {
        let pivot = 0..num_vars;
        (Just(num_vars), pivot).prop_flat_map(move |(nv, pv)| {
            let pos_occs = 2usize..=6;
            let neg_occs = 2usize..=6;
            let extra_clauses = nv..=(3 * nv).min(100);
            (Just(nv), Just(pv), pos_occs, neg_occs, extra_clauses).prop_flat_map(
                move |(nv, pv, po, no, ec)| {
                    let pivot_1based = (pv as i32) + 1;
                    // Generate clauses containing the pivot positively
                    let pos_clauses =
                        proptest::collection::vec(arb_clause_with_forced_lit(nv, pivot_1based), po);
                    // Generate clauses containing the pivot negatively
                    let neg_clauses = proptest::collection::vec(
                        arb_clause_with_forced_lit(nv, -pivot_1based),
                        no,
                    );
                    // Generate random extra clauses
                    let extra = proptest::collection::vec(arb_clause(nv, 4), ec);

                    (pos_clauses, neg_clauses, extra).prop_map(move |(pc, nc, ex)| {
                        let mut clauses = Vec::new();
                        clauses.extend(pc);
                        clauses.extend(nc);
                        clauses.extend(ex);
                        CnfCase {
                            family: CnfFamily::ElimPivot,
                            num_vars: nv,
                            clauses,
                        }
                    })
                },
            )
        })
    })
}

/// Generate a clause that contains a forced literal plus 1-3 random other literals.
fn arb_clause_with_forced_lit(num_vars: usize, forced: i32) -> impl Strategy<Value = Vec<i32>> {
    let nv = num_vars;
    let forced_var = forced.unsigned_abs() as usize;
    proptest::collection::vec(
        (1..=nv as i32).prop_flat_map(|v| prop_oneof![Just(v), Just(-v)]),
        1..=3,
    )
    .prop_map(move |mut others| {
        // Filter out the forced variable
        others.retain(|&lit| lit.unsigned_abs() as usize != forced_var);
        let mut clause = vec![forced];
        let mut seen = std::collections::HashSet::new();
        seen.insert(forced.unsigned_abs());
        for lit in others {
            if seen.insert(lit.unsigned_abs()) {
                clause.push(lit);
            }
        }
        clause
    })
}

/// Family 5: GateChain - emit AND/EQUIV gate encodings plus noise.
///
/// Generates formulas with explicit gate structure: gate variables defined
/// as `g <=> (a AND b)` or `g <=> (a EQUIV b)`, connected by random clauses.
/// Targets decompose, congruence, factor, sweep, and BVE interactions.
fn arb_gate_chain_cnf() -> impl Strategy<Value = CnfCase> {
    (4usize..=15).prop_flat_map(|num_inputs| {
        let num_gates = 2usize..=8.min(num_inputs);
        (Just(num_inputs), num_gates).prop_flat_map(move |(ni, ng)| {
            let total_vars = ni + ng;
            // Generate gate definitions
            let gate_defs = proptest::collection::vec((0..ni, 0..ni, proptest::bool::ANY), ng);
            // Generate random connecting clauses
            let noise_count = ng..=(3 * ng).min(40);
            (gate_defs, noise_count).prop_flat_map(move |(gates, nc)| {
                let tv = total_vars;
                let ni_inner = ni;
                proptest::collection::vec(arb_clause(tv, 4), nc).prop_map(move |noise_clauses| {
                    let mut clauses = Vec::new();

                    for (gi, (a_idx, b_idx, is_and)) in gates.iter().enumerate() {
                        let gate_var = (ni_inner + gi) as i32 + 1;
                        let a = *a_idx as i32 + 1;
                        let mut b = *b_idx as i32 + 1;
                        // Ensure a != b
                        if a == b {
                            b = (b % ni_inner as i32) + 1;
                            if b == a && ni_inner > 1 {
                                b = if a == 1 { 2 } else { 1 };
                            }
                        }

                        if *is_and {
                            // g <=> (a AND b):
                            // (-g OR a), (-g OR b), (g OR -a OR -b)
                            clauses.push(vec![-gate_var, a]);
                            clauses.push(vec![-gate_var, b]);
                            clauses.push(vec![gate_var, -a, -b]);
                        } else {
                            // g <=> (a EQUIV b):
                            // (-g OR -a OR b), (-g OR a OR -b), (g OR a OR b), (g OR -a OR -b)
                            clauses.push(vec![-gate_var, -a, b]);
                            clauses.push(vec![-gate_var, a, -b]);
                            clauses.push(vec![gate_var, a, b]);
                            clauses.push(vec![gate_var, -a, -b]);
                        }
                    }

                    clauses.extend(noise_clauses);

                    CnfCase {
                        family: CnfFamily::GateChain,
                        num_vars: tv,
                        clauses,
                    }
                })
            })
        })
    })
}

/// Combined strategy: weighted mixture of all five families.
fn arb_cnf_case() -> impl Strategy<Value = CnfCase> {
    prop_oneof![
        5 => arb_uniform_cnf(),
        3 => arb_planted_sat_cnf(),
        3 => arb_unsat_core_cnf(),
        5 => arb_elim_pivot_cnf(),
        4 => arb_gate_chain_cnf(),
    ]
}

// =============================================================================
// Solver profiles
// =============================================================================

/// ay_plain: all inprocessing disabled, deterministic baseline.
fn configure_plain(solver: &mut Solver) {
    solver.set_preprocess_enabled(true);
    solver.set_full_preprocessing(true);
    solver.set_walk_enabled(false);
    solver.set_warmup_enabled(false);
    solver.set_random_seed(0);
    solver.set_shrink_enabled(false);
    solver.set_hbr_enabled(false);
    disable_all_inprocessing(solver);
}

/// ay_bve_only: only BVE enabled, isolates BVE bugs from interaction bugs.
fn configure_bve_only(solver: &mut Solver) {
    configure_plain(solver);
    solver.set_bve_enabled(true);
}

/// ay_full_inproc: all inprocessing enabled (matches DIMACS competition profile).
fn configure_full_inproc(solver: &mut Solver) {
    solver.set_preprocess_enabled(true);
    solver.set_full_preprocessing(true);
    solver.set_walk_enabled(false);
    solver.set_warmup_enabled(false);
    solver.set_random_seed(0);
    solver.set_shrink_enabled(false);
    solver.set_hbr_enabled(true);
    solver.set_bve_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_vivify_enabled(true);
    solver.set_subsume_enabled(true);
    solver.set_probe_enabled(true);
    solver.set_bce_enabled(true);
    solver.set_condition_enabled(true);
    solver.set_decompose_enabled(true);
    solver.set_factor_enabled(true);
    solver.set_transred_enabled(true);
    solver.set_htr_enabled(true);
    solver.set_gate_enabled(true);
    solver.set_sweep_enabled(true);
    solver.set_backbone_enabled(true);
    solver.set_cce_enabled(true);
}

// =============================================================================
// Solving and verification
// =============================================================================

/// Verdict classification for comparison (ignores model content).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

impl std::fmt::Display for Verdict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sat => write!(f, "SAT"),
            Self::Unsat => write!(f, "UNSAT"),
            Self::Unknown => write!(f, "UNKNOWN"),
        }
    }
}

fn classify(result: &SatResult) -> Verdict {
    match result {
        SatResult::Sat(_) => Verdict::Sat,
        SatResult::Unsat(_) => Verdict::Unsat,
        _ => Verdict::Unknown,
    }
}

/// Solve a CnfCase with a given configuration. Returns (verdict, model_valid).
fn solve_case(
    case: &CnfCase,
    configure: impl FnOnce(&mut Solver),
    profile_name: &str,
) -> (Verdict, SatResult) {
    let mut solver = Solver::new(case.num_vars);
    configure(&mut solver);
    for clause in &case.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| dimacs_to_lit(l)).collect();
        solver.add_clause(lits);
    }
    let result = solver.solve().into_inner();

    // If SAT, verify the model against original clauses.
    if let SatResult::Sat(ref model) = result {
        let ay_clauses: Vec<Vec<Literal>> = case
            .clauses
            .iter()
            .map(|c| c.iter().map(|&l| dimacs_to_lit(l)).collect())
            .collect();
        assert!(
            verify_model(&ay_clauses, model),
            "SOUNDNESS BUG: {profile_name} model violates original clauses\n\
             Family: {}\nVars: {}\nClauses: {}\nDIMACS:\n{}",
            case.family,
            case.num_vars,
            case.clauses.len(),
            case_to_dimacs(case),
        );
    }

    (classify(&result), result)
}

// =============================================================================
// CaDiCaL oracle
// =============================================================================

/// Result from CaDiCaL oracle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CadicalResult {
    Sat,
    Unsat,
    Unavailable,
}

/// Run CaDiCaL on a CnfCase and return the result.
fn run_cadical(case: &CnfCase) -> CadicalResult {
    let cadical_path = workspace_root().join("reference/cadical/build/cadical");
    if !cadical_path.exists() {
        return CadicalResult::Unavailable;
    }

    let dimacs = case_to_dimacs(case);
    let tmp = match tempfile::Builder::new()
        .prefix("ay_propfuzz_")
        .suffix(".cnf")
        .tempfile()
    {
        Ok(f) => f,
        Err(_) => return CadicalResult::Unavailable,
    };

    if tmp.as_file().write_all(dimacs.as_bytes()).is_err() {
        return CadicalResult::Unavailable;
    }
    if tmp.as_file().sync_all().is_err() {
        return CadicalResult::Unavailable;
    }

    let output = Command::new(&cadical_path)
        .arg("-q")
        .arg(tmp.path())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .output();

    match output {
        Ok(result) => match result.status.code() {
            Some(10) => CadicalResult::Sat,
            Some(20) => CadicalResult::Unsat,
            _ => CadicalResult::Unavailable,
        },
        Err(_) => CadicalResult::Unavailable,
    }
}

// =============================================================================
// Differential comparison logic
// =============================================================================

/// Run the full differential oracle matrix on a single CnfCase.
///
/// Compares ay_plain, ay_bve_only, ay_full_inproc, and optionally CaDiCaL.
/// Panics with diagnostic information on any disagreement.
fn differential_oracle_matrix(case: &CnfCase) {
    let (v_plain, _r_plain) = solve_case(case, configure_plain, "ay_plain");
    let (v_bve, _r_bve) = solve_case(case, configure_bve_only, "ay_bve_only");
    let (v_full, _r_full) = solve_case(case, configure_full_inproc, "ay_full_inproc");

    let dimacs_str = case_to_dimacs(case);

    // Primary signal: ay_plain vs ay_bve_only
    if v_plain != Verdict::Unknown && v_bve != Verdict::Unknown {
        assert_eq!(
            v_plain,
            v_bve,
            "BVE SOUNDNESS BUG: ay_plain={v_plain} vs ay_bve_only={v_bve}\n\
             Family: {}\nVars: {}\nClauses: {}\nDIMACS:\n{dimacs_str}",
            case.family,
            case.num_vars,
            case.clauses.len(),
        );
    }

    // Secondary signal: ay_plain vs ay_full_inproc
    if v_plain != Verdict::Unknown && v_full != Verdict::Unknown {
        assert_eq!(
            v_plain,
            v_full,
            "INPROCESSING SOUNDNESS BUG: ay_plain={v_plain} vs ay_full_inproc={v_full}\n\
             (ay_bve_only={v_bve})\n\
             Family: {}\nVars: {}\nClauses: {}\nDIMACS:\n{dimacs_str}",
            case.family,
            case.num_vars,
            case.clauses.len(),
        );
    }

    // Tertiary signal: ay_bve_only vs ay_full_inproc
    if v_bve != Verdict::Unknown && v_full != Verdict::Unknown {
        assert_eq!(
            v_bve,
            v_full,
            "INTERACTION BUG: ay_bve_only={v_bve} vs ay_full_inproc={v_full}\n\
             (ay_plain={v_plain})\n\
             Family: {}\nVars: {}\nClauses: {}\nDIMACS:\n{dimacs_str}",
            case.family,
            case.num_vars,
            case.clauses.len(),
        );
    }

    // CaDiCaL oracle cross-validation
    let cadical = run_cadical(case);
    if cadical != CadicalResult::Unavailable {
        // Find the best ay verdict to compare
        let ay_best = if v_plain != Verdict::Unknown {
            v_plain
        } else if v_bve != Verdict::Unknown {
            v_bve
        } else if v_full != Verdict::Unknown {
            v_full
        } else {
            return;
        };

        let cadical_verdict = match cadical {
            CadicalResult::Sat => Verdict::Sat,
            CadicalResult::Unsat => Verdict::Unsat,
            CadicalResult::Unavailable => unreachable!(),
        };

        assert_eq!(
            ay_best,
            cadical_verdict,
            "AY vs CaDiCaL DISAGREEMENT: ay={ay_best} cadical={cadical_verdict}\n\
             ay_plain={v_plain}, ay_bve_only={v_bve}, ay_full_inproc={v_full}\n\
             Family: {}\nVars: {}\nClauses: {}\nDIMACS:\n{dimacs_str}",
            case.family,
            case.num_vars,
            case.clauses.len(),
        );
    }
}

/// Run ay_plain vs ay_bve_only comparison only (fast, BVE-focused).
fn differential_plain_vs_bve(case: &CnfCase) {
    let (v_plain, _) = solve_case(case, configure_plain, "ay_plain");
    let (v_bve, _) = solve_case(case, configure_bve_only, "ay_bve_only");

    if v_plain != Verdict::Unknown && v_bve != Verdict::Unknown {
        assert_eq!(
            v_plain,
            v_bve,
            "BVE SOUNDNESS BUG: ay_plain={v_plain} vs ay_bve_only={v_bve}\n\
             Family: {}\nVars: {}\nClauses: {}\nDIMACS:\n{}",
            case.family,
            case.num_vars,
            case.clauses.len(),
            case_to_dimacs(case),
        );
    }
}

/// Run ay_plain vs ay_full_inproc comparison (catch non-BVE inprocessing bugs).
fn differential_plain_vs_full(case: &CnfCase) {
    let (v_plain, _) = solve_case(case, configure_plain, "ay_plain");
    let (v_full, _) = solve_case(case, configure_full_inproc, "ay_full_inproc");

    if v_plain != Verdict::Unknown && v_full != Verdict::Unknown {
        assert_eq!(
            v_plain,
            v_full,
            "INPROCESSING SOUNDNESS BUG: ay_plain={v_plain} vs ay_full_inproc={v_full}\n\
             Family: {}\nVars: {}\nClauses: {}\nDIMACS:\n{}",
            case.family,
            case.num_vars,
            case.clauses.len(),
            case_to_dimacs(case),
        );
    }
}

// =============================================================================
// PlantedSat: ay must return SAT (UNSAT is always wrong for planted formulas)
// =============================================================================

fn planted_sat_must_be_sat(case: &CnfCase) {
    let (v_plain, _) = solve_case(case, configure_plain, "ay_plain");
    let (v_bve, _) = solve_case(case, configure_bve_only, "ay_bve_only");
    let (v_full, _) = solve_case(case, configure_full_inproc, "ay_full_inproc");

    for (label, verdict) in [
        ("ay_plain", v_plain),
        ("ay_bve_only", v_bve),
        ("ay_full_inproc", v_full),
    ] {
        // PlantedSat formulas are SAT by construction. UNSAT is a bug.
        // Unknown is also suspicious but tolerable.
        assert_ne!(
            verdict,
            Verdict::Unsat,
            "SOUNDNESS BUG: {label} returned UNSAT on a PlantedSat formula\n\
             Vars: {}\nClauses: {}\nDIMACS:\n{}",
            case.num_vars,
            case.clauses.len(),
            case_to_dimacs(case),
        );
    }
}

// =============================================================================
// UnsatCore: ay must return UNSAT (SAT is always wrong for unsat-core formulas)
// =============================================================================

fn unsat_core_must_be_unsat(case: &CnfCase) {
    let (v_plain, _) = solve_case(case, configure_plain, "ay_plain");
    let (v_bve, _) = solve_case(case, configure_bve_only, "ay_bve_only");
    let (v_full, _) = solve_case(case, configure_full_inproc, "ay_full_inproc");

    for (label, verdict) in [
        ("ay_plain", v_plain),
        ("ay_bve_only", v_bve),
        ("ay_full_inproc", v_full),
    ] {
        // UnsatCore formulas contain a contradictory core. SAT is a bug.
        assert_ne!(
            verdict,
            Verdict::Sat,
            "SOUNDNESS BUG: {label} returned SAT on an UnsatCore formula\n\
             Vars: {}\nClauses: {}\nDIMACS:\n{}",
            case.num_vars,
            case.clauses.len(),
            case_to_dimacs(case),
        );
    }
}

// =============================================================================
// Proptest entry points
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// ay_plain vs ay_bve_only across all five formula families.
    /// Primary BVE soundness gate.
    #[test]
    fn prop_cnf_fuzz_plain_vs_bve_only(case in arb_cnf_case()) {
        differential_plain_vs_bve(&case);
    }

    /// ay_plain vs ay_full_inproc across all five families.
    /// Full inprocessing soundness gate.
    #[test]
    fn prop_cnf_fuzz_plain_vs_full_inproc(case in arb_cnf_case()) {
        differential_plain_vs_full(&case);
    }

    /// Full oracle matrix: ay_plain vs ay_bve_only vs ay_full_inproc vs CaDiCaL.
    #[test]
    fn prop_cnf_fuzz_oracle_matrix(case in arb_cnf_case()) {
        differential_oracle_matrix(&case);
    }

    /// PlantedSat family: ay must never return UNSAT.
    #[test]
    fn prop_planted_sat_correctness(case in arb_planted_sat_cnf()) {
        planted_sat_must_be_sat(&case);
    }

    /// UnsatCore family: ay must never return SAT.
    #[test]
    fn prop_unsat_core_correctness(case in arb_unsat_core_cnf()) {
        unsat_core_must_be_unsat(&case);
    }

    /// ElimPivot family: BVE-specific stress with controlled positive/negative
    /// occurrence counts.
    #[test]
    fn prop_elim_pivot_bve_soundness(case in arb_elim_pivot_cnf()) {
        differential_oracle_matrix(&case);
    }

    /// GateChain family: gate-structured formulas that exercise BVE, decompose,
    /// congruence, and sweep interactions.
    #[test]
    fn prop_gate_chain_inproc_soundness(case in arb_gate_chain_cnf()) {
        differential_oracle_matrix(&case);
    }
}

// =============================================================================
// Heavier soak tests (run with larger case counts)
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Extended soak test: 256 cases across all families.
    /// Run with: PROPTEST_CASES=512 cargo test -p ay-sat --test cnf_fuzz_proptest -- prop_soak
    #[test]
    fn prop_soak_all_families(case in arb_cnf_case()) {
        differential_oracle_matrix(&case);
    }
}
