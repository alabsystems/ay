// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof recording (design D3): every `unsat` answer of the kernel comes with
//! one refutation of the asserted formulas, assembled from what the search
//! recorded, and AY's strict checker accepts it with no hole.
//!
//! The checker is independent of the kernel: it validates each clausification
//! step against its rule, each theory step against its kind (Farkas sums for
//! `LraFarkas`, trichotomy for `ArithDisequalitySplit`), each resolution
//! against its premises, and each `assume` against the problem's assertions.

use ay_cdclt::{CheckOutcome, Engine, EngineConfig, Guard, KernelProof, Verdict};
use ay_core::{ProofStep, Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

fn q(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

/// Check `assertions` with recording on; on `unsat`, the assembled proof.
fn refute(terms: &mut TermStore, assertions: &[TermId]) -> (CheckOutcome, Option<KernelProof>) {
    let mut engine = Engine::new(EngineConfig {
        record_proofs: true,
        ..EngineConfig::default()
    });
    for &a in assertions {
        engine.assert(a);
    }
    let outcome = engine.check(terms, &[], &Guard::new());
    let proof = (outcome.verdict == Verdict::Unsat).then(|| {
        outcome
            .proof
            .as_ref()
            .ok_or(ay_cdclt::ProofFailure::NotRecorded)
            .and_then(|recorded| recorded.assemble(terms, None))
            .unwrap_or_else(|failure| panic!("no recorded refutation: {failure}"))
    });
    (outcome, proof)
}

/// The pinned external checker, when this machine has one (`CARCARA_PATH`,
/// else `~/.cargo/bin/carcara`).
fn carcara() -> Option<std::path::PathBuf> {
    if let Some(path) = std::env::var_os("CARCARA_PATH") {
        return Some(path.into());
    }
    let path = std::path::PathBuf::from(std::env::var_os("HOME")?).join(".cargo/bin/carcara");
    path.is_file().then_some(path)
}

/// carcara's verdict on the printed proof against a problem file stating
/// exactly `assertions` over the Real variables `vars`.
fn carcara_verdict(
    checker: &std::path::Path,
    terms: &TermStore,
    vars: &[&str],
    assertions: &[TermId],
    proof: &KernelProof,
    tag: &str,
) -> String {
    let mut problem = String::from("(set-logic QF_LRA)\n");
    for v in vars {
        problem.push_str(&format!("(declare-fun {v} () Real)\n"));
    }
    for &a in assertions {
        problem.push_str(&format!(
            "(assert {})\n",
            ay_proof::format_term_alethe(terms, a)
        ));
    }
    problem.push_str("(check-sat)\n");
    let dir = std::env::temp_dir().join(format!("ay-cdclt-proof-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let problem_path = dir.join(format!("{tag}.smt2"));
    let proof_path = dir.join(format!("{tag}.alethe"));
    std::fs::write(&problem_path, problem).expect("write problem");
    // Proof commands only: carcara's proof grammar has no declaration
    // command, and the problem file declares the variables.
    let document = ay_proof::export_alethe_with_problem_scope(&proof.proof, terms, assertions);
    std::fs::write(&proof_path, document).expect("write proof");
    let out = std::process::Command::new(checker)
        .arg("check")
        .arg("--allow-int-real-subtyping")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run carcara");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let verdict = stdout
        .lines()
        .map(str::trim)
        .find(|l| matches!(*l, "valid" | "holey" | "invalid"))
        .unwrap_or("error")
        .to_string();
    if verdict == "valid" {
        let _ = std::fs::remove_file(&problem_path);
        let _ = std::fs::remove_file(&proof_path);
    } else {
        eprintln!(
            "carcara {verdict} on {}: {}",
            proof_path.display(),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    verdict
}

fn strict_check(terms: &TermStore, assertions: &[TermId], proof: &KernelProof) {
    if let Err(error) =
        ay_proof::check_proof_strict_with_context(&proof.proof, terms, None, None, Some(assertions))
    {
        panic!(
            "strict check rejected the kernel's proof: {error:?}\n{}",
            ay_proof::export_alethe(&proof.proof, terms)
        );
    }
}

/// `x ≥ 0, y ≥ 0, x ≤ 1, y ≤ 1, x + y ≥ 3`: one Farkas conflict.
#[test]
fn a_farkas_conflict_is_a_checked_refutation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(q(0));
    let one = terms.mk_rational(q(1));
    let three = terms.mk_rational(q(3));
    let sum = terms.mk_add(vec![x, y]);
    let assertions = vec![
        terms.mk_ge(x, zero),
        terms.mk_ge(y, zero),
        terms.mk_le(x, one),
        terms.mk_le(y, one),
        terms.mk_ge(sum, three),
    ];
    let (outcome, proof) = refute(&mut terms, &assertions);
    assert_eq!(outcome.verdict, Verdict::Unsat);
    let proof = proof.expect("proof");
    assert_eq!(proof.stats.holes, 0, "{:?}", proof.stats);
    assert!(
        proof.stats.theory_kinds.contains_key("LraFarkas"),
        "{:?}",
        proof.stats
    );
    assert!(
        matches!(proof.proof.steps.last(), Some(ProofStep::Step { clause, .. }) if clause.is_empty())
    );
    strict_check(&terms, &assertions, &proof);
}

/// `x - y ≤ 0 ∧ y - x ≤ 0 ∧ x ≠ y`: the disequality split is decided in the
/// search, and its trichotomy lemma is a checked step of the refutation.
#[test]
fn a_split_inside_the_search_is_a_checked_step() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(q(0));
    let xy = terms.mk_sub(vec![x, y]);
    let yx = terms.mk_sub(vec![y, x]);
    let eq = terms.mk_eq(x, y);
    let assertions = vec![
        terms.mk_le(xy, zero),
        terms.mk_le(yx, zero),
        terms.mk_not(eq),
    ];
    let (outcome, proof) = refute(&mut terms, &assertions);
    assert_eq!(outcome.verdict, Verdict::Unsat);
    let proof = proof.expect("proof");
    assert_eq!(proof.stats.holes, 0, "{:?}", proof.stats);
    strict_check(&terms, &assertions, &proof);
}

/// Boolean structure over theory atoms: the clausification steps (`and_pos`,
/// `or_pos`, `ite_*`, `equiv_*`) join the theory steps in one refutation.
#[test]
fn clausification_and_theory_steps_join_in_one_refutation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let p = terms.mk_var("p", Sort::Bool);
    let zero = terms.mk_rational(q(0));
    let two = terms.mk_rational(q(2));
    let x_pos = terms.mk_gt(x, zero);
    let y_pos = terms.mk_gt(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let small = terms.mk_le(sum, zero);
    let big = terms.mk_ge(x, two);
    let either = terms.mk_or(vec![x_pos, big]);
    let both = terms.mk_and(vec![either, y_pos]);
    let choice = terms.mk_ite(p, both, x_pos);
    let q_eq = terms.mk_eq(p, small);
    let not_p = terms.mk_not(p);
    let y_nonneg = terms.mk_ge(y, zero);
    let assertions = vec![choice, q_eq, terms.mk_or(vec![p, not_p]), y_nonneg, small];
    let (outcome, proof) = refute(&mut terms, &assertions);
    assert_eq!(outcome.verdict, Verdict::Unsat);
    let proof = proof.expect("proof");
    assert_eq!(proof.stats.holes, 0, "{:?}", proof.stats);
    assert!(proof.stats.clausification > 0, "{:?}", proof.stats);
    strict_check(&terms, &assertions, &proof);
}

/// The check has teeth: corrupting one Farkas coefficient, or one theory
/// step's clause, makes the strict checker reject the proof.
#[test]
fn a_corrupted_step_is_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(q(0));
    let one = terms.mk_rational(q(1));
    let three = terms.mk_rational(q(3));
    let sum = terms.mk_add(vec![x, y]);
    let assertions = vec![
        terms.mk_ge(x, zero),
        terms.mk_ge(y, zero),
        terms.mk_le(x, one),
        terms.mk_le(y, one),
        terms.mk_ge(sum, three),
    ];
    let (_, proof) = refute(&mut terms, &assertions);
    let proof = proof.expect("proof");
    let farkas_step = proof
        .proof
        .steps
        .iter()
        .position(|s| {
            matches!(
                s,
                ProofStep::TheoryLemma {
                    farkas: Some(_),
                    ..
                }
            )
        })
        .expect("a Farkas step");

    let mut scaled = proof.proof.clone();
    if let ProofStep::TheoryLemma {
        farkas: Some(f), ..
    } = &mut scaled.steps[farkas_step]
    {
        f.coefficients[0] *= num_rational::Rational64::from(2);
        f.coefficients[1] *= num_rational::Rational64::from(0);
    }
    assert!(
        ay_proof::check_proof_strict_with_context(&scaled, &terms, None, None, Some(&assertions))
            .is_err(),
        "a wrong certificate must be rejected"
    );

    let mut weakened = proof.proof.clone();
    if let ProofStep::TheoryLemma { clause, .. } = &mut weakened.steps[farkas_step] {
        let _ = clause.remove(0);
    }
    assert!(
        ay_proof::check_proof_strict_with_context(&weakened, &terms, None, None, Some(&assertions))
            .is_err(),
        "a theory step that no longer holds must be rejected"
    );
}

// ---- random difference-logic combinations (the kernel's oracle test shape) --

#[derive(Clone, Copy, Debug)]
enum Atom {
    Le(usize, usize, i64),
    Eq(usize, usize, i64),
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Every `unsat` answer over 1,000 random Boolean combinations of `x - y ≤ c`
/// and `x - y = c` (with disequalities, so splits, model equalities and
/// Farkas conflicts all occur) has a strict-checked proof with no hole.
/// A random difference-logic instance: the variable count, six atoms
/// `x_u - x_v <= c` or `= c`, and three to eight clauses over them.
fn random_difference_instance(rng: &mut Rng) -> (usize, Vec<Atom>, Vec<Vec<(usize, bool)>>) {
    let n = 3 + usize::try_from(rng.below(2)).unwrap_or(0);
    let mut atoms = Vec::new();
    while atoms.len() < 6 {
        let (u, v) = (
            usize::try_from(rng.below(n as u64)).unwrap_or(0),
            usize::try_from(rng.below(n as u64)).unwrap_or(0),
        );
        if u == v {
            continue;
        }
        let c = i64::try_from(rng.below(5)).unwrap_or(0) - 2;
        atoms.push(if rng.below(3) == 0 {
            Atom::Eq(u, v, c)
        } else {
            Atom::Le(u, v, c)
        });
    }
    let clauses: Vec<Vec<(usize, bool)>> = (0..3 + rng.below(6))
        .map(|_| {
            (0..=rng.below(3))
                .map(|_| {
                    (
                        usize::try_from(rng.below(6)).unwrap_or(0),
                        rng.below(2) == 0,
                    )
                })
                .collect()
        })
        .collect();
    (n, atoms, clauses)
}

#[test]
fn every_random_refutation_checks() {
    let mut rng = Rng(0xD1B5_4A32_D192_ED03);
    let checker = carcara();
    let (mut unsat, mut steps, mut resolutions, mut carcara_valid) = (0u64, 0u64, 0u64, 0u64);
    for round in 0..1000 {
        let (n, atoms, clauses) = random_difference_instance(&mut rng);
        let mut terms = TermStore::new();
        let xs: Vec<TermId> = (0..n)
            .map(|i| terms.mk_var(format!("x{i}"), Sort::Real))
            .collect();
        let atom_terms: Vec<TermId> = atoms
            .iter()
            .map(|&a| {
                let (Atom::Le(u, v, c) | Atom::Eq(u, v, c)) = a;
                let diff = terms.mk_sub(vec![xs[u], xs[v]]);
                let k = terms.mk_rational(q(c));
                match a {
                    Atom::Le(..) => terms.mk_le(diff, k),
                    Atom::Eq(..) => terms.mk_eq(diff, k),
                }
            })
            .collect();
        let assertions: Vec<TermId> = clauses
            .iter()
            .map(|c| {
                let lits = c
                    .iter()
                    .map(|&(a, pos)| {
                        if pos {
                            atom_terms[a]
                        } else {
                            terms.mk_not(atom_terms[a])
                        }
                    })
                    .collect();
                terms.mk_or(lits)
            })
            .collect();
        let (outcome, proof) = refute(&mut terms, &assertions);
        if let Some(proof) = proof {
            assert_eq!(
                proof.stats.holes,
                0,
                "round {round}: {:?}\n{}",
                proof.stats,
                ay_proof::export_alethe(&proof.proof, &terms)
            );
            strict_check(&terms, &assertions, &proof);
            if let Some(checker) = &checker {
                let names: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
                let names: Vec<&str> = names.iter().map(String::as_str).collect();
                let verdict = carcara_verdict(
                    checker,
                    &terms,
                    &names,
                    &assertions,
                    &proof,
                    &format!("round{round}"),
                );
                assert_eq!(verdict, "valid", "round {round}: carcara");
                carcara_valid += 1;
            }
            unsat += 1;
            steps += proof.stats.steps;
            resolutions += proof.stats.resolutions;
        } else {
            assert_eq!(outcome.verdict, Verdict::Sat, "round {round}");
        }
    }
    eprintln!(
        "proofs: {unsat} refutations, {steps} steps, {resolutions} resolution steps, \
         {carcara_valid} carcara-valid (checker {})",
        checker
            .as_ref()
            .map_or("absent".to_string(), |c| c.display().to_string())
    );
    assert!(unsat > 150, "a useful number of refutations: {unsat}");
}
