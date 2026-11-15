// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Chainable-`=` surfaces under the premise-free `equiv_*`/`xor_*`/`implies_*`
//! family. Each fixture is the CLI's own shape: the term store holds a BINARY
//! connective, the authored-surface override prints it with more operands, and
//! AY's strict checker (which reads the store) accepts the step. Positive cases
//! must replay `valid` in pinned carcara; negative twins must refuse the export
//! rather than name a rule the printed text does not instantiate.

use crate::{try_export_alethe_with_problem_scope_and_overrides, AlethePrintError};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermId, TermStore};
use std::process::Command;

struct Atoms {
    p: TermId,
    q: TermId,
    not_p: TermId,
    not_q: TermId,
}

fn atoms(terms: &mut TermStore) -> Atoms {
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let not_q = terms.mk_not_raw(q);
    Atoms { p, q, not_p, not_q }
}

fn binary(terms: &mut TermStore, op: &str, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named(op), [left, right], Sort::Bool)
}

/// Refute `premises` from the premise-free `rule` step over `clause`: every
/// clause literal but `clause[0]` is resolved against an asserted unit, then
/// `clause[0]` against the assumed source unit `source_unit`.
fn refutation(rule: AletheRule, clause: &[TermId], source_unit: TermId, units: &[TermId]) -> Proof {
    let mut proof = Proof::new();
    let source = proof.add_assume(source_unit, None);
    let unit_ids: Vec<ProofId> = units.iter().map(|&u| proof.add_assume(u, None)).collect();
    let mut current = proof.add_rule_step(rule, clause.to_vec(), Vec::new(), Vec::new());
    let mut remaining = clause.to_vec();
    for (&literal, &unit) in clause[1..].iter().zip(&unit_ids) {
        remaining.retain(|&lit| lit != literal);
        current = proof.add_resolution(remaining.clone(), literal, current, unit);
    }
    proof.add_resolution(Vec::new(), clause[0], current, source);
    proof
}

fn export(
    proof: &Proof,
    terms: &TermStore,
    scope: &[TermId],
    overrides: &[(TermId, &str)],
) -> Result<String, AlethePrintError> {
    let overrides: DetHashMap<TermId, String> = overrides
        .iter()
        .map(|&(term, text)| (term, text.to_string()))
        .collect();
    try_export_alethe_with_problem_scope_and_overrides(proof, terms, scope, Some(&overrides))
}

/// Pinned carcara's verdict, or `None` when it is not on PATH (the replay is
/// then skipped, never passed). `case` must be unique per call site: it keys
/// the scratch directory, and the harness runs these tests in parallel.
fn carcara_verdict(case: &str, problem: &str, proof: &str) -> Option<String> {
    if let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof) {
        panic!("{case}: {misjudged}\n{proof}");
    }
    let probe = Command::new("carcara").arg("--version").output();
    if !probe.is_ok_and(|probe| probe.status.success()) {
        eprintln!("carcara not on PATH: the {case} replay is skipped");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("ay-chain-equiv-{}-{case}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("p.smt2"), problem).unwrap();
    std::fs::write(dir.join("p.alethe"), proof).unwrap();
    let output = Command::new("carcara")
        .args(["check", "--expand-let-bindings", "--"])
        .arg(dir.join("p.alethe"))
        .arg(dir.join("p.smt2"))
        .output()
        .unwrap();
    // All of stdout on one line: only a lone `valid` from a successful run is
    // verification.
    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut verdict = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    if !output.status.success() {
        verdict = format!("exit {}: {verdict}", output.status);
    }
    let stderr = String::from_utf8_lossy(&output.stderr);
    if verdict == "valid" {
        let _ = std::fs::remove_dir_all(&dir);
    }
    Some(format!("{verdict}\n{stderr}\nkept: {}", dir.display()))
}

/// NEGATIVE CONTROL: the replay refuses, before the checker runs (so with or
/// without carcara on PATH), the pair pinned carcara prints `valid` for only
/// through its `evaluate` defect (`ay_core::pinned_carcara`).
#[test]
#[should_panic(expected = "is not evidence")]
fn the_carcara_replay_refuses_a_document_pinned_carcara_misjudges() {
    carcara_verdict(
        "false_valid_control",
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM,
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF,
    );
}

fn assert_carcara_valid(case: &str, asserts: &[&str], proof: &str) {
    let mut problem =
        String::from("(set-logic QF_UF)\n(declare-fun p () Bool)\n(declare-fun q () Bool)\n");
    for assertion in asserts {
        problem.push_str(&format!("(assert {assertion})\n"));
    }
    problem.push_str("(check-sat)\n");
    if let Some(verdict) = carcara_verdict(case, &problem, proof) {
        assert_eq!(
            verdict.lines().next().unwrap_or(""),
            "valid",
            "{case}: {verdict}\n{proof}"
        );
    }
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{proof}"
    );
}

fn assert_refused(result: Result<String, AlethePrintError>, rule: &str) {
    match result {
        Err(AlethePrintError::InvalidSurfaceStep { reason, .. }) => {
            assert!(reason.contains(rule), "{reason}");
        }
        other => panic!("expected the {rule} export to be refused, got {other:?}"),
    }
}

/// The published defect: `(assert (= p q q))` stores the binary `(= p q)` and
/// prints it as the authored chain. The step used to ship as a bare
/// `equiv_pos2` over `(= p q q)`, which carcara refuses as "of the wrong form".
#[test]
fn chainable_equality_equiv_pos2_is_derived_through_nary_elim() {
    for (index, surface) in ["(= p q q)", "(= p q q q)", "(= p q p q)", "(= p p q)"]
        .into_iter()
        .enumerate()
    {
        let mut terms = TermStore::new();
        let a = atoms(&mut terms);
        let equality = binary(&mut terms, "=", a.p, a.q);
        let not_equality = terms.mk_not_raw(equality);
        let clause = [not_equality, a.not_p, a.q];
        let proof = refutation(AletheRule::EquivPos2, &clause, equality, &[a.p, a.not_q]);
        let output = export(
            &proof,
            &terms,
            &[equality, a.p, a.not_q],
            &[(equality, surface)],
        )
        .expect("a chain that entails the printed clause must export");
        assert!(output.contains(":rule nary_elim)"), "{output}");
        assert!(
            !output.contains(&format!("(cl (not {surface}) (not p) q) :rule equiv_pos2")),
            "the n-ary source must not be named as an equiv_pos2 instance:\n{output}"
        );
        assert_carcara_valid(
            &format!("pos2_{index}"),
            &[surface, "p", "(not q)"],
            &output,
        );
    }
}

/// `equiv_pos1` over the store `(= p q)` reads `(cl (not S) p (not q))`; with
/// the chain spelled `(= q p q)` only a REVERSED link carries it, so the bridge
/// must pick the other binary rule over that link.
#[test]
fn chainable_equality_equiv_pos1_uses_a_reversed_link() {
    let mut terms = TermStore::new();
    let a = atoms(&mut terms);
    let equality = binary(&mut terms, "=", a.p, a.q);
    let not_equality = terms.mk_not_raw(equality);
    let clause = [not_equality, a.p, a.not_q];
    let proof = refutation(AletheRule::EquivPos1, &clause, equality, &[a.not_p, a.q]);
    let output = export(
        &proof,
        &terms,
        &[equality, a.not_p, a.q],
        &[(equality, "(= q p q)")],
    )
    .expect("the reversed link entails the printed clause");
    assert!(output.contains(":rule nary_elim)"), "{output}");
    assert_carcara_valid("pos1_reversed", &["(= q p q)", "(not p)", "q"], &output);
}

/// The positive-source direction needs EVERY link: a reflexive one follows by
/// `eq_reflexive` and every other by the binary `equiv_neg*` instance, here
/// including DUPLICATE non-reflexive links (`(= p q p q)` repeats `(= p q)`).
#[test]
fn chainable_equality_equiv_neg_recombines_every_link() {
    for (index, (rule, surface, units)) in [
        (AletheRule::EquivNeg1, "(= p q q)", ["p", "q"]),
        (AletheRule::EquivNeg2, "(= p q p)", ["(not p)", "(not q)"]),
        (AletheRule::EquivNeg1, "(= p q p q)", ["p", "q"]),
    ]
    .into_iter()
    .enumerate()
    {
        let mut terms = TermStore::new();
        let a = atoms(&mut terms);
        let equality = binary(&mut terms, "=", a.p, a.q);
        let not_equality = terms.mk_not_raw(equality);
        let (clause, unit_terms) = match rule {
            AletheRule::EquivNeg1 => ([equality, a.not_p, a.not_q], [a.p, a.q]),
            _ => ([equality, a.p, a.q], [a.not_p, a.not_q]),
        };
        let proof = refutation(rule.clone(), &clause, not_equality, &unit_terms);
        let mut scope = vec![not_equality];
        scope.extend(unit_terms);
        let output = export(&proof, &terms, &scope, &[(equality, surface)])
            .expect("a chain over exactly the two literals is entailed by them");
        assert!(output.contains(":rule and_neg)"), "{output}");
        let negated = format!("(not {surface})");
        assert_carcara_valid(
            &format!("recombine_{index}"),
            &[&negated, units[0], units[1]],
            &output,
        );
    }
}

/// A chain over a NEGATED operand: the binary instance states
/// `(not (not p))` where the traced clause holds the stripped `p`, so the link
/// step carries a `not_not` bridge. Measured on the CLI: `(= (not p) q q)`
/// with `(not p)` and `(not q)` shipped a bare `equiv_pos2` over the chain.
#[test]
fn chainable_equality_over_a_negated_operand_bridges_the_stripped_literal() {
    for rule in [AletheRule::EquivPos2, AletheRule::EquivNeg1] {
        let mut terms = TermStore::new();
        let a = atoms(&mut terms);
        let equality = binary(&mut terms, "=", a.not_p, a.q);
        let not_equality = terms.mk_not_raw(equality);
        let (clause, source, units, asserts) = match rule {
            AletheRule::EquivPos2 => (
                [not_equality, a.p, a.q],
                equality,
                [a.not_p, a.not_q],
                ["(= (not p) q q)", "(not p)", "(not q)"],
            ),
            _ => (
                [equality, a.p, a.not_q],
                not_equality,
                [a.not_p, a.q],
                ["(not (= (not p) q q))", "(not p)", "q"],
            ),
        };
        let proof = refutation(rule.clone(), &clause, source, &units);
        let scope = [source, units[0], units[1]];
        let output = export(&proof, &terms, &scope, &[(equality, "(= (not p) q q)")])
            .expect("the link instance plus a not_not bridge entails the printed clause");
        assert!(output.contains(":rule not_not)"), "{output}");
        assert_carcara_valid(&format!("negated_operand_{rule}"), &asserts, &output);
    }
}

/// NEGATIVE TWIN of the neg-direction bridge, and the arity guard's sharpest
/// case. `(cl (= p q r) p q)` is FALSE over the printed text (`r` true, `p`
/// and `q` false), yet the unguarded `equiv_neg2` template read operands 0 and
/// 1 of the chain, reproduced the clause, and let the default rendering ship
/// it as `DefaultIsExact`. The link `(= q r)` does not follow from `(not p)`
/// and `(not q)`, so no derivation exists and the export must be refused.
#[test]
fn chainable_equality_equiv_neg_over_an_unentailed_chain_is_refused() {
    let mut terms = TermStore::new();
    let a = atoms(&mut terms);
    let equality = binary(&mut terms, "=", a.p, a.q);
    let not_equality = terms.mk_not_raw(equality);
    let clause = [equality, a.p, a.q];
    let proof = refutation(
        AletheRule::EquivNeg2,
        &clause,
        not_equality,
        &[a.not_p, a.not_q],
    );
    let scope = [not_equality, a.not_p, a.not_q];
    assert_refused(
        export(&proof, &terms, &scope, &[(equality, "(= p q r)")]),
        "equiv_neg2",
    );
    // Unmutated twin: the binary spelling still renders the plain rule.
    let output = export(&proof, &terms, &scope, &[])
        .expect("a spec-shaped binary equiv_neg2 must still export");
    assert!(
        output.contains("(cl (= p q) p q) :rule equiv_neg2)"),
        "{output}"
    );
}

/// NEGATIVE TWIN of the positive-direction bridge: no link of `(= p r q)`
/// relates `p` and `q` directly, and a transitive step is not what the step
/// claims, so the bridge declines and the export is refused.
#[test]
fn chainable_equality_equiv_pos_without_a_matching_link_is_refused() {
    let mut terms = TermStore::new();
    let a = atoms(&mut terms);
    let equality = binary(&mut terms, "=", a.p, a.q);
    let not_equality = terms.mk_not_raw(equality);
    let clause = [not_equality, a.not_p, a.q];
    let proof = refutation(AletheRule::EquivPos2, &clause, equality, &[a.p, a.not_q]);
    let scope = [equality, a.p, a.not_q];
    assert_refused(
        export(&proof, &terms, &scope, &[(equality, "(= p r q)")]),
        "equiv_pos2",
    );
}

/// The same arity defect in the other fixed-shape families: the left-assoc
/// `(xor p q q)` and the right-assoc `(=> p q q)` are not `xor_pos1` and
/// `implies_pos` instances, although each template over the first two
/// operands reproduces the printed clause. No bridge spells them, so the
/// export is refused; the binary spelling still renders the plain rule.
#[test]
fn n_ary_xor_and_implies_surfaces_are_not_binary_template_instances() {
    for (op, rule, name, surface) in [
        ("xor", AletheRule::XorPos1, "xor_pos1", "(xor p q q)"),
        ("=>", AletheRule::ImpliesPos, "implies_pos", "(=> p q q)"),
    ] {
        let mut terms = TermStore::new();
        let a = atoms(&mut terms);
        let gate = binary(&mut terms, op, a.p, a.q);
        let not_gate = terms.mk_not_raw(gate);
        let (clause, units) = match rule {
            AletheRule::XorPos1 => ([not_gate, a.p, a.q], [a.not_p, a.not_q]),
            _ => ([not_gate, a.not_p, a.q], [a.p, a.not_q]),
        };
        let proof = refutation(rule, &clause, gate, &units);
        let scope = [gate, units[0], units[1]];
        assert_refused(export(&proof, &terms, &scope, &[(gate, surface)]), name);
        let output = export(&proof, &terms, &scope, &[])
            .unwrap_or_else(|error| panic!("binary {name} must still export: {error:?}"));
        assert!(output.contains(&format!(":rule {name})")), "{output}");
    }
}
