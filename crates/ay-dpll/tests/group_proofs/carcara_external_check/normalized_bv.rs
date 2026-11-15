// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// The NORMALIZED-ASSUME MISMATCH class (SMT-COMP QF_LIA CAV_2009 family):
/// the file spells linear atoms with explicit coefficients — `(* 1 x)`,
/// `(* 0 x)`, `(* (- 1) x)`, duplicated monomials — that arithmetic
/// elaboration canonicalizes (unit/zero elision, unary minus, folding,
/// reordering), so a canonical-print `assume` matches no problem premise.
/// The repair raw-interns the surface spelling for the assume and bridges
/// each extracted conjunct to its canonical atom with a certified `[1, 1]`
/// `la_generic` orientation lemma (#real-bench).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_external_normalized_linear_assume_bridge() {
    let problem = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (and (<= (+ (* 1 x0) (* 1 x0) (* 0 x1) (* (- 1) x1)) 0) (<= (+ (* 1 x1) (* (- 2) x0)) (- 1)) (<= (+ (* 0 x0) (* 1 x2)) 5)))
(check-sat)
"#;

    let proof = solve_unsat_and_get_proof(problem, "normalized_linear_assume");
    assert!(
        !proof.contains(":rule trust"),
        "normalized-assume proof must be trust-free:\n{proof}"
    );
    assert!(
        proof.contains(":rule la_generic"),
        "expected certified la_generic bridge lemmas:\n{proof}"
    );
    // Every assume must spell an asserted problem premise EXACTLY (the raw
    // surface print, not the canonicalized atom forms).
    let asserted = extract_asserted_terms(problem);
    for assume in extract_assume_terms(&proof) {
        assert!(
            asserted.contains(&assume),
            "assume is not a problem premise: {assume}"
        );
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    verify_alethe_with_carcara(
        &carcara,
        "normalized_linear_assume",
        problem,
        proof.as_str(),
    );
}

/// The deduplicated-conjunct variant of the normalized-assume mismatch
/// (CAV_2009 problem__030): two surface conjuncts elaborate to the SAME
/// canonical atom, so the canonical conjunction has fewer conjuncts than the
/// file — positional pairing is impossible and the alignment-capable
/// `AndDistinct` classifier must carry the repair, dropping the exporter's
/// de-Morganized `and_pos` steps in favor of re-derived per-conjunct units
/// (#real-bench).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_external_normalized_assume_deduplicated_conjunct() {
    let problem = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (and (<= (+ (* 1 x0) (* (- 1) x1)) 0) (<= (+ (* 0 x2) (* 1 x0) (* (- 1) x1)) 0) (<= (+ (* 1 x1) (* (- 1) x0)) (- 1))))
(check-sat)
"#;

    let proof = solve_unsat_and_get_proof(problem, "normalized_assume_dedup");
    assert!(
        !proof.contains(":rule trust"),
        "deduplicated normalized-assume proof must be trust-free:\n{proof}"
    );
    let asserted = extract_asserted_terms(problem);
    for assume in extract_assume_terms(&proof) {
        assert!(
            asserted.contains(&assume),
            "assume is not a problem premise: {assume}"
        );
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    verify_alethe_with_carcara(&carcara, "normalized_assume_dedup", problem, proof.as_str());
}

// ============================================================================
// Ground bitvector disequality: `hole` -> checked `evaluate` derivation
// ============================================================================

/// Real benchmark rows whose ONLY unchecked step was the ground bitvector
/// disequality `(cl (not (= #b… #b…)))`.
///
/// AY closes every "two constants forced equal" refutation by chaining the
/// problem's own equalities with `eq_transitive` down to `(cl (= C1 C2))` and
/// resolving against its negation. The negation is a closed fact, but no
/// carcara rule CONCLUDES `(cl (not (= t u)))` — `evaluate` proves only a
/// POSITIVE unit `(= term value)` — so it used to print as `hole` and made
/// otherwise-complete documents `holey`. It is now spelled out as
/// `evaluate` + `equiv1` + `false` + `resolution`, all of which this carcara
/// build implements, and these documents check as `valid`.
const GROUND_BV_DISEQUALITY_BENCHMARKS: &[&str] = &[
    "benchmarks/smt/QF_ABV/csplit_repro_unsat.smt2",
    "benchmarks/smt/QF_ABV/csplit_repro_store_chain_unsat.smt2",
    "benchmarks/smt/QF_BV/puzzle_03.smt2",
    "benchmarks/smt/QF_BV/puzzle_12.smt2",
];

#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(240_000))]
fn test_carcara_ground_bv_disequality_is_checked_not_holey() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    for relative_path in GROUND_BV_DISEQUALITY_BENCHMARKS {
        let label = relative_path
            .rsplit('/')
            .next()
            .expect("benchmark file name");
        let problem: String = benchmark_content(relative_path)
            .lines()
            .filter(|line| line.trim() != "(exit)")
            .collect::<Vec<_>>()
            .join("\n");
        let proof = solve_unsat_and_get_proof(&problem, label);
        assert!(
            !proof.contains(":rule hole"),
            "{label}: the ground bitvector disequality must not print as a hole:\n{proof}"
        );
        assert!(
            proof.contains(":rule evaluate"),
            "{label}: expected the `evaluate` lowering in the proof:\n{proof}"
        );
        assert!(
            run_carcara_trust_free(&carcara, label, &problem, &proof),
            "{label}: proof must be externally VALID, not merely holey"
        );
    }
}

/// The lowering is shape-gated, not blanket: an `evaluate` step may only ever
/// carry a closed constant equality, never a non-ground clause.
///
/// CONTRACT CORRECTED 2026-09-23 (the name is kept so name-keyed ledgers keep
/// the oracle). It also said this document "must keep its honest `hole` and
/// report `holey` — never `invalid`", checked through a runner that passed
/// `--allowed-rules trust` and read only the exit status, which is 0 for
/// `holey` AND `valid`. Read exactly, with no allowance, on ay `8d9e105fa`/`69efb137d` and
/// carcara 1.1.0 [git 9a352ee], the document is `valid`: it carries no hole.
/// The test now requires that strictly stronger verdict; falling back to a
/// hole, or to any rule Carcara cannot re-derive, fails it.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_symbolic_bv_conflict_keeps_its_honest_hole() {
    let problem = r#"
(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 8))
(declare-fun v1 () (_ BitVec 8))
(assert (= (bvand v0 v1) #x0f))
(assert (= (bvor v0 v1) #x00))
(check-sat)
"#;
    let proof = solve_unsat_and_get_proof(problem, "symbolic_bv_conflict");
    for line in proof.lines() {
        assert!(
            !line.contains(":rule evaluate") || line.contains("(cl (= (= #"),
            "an `evaluate` step was emitted for a non-ground clause: {line}"
        );
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert!(
        run_carcara_trust_free(&carcara, "symbolic_bv_conflict", problem, &proof),
        "the symbolic BV conflict must be Carcara `valid` with no allowance:\n{proof}"
    );
}

/// An authored bit-vector literal spelling inside a certified congruence
/// PREMISE. The authored-assume override keeps `(= p0 #x10)` and
/// `(= mem2 (store mem p0 #xAA))` verbatim, while the congruences that consume
/// them print the canonical `#b00010000` / `#b10101010` renderings of the same
/// constants. carcara parses both spellings to one term, so the printer must
/// bridge each premise leg with `refl` + `trans` instead of refusing the whole
/// document as `UNVERIFIABLE PROOF` — the shape that cost QF_ABV
/// `csplit_repro_many_trivial_selects_unsat` its certificate once 779076535
/// retained the native resolution.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_trust_free_authored_bv_literal_congruence_premise() {
    let problem = r#"
(set-logic QF_ABV)
(declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const p0 (_ BitVec 8))
(declare-const p1 (_ BitVec 8))
(declare-const mem2 (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= p0 #x10))
(assert (= p1 #x10))
(assert (= mem2 (store mem p0 #xAA)))
(assert (= (select mem2 p1) #xBB))
(check-sat)
"#;
    let label = "authored_bv_literal_congruence_premise";
    let proof = solve_unsat_and_get_proof(problem, label);
    assert!(
        proof
            .lines()
            .any(|line| line.contains(".r (cl (= #x10 #b00010000)) :rule refl)")),
        "{label}: expected the authored-literal PREMISE leg (`<id>.r`) to be bridged by refl:\n{proof}"
    );
    // The bridge adds no hypothesis: every assume is still an authored premise.
    let asserted = extract_asserted_terms(problem);
    for assume in extract_assume_terms(&proof) {
        assert!(
            asserted.contains(&assume),
            "{label}: assume is not a problem premise: {assume}"
        );
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert!(
        run_carcara_trust_free(&carcara, label, problem, &proof),
        "{label}: proof must be externally VALID, not merely holey"
    );
}

/// [`test_carcara_trust_free_authored_bv_literal_congruence_premise`]'s ROW1
/// problem with the two uses of the index authored as caller-chosen spellings
/// of `#x10`.
fn row1_authored_index_problem(p0_index: &str, p1_index: &str) -> String {
    format!(
        "(set-logic QF_ABV)\n\
         (declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))\n\
         (declare-const p0 (_ BitVec 8))\n\
         (declare-const p1 (_ BitVec 8))\n\
         (declare-const mem2 (Array (_ BitVec 8) (_ BitVec 8)))\n\
         (assert (= p0 {p0_index}))\n\
         (assert (= p1 {p1_index}))\n\
         (assert (= mem2 (store mem p0 #xAA)))\n\
         (assert (= (select mem2 p1) #xBB))\n\
         (check-sat)\n"
    )
}

/// The same problem with the index authored as one CONSTANT-FOLDED term,
/// `(bvadd #x08 #x08)`, at both uses. Elaboration folds it to `#b00010000`,
/// and the native refutation lifts the derived `(= p0 p1)` onto the store
/// through a `cong` whose premise prints from the authored
/// `(= p0 (bvadd #x08 #x08))` against that constant. No literal `refl` bridge
/// relates the two, so the printer refuses it (`InvalidCongruenceStep`).
///
/// The raw-root ground closure, the last wire-gap retry for a native-strict
/// proof (`repair_wire_gap_with_authored_root_refutation`), refutes the
/// AUTHORED roots instead: `p0` and `p1` equal one authored term, so
/// transitivity relates them without evaluating it, and the read
/// over the write closes by `arrays_idx`. This was the accepted-cell fixture
/// of `api::tests::test_proof_artifact::a_rescued_authored_spelling_refusal_publishes_an_accepted_verdict`
/// until that retry made it print directly. Counterfactual, measured with
/// the retry disabled: `(get-proof)` answers `UNVERIFIABLE PROOF`.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_trust_free_authored_folded_bv_index_shared_term() {
    let problem = row1_authored_index_problem("(bvadd #x08 #x08)", "(bvadd #x08 #x08)");
    let label = "authored_folded_bv_index_shared_term";
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let mut outputs = Vec::new();
    for command in parse(&format!("{problem}(get-proof)\n")).unwrap() {
        if let Some(output) = exec.execute_authored(&command).unwrap() {
            outputs.push(output);
        }
    }
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
    let native = exec.last_proof().expect("public source proof retained");
    assert!(ay_proof::check_proof_strict(native, exec.terms())
        .expect("complete native derivation")
        .is_complete());
    let proof = outputs.last().expect("public get-proof document");
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{label}: the authored-root refutation must be trust-free:\n{proof}"
    );
    // Source fidelity and complete replay are the contract. Either equality
    // orientation (or another checked derivation) may transport the read.
    let asserted: BTreeSet<_> = extract_asserted_terms(&problem)
        .iter()
        .map(|term| ay_dpll::normalize_premise_surface(term))
        .collect();
    for assume in extract_assume_terms(proof) {
        assert!(asserted.contains(&ay_dpll::normalize_premise_surface(&assume)));
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert!(
        run_carcara_trust_free(&carcara, label, &problem, proof),
        "{label}: proof must be externally VALID, not merely holey"
    );
    let source_premise = "(assert (= p0 (bvadd #x08 #x08)))\n";
    assert_eq!(problem.matches(source_premise).count(), 1);
    let missing = problem.replacen(source_premise, "", 1);
    assert_ne!(
        carcara_verdict_without_allowances(
            &carcara,
            "folded_index_missing_premise",
            &missing,
            proof
        ),
        CarcaraVerdict::Valid
    );
    // Replace a required Assume with the other authored premise against the
    // SAME unchanged UNSAT problem. Source admission alone cannot reject this
    // corruption; the actual derivation must refuse the missing p0 evidence.
    let premise_line = proof
        .lines()
        .find(|line| line.starts_with("(assume ") && line.contains("(= p0 "))
        .expect("actual source p0 premise");
    let wrong_line = premise_line.replacen("(= p0 ", "(= p1 ", 1);
    assert_ne!(wrong_line, premise_line);
    let wrong_proof = proof.replacen(premise_line, &wrong_line, 1);
    assert_ne!(
        carcara_verdict_without_allowances(
            &carcara,
            "folded_index_wrong_assume",
            &problem,
            &wrong_proof
        ),
        CarcaraVerdict::Valid
    );
}

/// NEGATIVE TWIN of
/// [`test_carcara_trust_free_authored_folded_bv_index_shared_term`]: the two
/// uses spelled `(bvudiv #x20 #x02)` and `#x10` share no authored term, and
/// meet in the ground closure only through an `Evaluated` edge, which it does
/// not propose for `bvudiv` (`EVALUATED_OPERATORS`; pinned Carcara refuses the
/// divider steps that evaluation prints). Whatever `(get-proof)` answers, it
/// must never be a document Carcara refuses. Measured today it is withheld
/// as `UNVERIFIABLE PROOF`.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_unevaluated_folded_bv_index_never_publishes_a_refused_document() {
    let problem = row1_authored_index_problem("(bvudiv #x20 #x02)", "#x10");
    let label = "authored_unevaluated_folded_bv_index";
    let script = format!("(set-option :produce-proofs true)\n{problem}\n(get-proof)\n");
    let commands = parse(&script).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{label}: {outputs:?}"
    );
    let proof = outputs.last().cloned().expect("get-proof output");
    let published = proof.contains("(assume ") || proof.contains("(step ");
    if !published {
        assert!(
            proof.contains("UNVERIFIABLE PROOF"),
            "{label}: a withheld document must say so:\n{proof}"
        );
        return;
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert!(
        run_carcara_trust_free(&carcara, label, &problem, &proof),
        "{label}: a published document must be Carcara `valid`:\n{proof}"
    );
}
