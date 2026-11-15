// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Word-level translation-validation roots: one nested authored conjunction
//! whose last conjunct negates the claim, refuted by congruence through slice
//! identities instead of a bit-level miter.
//!
//! The fixtures are external-codegen x86-64 body theorems from the Darwin `core`
//! proof census (`census-distinct`, 2026-10-01), verbatim or minimized. Before
//! this lane learned nested conjunctions, negated composite goals and slice
//! identities, every one of them left the placeholder in place (the lane read
//! only the first `and` level and had no rule for `extract(zero_extend(v))`),
//! and AY answered `unknown (incomplete self-check-rejected)`.

use super::*;

/// Census query `101fca904a102615`, verbatim: a 32-bit `imul` against its
/// machine lowering through zero-extended 64-bit registers. No SAT budget
/// closes the bit-level multiplier miter; two slice identities and one
/// congruence do.
const SLICE_PRODUCT: &str = r#"
(set-option :produce-proofs true)
(set-logic QF_BV)
(declare-const e_rdi (_ BitVec 64))
(declare-const e_rsi (_ BitVec 64))
(declare-const p0 (_ BitVec 32))
(declare-const p1 (_ BitVec 32))
(declare-const s0 (_ BitVec 32))
(declare-const m0 (_ BitVec 64))
(declare-const m1 (_ BitVec 64))
(declare-const m2 (_ BitVec 64))
(declare-const m3 (_ BitVec 64))
(assert (and (= p0 ((_ extract 31 0) e_rdi)) (and (= p1 ((_ extract 31 0) e_rsi)) (and (= s0 (bvmul p0 p1)) (and (= m0 ((_ zero_extend 32) ((_ extract 31 0) e_rdi))) (and (= m1 ((_ zero_extend 32) ((_ extract 31 0) e_rsi))) (and (= m2 ((_ zero_extend 32) (bvmul ((_ extract 31 0) m0) ((_ extract 31 0) m1)))) (and (= m3 ((_ zero_extend 32) ((_ extract 31 0) m2))) (not (= s0 ((_ extract 31 0) m3)))))))))))
(check-sat)
"#;

/// Census query `057d5f06ef20f7b5`, minimized: SSA copies on both sides and
/// one negated `(= true (and ..))` claim, refuted by congruence over a 64-bit
/// product (a `bvadd` in the census query; a product here, so no bit-blast
/// rescue can close it first).
const NESTED_CLAIM: &str = r#"
(set-option :produce-proofs true)
(set-logic QF_BV)
(declare-const e_rdi (_ BitVec 64))
(declare-const e_rsi (_ BitVec 64))
(declare-const p0 (_ BitVec 64))
(declare-const s0 (_ BitVec 64))
(declare-const s1 (_ BitVec 64))
(declare-const s2 (_ BitVec 64))
(declare-const m0 (_ BitVec 64))
(declare-const m1 (_ BitVec 64))
(declare-const m2 (_ BitVec 64))
(declare-const m3 (_ BitVec 64))
(assert (and (= p0 e_rdi) (and (= s0 p0) (and (= s1 e_rsi) (and (= s2 (bvmul s0 s1)) (and (= m0 e_rdi) (and (= m1 m0) (and (= m2 e_rsi) (and (= m3 (bvmul m1 m2)) (not (= true (and (= p0 m0) (and (= s2 m3) (= s1 m2))))))))))))))
(check-sat)
"#;

/// Census query `2a1aabb3949a5165`, minimized: a flag bit rebuilt through a
/// byte read of a concatenation and two zero extensions, one of them read
/// across its boundary (`extract[31:0]` of a zero-extended byte).
const STRADDLED_FLAG: &str = r#"
(set-option :produce-proofs true)
(set-logic QF_BV)
(declare-const r2 (_ BitVec 1))
(declare-const g2 (_ BitVec 56))
(declare-const s30 (_ BitVec 1))
(declare-const s28 (_ BitVec 64))
(declare-const m40 (_ BitVec 64))
(declare-const m42 (_ BitVec 64))
(declare-const m43 (_ BitVec 64))
(assert (and (= s30 r2) (and (= s28 (bvmul m40 m40)) (and (= m42 ((_ zero_extend 56) ((_ extract 7 0) (concat g2 ((_ zero_extend 7) r2))))) (and (= m43 ((_ zero_extend 32) ((_ extract 31 0) m42))) (not (= true (and (= ((_ zero_extend 31) s30) ((_ extract 31 0) m43)) (= s28 (bvmul m40 m40))))))))))
(check-sat)
"#;

/// Census query `e2953c57e567f614`, verbatim but for its options: a `cmp`
/// flag the source keeps as `(ite (= s7 s8) #b1 #b0)` and the machine side
/// materializes as a byte `(ite (= (bvsub ..) #x00000000) #x01 #x00)`, read
/// back zero-extended. Refuted by the zero-difference identity, congruence
/// over `=`, `ite` and the slice identities, with the constant branches
/// folded through the extension.
const DIFFERENCE_FLAG: &str = r#"
(set-option :produce-proofs true)
(set-logic QF_BV)
(declare-const e_rdi (_ BitVec 64))
(declare-const e_rsi (_ BitVec 64))
(declare-const e_rdx (_ BitVec 64))
(declare-const r0 (_ BitVec 32))
(declare-const g0 (_ BitVec 32))
(declare-const u0 (_ BitVec 56))
(declare-const p0 (_ BitVec 64))
(declare-const p1 (_ BitVec 64))
(declare-const p2 (_ BitVec 64))
(declare-const s0 (_ BitVec 64))
(declare-const s1 (_ BitVec 64))
(declare-const s2 (_ BitVec 64))
(declare-const s3 (_ BitVec 64))
(declare-const s4 (_ BitVec 64))
(declare-const s5 (_ BitVec 64))
(declare-const s6 (_ BitVec 64))
(declare-const s7 (_ BitVec 32))
(declare-const s8 (_ BitVec 32))
(declare-const s9 (_ BitVec 1))
(declare-const m0 (_ BitVec 64))
(declare-const m1 (_ BitVec 64))
(declare-const m2 (_ BitVec 64))
(declare-const m3 (_ BitVec 64))
(declare-const m4 (_ BitVec 64))
(declare-const m5 (_ BitVec 64))
(declare-const m6 (_ BitVec 64))
(declare-const m7 (_ BitVec 64))
(declare-const m8 (_ BitVec 64))
(declare-const m9 (_ BitVec 64))
(declare-const m10 (_ BitVec 64))
(declare-const m11 (_ BitVec 64))
(declare-const m12 (_ BitVec 64))
(declare-const m13 (_ BitVec 64))
(declare-const m14 (_ BitVec 64))
(declare-const m15 (_ BitVec 64))
(declare-const m16 (_ BitVec 64))
(declare-const m17 (_ BitVec 64))
(assert (and (= p0 e_rdi) (and (= p1 e_rsi) (and (= p2 e_rdx) (and (= s0 (_ bv1 64)) (and (= s1 (bvmul p2 s0)) (and (= s2 p0) (and (= s3 p1) (and (= s4 s2) (and (= s5 s3) (and (= s6 s1) (and (= s7 r0) (and (= s8 (_ bv0 32)) (and (= s9 (ite (= s7 s8) (_ bv1 1) (_ bv0 1))) (and (= m0 e_rdi) (and (= m1 e_rsi) (and (= m2 e_rdx) (and (= m3 (_ bv1 64)) (and (= m4 (bvmul m2 m3)) (and (= m5 m0) (and (= m6 m1) (and (= m7 m5) (and (= m8 m6) (and (= m9 m4) (and (= m10 m7) (and (= m11 m8) (and (= m12 m9) (and (= m13 ((_ zero_extend 32) ((_ extract 31 0) (concat g0 r0)))) (and (= m14 (_ bv0 64)) (and (= m15 (concat u0 (ite (= (bvsub ((_ extract 31 0) m13) ((_ extract 31 0) m14)) (_ bv0 32)) (_ bv1 8) (_ bv0 8)))) (and (= m16 ((_ zero_extend 56) ((_ extract 7 0) m15))) (and (= m17 ((_ zero_extend 32) ((_ extract 31 0) m16))) (not (= true (and (= ((_ zero_extend 31) s9) ((_ extract 31 0) m17)) (and (= s4 m10) (and (= s5 m11) (= s6 m12))))))))))))))))))))))))))))))))))))))
(check-sat)
"#;

fn unit_bv_lemmas(proof: &Proof) -> usize {
    lemma_count(proof, |kind, clause| {
        matches!(kind, TheoryLemmaKind::BvBitBlast) && clause.len() == 1
    })
}

/// The published document: every bit-vector lemma it prints, and no
/// multiplier circuit. A product enters a slice identity only as one opaque
/// word (`bitblast_var`); the whole point is that it is never bit-blasted.
fn assert_no_multiplier_circuit(exec: &Executor, proof: &Proof) {
    let scope = exec
        .proof_export_scope_assertions_for(proof)
        .expect("an export scope");
    let overrides = exec.proof_export_term_overrides();
    let surfaces = exec.authored_export_surfaces();
    let document = ay_proof::try_export_alethe_with_authored_surfaces(
        proof,
        &exec.ctx.terms,
        &scope,
        overrides.as_ref(),
        surfaces.channels(),
        Some(DEFAULT_ALETHE_EMISSION_WORK_BUDGET),
    )
    .expect("the committed proof renders");
    assert!(!document.contains(":rule hole") && !document.contains(":rule trust"));
    assert!(
        !document.contains("bitblast_mult"),
        "a multiplier circuit was printed"
    );
}

fn mentions(terms: &TermStore, root: TermId, name: &str) -> bool {
    let mut pending = vec![root];
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::App(symbol, args) => {
                if symbol.name() == name {
                    return true;
                }
                pending.extend(args.iter().copied());
            }
            TermData::Not(inner) => pending.push(*inner),
            TermData::Ite(c, t, e) => pending.extend([*c, *t, *e]),
            _ => {}
        }
    }
    false
}

fn rule_count(proof: &Proof, wanted: &AletheRule) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::Step { rule, .. } if rule == wanted))
        .count()
}

#[test]
fn a_product_read_through_zero_extended_registers_is_refuted_by_slice_identities() {
    let (mut exec, proof) = rebuilt(SLICE_PRODUCT);
    let slices = unit_bv_lemmas(&proof);
    assert!(slices >= 2, "two slice identities at least: {slices}");
    assert_no_multiplier_circuit(&exec, &proof);
    assert!(
        lemma_count(&proof, |kind, clause| matches!(
            kind,
            TheoryLemmaKind::EufCongruent
        ) && clause
            .iter()
            .any(|&literal| mentions(&exec.ctx.terms, literal, "bvmul")))
            >= 1,
        "the products are joined by congruence"
    );
    assert!(exec.presents_wire_clean(&proof));
}

#[test]
fn a_negated_nested_claim_is_refuted_by_and_neg_over_congruence() {
    let (mut exec, proof) = rebuilt(NESTED_CLAIM);
    assert_no_multiplier_circuit(&exec, &proof);
    assert_eq!(
        rule_count(&proof, &AletheRule::EquivNeg1),
        1,
        "one `(= true ..)`"
    );
    assert_eq!(
        rule_count(&proof, &AletheRule::AndNeg),
        2,
        "two claim levels"
    );
    assert!(
        rule_count(&proof, &AletheRule::AndPos(1)) >= 8,
        "nested projections"
    );
    assert!(exec.presents_wire_clean(&proof));
}

/// A session that retains no proof surface still certifies its `unsat`, and
/// this lane must find its roots there too. The regime is the one
/// `configure_unproved_smt_executor` gives an `ay --incremental` session: no
/// parsed surface, the definitional pass's budgeted copy armed. Before the
/// lane read that copy it found no roots in such a session, and the
/// one-shot proof's 0.1 s refutation of a 64-bit product became a bit-level
/// one that ran out external-codegen's 30 s resident deadline (`u64::wrapping_mul`,
/// AY build 12713).
#[test]
fn the_closure_finds_its_roots_in_a_session_that_retains_no_proof_surface() {
    let script = NESTED_CLAIM.replace(
        "(set-option :produce-proofs true)\n",
        "(set-option :timeout 20000)\n",
    );
    let commands = parse(&script).expect("fixture parses");
    let mut exec = Executor::new();
    exec.set_retain_parsed_assertions(false);
    exec.set_definitional_pass_parsed_budget(ay_frontend::CHECK_SAT_ADOPTION_MAX_RETAINED_NODES);
    let outputs = exec.execute_all(&commands).expect("fixture executes");
    assert!(
        exec.ctx.assertions_parsed().is_empty(),
        "the session retains no proof surface"
    );
    assert!(
        exec.ground_closure_roots().is_some(),
        "the lane reads the pass's copy of the same assertions"
    );
    assert_eq!(
        outputs,
        vec!["unsat"],
        "unknown_reason={:?}",
        exec.unknown_reason()
    );
}

/// The early attempt ahead of the Generic promotion asks whether the
/// ELABORATED assertions are pure bit-vector before the closure raw
/// re-interns any parsed root, and that question mints no term. Asked through
/// the closure itself, the attempt renumbered the terms of the session's next
/// check on the array-frame fixture (`group_proofs` `frame_ite_lift`, u64
/// guard), whose Skolemized re-solve then ended `unknown`.
#[test]
fn the_early_attempt_asks_purity_without_interning() {
    let mixed = "(set-logic ALL)\n(declare-fun s () (Array Int Int))\n\
                 (declare-fun v () Int)\n(declare-const b (_ BitVec 8))\n\
                 (assert (= (select s 0) v))\n(assert (= b #x01))\n\
                 (assert (forall ((k Int)) (>= (select s k) 0)))\n";
    let pure = NESTED_CLAIM.replace("(check-sat)\n", "");
    for (script, expected) in [(mixed, false), (pure.as_str(), true)] {
        let commands = parse(script).expect("fixture parses");
        let mut exec = Executor::new();
        exec.execute_all(&commands).expect("fixture executes");
        assert!(
            !exec.ctx.assertions.is_empty(),
            "the assertions are elaborated"
        );
        let terms = exec.ctx.terms.len();
        assert_eq!(exec.elaborated_assertions_are_pure_bit_vector(), expected);
        assert_eq!(exec.ctx.terms.len(), terms, "the question interns nothing");
    }
}

#[test]
fn a_zero_extension_read_across_its_boundary_is_rewritten() {
    let (mut exec, proof) = rebuilt(STRADDLED_FLAG);
    let slices = unit_bv_lemmas(&proof);
    assert!(slices >= 3, "byte read, straddle and widening: {slices}");
    assert_no_multiplier_circuit(&exec, &proof);
    assert!(exec.presents_wire_clean(&proof));
}

/// NEGATIVE TWIN: the claim needs `bvmul` commutativity, which is neither a
/// slice identity nor congruence. The lane must leave the proof untouched,
/// whatever the rest of the pipeline answers. (The words are bytes so the
/// pipeline's own bit-level members finish quickly.)
#[test]
fn a_commuted_product_is_not_a_slice_identity() {
    let commuted = r#"
(set-option :produce-proofs true)
(set-logic QF_BV)
(declare-const e_rdi (_ BitVec 64))
(declare-const e_rsi (_ BitVec 64))
(declare-const s0 (_ BitVec 8))
(declare-const m0 (_ BitVec 64))
(declare-const m1 (_ BitVec 64))
(declare-const m2 (_ BitVec 64))
(assert (and (= s0 (bvmul ((_ extract 7 0) e_rdi) ((_ extract 7 0) e_rsi))) (and (= m0 ((_ zero_extend 56) ((_ extract 7 0) e_rdi))) (and (= m1 ((_ zero_extend 56) ((_ extract 7 0) e_rsi))) (and (= m2 ((_ zero_extend 56) (bvmul ((_ extract 7 0) m1) ((_ extract 7 0) m0)))) (not (= s0 ((_ extract 7 0) m2))))))))
(check-sat)
"#;
    let commands = parse(commuted).expect("fixture parses");
    let mut exec = Executor::new();
    let _ = exec.execute_all(&commands).expect("fixture executes");
    let mut proof = placeholder();
    let before = format!("{:?}", proof.steps);
    exec.replace_with_raw_authored_ground_closure_refutation(&mut proof);
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// NEGATIVE TWIN: the high half of a sign extension is not a slice of its
/// argument, so it is never rewritten; the claim below is satisfiable
/// (`v = #x80000000`), and the solver must say so.
#[test]
fn the_high_half_of_a_sign_extension_is_not_rewritten() {
    let sat = r#"
(set-option :produce-proofs true)
(set-logic QF_BV)
(declare-const v (_ BitVec 32))
(declare-const m (_ BitVec 64))
(assert (and (= m ((_ sign_extend 32) v)) (not (= ((_ extract 63 32) m) #x00000000))))
(check-sat)
"#;
    let mut exec = solved(sat, "sat");
    let parsed: Vec<FrontendTerm> = exec.ctx.assertions_parsed().to_vec();
    let root = exec.raw_intern_surface(&parsed[0]).expect("raw root");
    let TermData::App(_, conjuncts) = exec.ctx.terms.get(root).clone() else {
        panic!("conjunction");
    };
    let TermData::Not(claim) = exec.ctx.terms.get(conjuncts[1]).clone() else {
        panic!("negated claim");
    };
    let (high, _) = decode_eq_local(&exec.ctx.terms, claim).expect("equality");
    let (_, extended) = decode_eq_local(&exec.ctx.terms, conjuncts[0]).expect("pin");
    assert_eq!(exec.slice_rewrite(high, extended), None);
}

/// A forged slice edge (`extract[31:0](zero_extend 32 #x00000001)` equated
/// with zero) yields a candidate that derives the empty clause, and the strict
/// checker, not the producer, refuses it.
#[test]
fn a_forged_slice_identity_is_refused_by_the_strict_checker() {
    let mut exec = Executor::new();
    let one = exec.ctx.terms.mk_bitvec(BigInt::from(1), 32);
    let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0), 32);
    let wide = exec.ctx.terms.mk_app(
        Symbol::indexed("zero_extend", vec![32]),
        [one],
        Sort::bitvec(64),
    );
    let low = exec.ctx.terms.mk_app(
        Symbol::indexed("extract", vec![31, 0]),
        [wide],
        Sort::bitvec(32),
    );
    let mut search = GroundSearch::default();
    for term in [low, wide, one, zero] {
        search.closure.register(term);
    }
    assert!(search.closure.merge(low, zero, EdgeReason::SliceIdentity));
    assert!(search.closure.merge(low, one, EdgeReason::Evaluated));
    let candidate = exec
        .emit_ground_closure_refutation(&search, ClosureConflict::ConstantClash(zero, one))
        .expect("emission trusts its edges; the checker does not");
    assert!(Executor::proof_derives_empty_clause(&candidate));
    let refusal = exec
        .check_proof_strict_with_datatypes(&candidate)
        .expect_err("extract[31:0](zero_extend 32 #x00000001) = 0 is not a theorem")
        .to_string();
    assert!(
        refusal.contains("bv_bitblast"),
        "refused at the forged slice lemma itself: {refusal}"
    );
    let mut proof = placeholder();
    let before = format!("{:?}", proof.steps);
    assert!(!exec.commit_raw_ground_closure(&mut proof, candidate, &[]));
    assert_eq!(format!("{:?}", proof.steps), before);
}

#[test]
fn a_flag_materialized_from_a_zero_difference_is_refuted_through_ite() {
    let (mut exec, proof) = rebuilt(DIFFERENCE_FLAG);
    assert_no_multiplier_circuit(&exec, &proof);
    let ite_congruences = proof
        .steps
        .iter()
        .filter(|step| {
            matches!(step, ProofStep::Step { rule: AletheRule::Cong, clause, .. }
            if matches!(clause.as_slice(), [literal] if decode_eq_local(&exec.ctx.terms, *literal)
                .is_some_and(|(lhs, _)| matches!(exec.ctx.terms.get(lhs), TermData::Ite(..)))))
        })
        .count();
    assert!(
        ite_congruences >= 1,
        "the two flags meet by congruence over `ite`"
    );
    assert!(exec.presents_wire_clean(&proof));
}
