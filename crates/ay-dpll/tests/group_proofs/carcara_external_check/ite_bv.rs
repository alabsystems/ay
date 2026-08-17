// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// A negated ITE condition canonicalizes by swapping branch order. Any proof
/// that is still published must honor the authored positional surface when
/// checked independently; declining the unsupported spelling is also sound.
#[test]
#[timeout(60_000)]
fn test_carcara_negated_condition_ite_is_valid_or_fails_closed() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    for (label, definition) in [
        (
            "negated_condition_formula_ite",
            "(assert (ite (not (= J 1)) (= I E) (= I (+ E F))))",
        ),
        (
            "negated_condition_rhs_ite",
            "(assert (= I (ite (not (= J 1)) E (+ E F))))",
        ),
    ] {
        let problem = arithmetic_ite_nonnegative_problem("", definition, "(assert (< I 0))");
        let Some(proof) = solve_or_fail_closed_and_maybe_get_proof(&problem, label) else {
            continue;
        };
        assert!(!proof.contains(":rule trust"), "{label}: {proof}");
        assert!(
            run_carcara_trust_free(&carcara, label, &problem, &proof),
            "{label}: Carcara must accept any published proof"
        );
    }
}

/// QF_UF proofs on simple benchmarks should be fully verifiable without trust steps.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_qf_uf() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let proof = solve_unsat_and_get_proof(QF_UF_UNSAT, "trust_free_qf_uf");
    assert!(
        run_carcara_trust_free(&carcara, "trust_free_qf_uf", QF_UF_UNSAT, &proof),
        "QF_UF proof must be trust-free verifiable by carcara"
    );
}

/// The witnessed-universe EPR lane may instantiate complementary authored
/// universals at an authored ground term. Its native strict check is necessary
/// but not sufficient for the public artifact contract: independently require
/// the emitted `forall_inst` document to pass Carcara with no trust allowance.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_authored_witness_forall_conflict() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let label = "trust_free_authored_witness_forall_conflict";
    let proof = solve_unsat_and_get_proof(UF_AUTHORED_WITNESS_FORALL_CONFLICT_UNSAT, label);
    assert!(proof.contains(":rule forall_inst"), "{proof}");
    assert!(!proof.contains(":rule trust"), "{proof}");
    assert!(!proof.contains("(declare-"), "{proof}");
    assert!(
        run_carcara_trust_free(
            &carcara,
            label,
            UF_AUTHORED_WITNESS_FORALL_CONFLICT_UNSAT,
            &proof,
        ),
        "authored-witness forall conflict must validate without allowed trust"
    );
}

/// The direct E-matching proof lane must agree with the independent Alethe
/// checker, including authored-forall surface binding and Farkas literal order.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_auflia_ematching_forall_equality() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let label = "trust_free_auflia_ematching_forall_equality";
    let proof = solve_unsat_and_get_proof(AUFLIA_EMATCHING_FORALL_EQUALITY_UNSAT, label);
    assert!(!proof.contains(":rule trust"), "{proof}");
    assert!(proof.contains(":rule forall_inst"), "{proof}");
    assert!(proof.contains(":rule la_generic"), "{proof}");
    assert!(
        run_carcara_trust_free(
            &carcara,
            label,
            AUFLIA_EMATCHING_FORALL_EQUALITY_UNSAT,
            &proof,
        ),
        "AUFLIA E-matching proof must be verified without allowed trust"
    );
}

/// Exercise exact Clean composed roots and linear fold-to-false source roots
/// through the independent Alethe checker so a locally strict proof cannot
/// mask a surface mismatch.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_composed_authored_roots() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };

    let cases = [
        (
            "trust_free_qf_uf_composed_authored_root",
            QF_UF_COMPOSED_AUTHORED_ROOT_UNSAT,
            QF_UF_COMPOSED_AUTHORED_ROOT_UNSAT,
        ),
        (
            "trust_free_qf_lia_composed_authored_root",
            QF_LIA_COMPOSED_AUTHORED_ROOT_UNSAT,
            QF_LIA_COMPOSED_AUTHORED_ROOT_UNSAT,
        ),
        (
            "trust_free_qf_auflia_composed_row2_root",
            QF_AUFLIA_COMPOSED_ROW2_ROOT_UNSAT,
            QF_AUFLIA_COMPOSED_ROW2_ROOT_UNSAT,
        ),
        (
            "trust_free_qf_lia_linear_and_fold",
            QF_LIA_LINEAR_AND_FOLD_UNSAT,
            QF_LIA_LINEAR_AND_FOLD_UNSAT,
        ),
        (
            "trust_free_qf_lia_literal_false",
            QF_LIA_LITERAL_FALSE_UNSAT,
            QF_LIA_LITERAL_FALSE_UNSAT,
        ),
        (
            "trust_free_qf_lia_mod_assuming",
            QF_LIA_MOD_ASSUMING_UNSAT,
            QF_LIA_MOD_ASSUMING_CARCARA_SCOPE,
        ),
        (
            "trust_free_qf_auflia_linear_assuming",
            QF_AUFLIA_LINEAR_ASSUMING_UNSAT,
            QF_AUFLIA_LINEAR_ASSUMING_CARCARA_SCOPE,
        ),
        (
            "trust_free_qf_lra_guarded_split",
            QF_LRA_GUARDED_SPLIT_UNSAT,
            QF_LRA_GUARDED_SPLIT_UNSAT,
        ),
        (
            "trust_free_qf_lia_let_linear_and_fold",
            QF_LIA_LET_LINEAR_AND_FOLD_UNSAT,
            QF_LIA_LET_LINEAR_AND_FOLD_UNSAT,
        ),
    ];

    for (label, solver_problem, carcara_problem) in cases {
        let proof = solve_unsat_and_get_proof(solver_problem, label);
        assert!(
            !proof.contains(":rule trust") && !proof.contains(":rule hole"),
            "{label}: composed-root proof must not contain unchecked rules:\n{proof}"
        );
        assert!(
            run_carcara_trust_free(&carcara, label, carcara_problem, &proof),
            "{label}: composed-root proof must be trust-free verifiable by carcara"
        );
    }
}

/// Store-commutativity has NO counterpart rule in the pinned checker, so the
/// lemma is lowered as a derivation over the array rules carcara does have.
/// Both chain lengths must come back trust-free `valid`, not `holey`.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_array_store_permutation() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };

    for (label, problem) in [
        (
            "trust_free_qf_auflia_store_permutation",
            QF_AUFLIA_STORE_PERMUTATION_UNSAT,
        ),
        (
            "trust_free_qf_auflia_store_permutation_chain3",
            QF_AUFLIA_STORE_PERMUTATION_CHAIN3_UNSAT,
        ),
    ] {
        let proof = solve_unsat_and_get_proof(problem, label);
        assert!(
            !proof.contains(":rule trust") && !proof.contains(":rule hole"),
            "{label}: store-permutation proof must not contain unchecked rules:\n{proof}"
        );
        // The unknown internal name must never reach the wire either.
        assert!(!proof.contains("store_permutation"), "{label}:\n{proof}");
        for rule in [":rule arrays_ext", ":rule arrays_row", ":rule arrays_idx"] {
            assert!(proof.contains(rule), "{label}: missing {rule}:\n{proof}");
        }
        assert!(
            run_carcara_trust_free(&carcara, label, problem, &proof),
            "{label}: store-permutation proof must be trust-free verifiable by carcara"
        );
    }
}

/// REGRESSION: a store chain mentioning a user symbol literally named `x`
/// collides with the `arrays_ext` witness's `choice` binder. The lowering
/// must DECLINE — the document stays an honest `hole` and carcara checks it
/// as `holey`, never `invalid` — while a chain that does not mention `x`
/// keeps the full derivation and the trust-free `valid` verdict.
#[test]
#[timeout(60_000)]
fn test_carcara_store_permutation_binder_collision_stays_holey() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };

    let label = "store_permutation_binder_collision";
    let problem = QF_AUFLIA_STORE_PERMUTATION_BINDER_COLLISION_UNSAT;
    let proof = solve_unsat_and_get_proof(problem, label);
    assert!(
        proof.contains(":rule hole"),
        "{label}: the colliding chain must keep the honest hole:\n{proof}"
    );
    // No witness may be built over the colliding chain at all: any
    // `(choice ((x ...)` in this document would capture the clause's own `x`.
    assert!(
        !proof.contains("(choice ((x "),
        "{label}: no witness may capture the user symbol x:\n{proof}"
    );
    assert!(
        run_carcara(&carcara, label, problem, &proof),
        "{label}: the honest hole must leave the document checkable (holey), never invalid"
    );

    // Control: the SAME schema over symbols that do not collide with the
    // binder keeps the derivation and stays trust-free `valid`.
    let control = "store_permutation_binder_collision_control";
    let proof = solve_unsat_and_get_proof(QF_AUFLIA_STORE_PERMUTATION_UNSAT, control);
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{control}: the non-colliding chain must keep the derivation:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(&carcara, control, QF_AUFLIA_STORE_PERMUTATION_UNSAT, &proof),
        "{control}: the non-colliding chain must stay trust-free valid"
    );
}

/// The exact QF_ABV regression must remain self-contained: the authored nested
/// concat and binary `distinct` are bridged explicitly, while the closed
/// constant folds use Carcara's checked `evaluate` rule.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_qf_abv_pinned_concat_substitution() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let label = "trust_free_qf_abv_pinned_concat_substitution";
    let proof = solve_unsat_and_get_proof(QF_ABV_PINNED_CONCAT_UNSAT, label);
    assert!(
        !proof.contains(":rule trust") && !proof.contains(":rule hole"),
        "QF_ABV regression proof must not contain unchecked rules:\n{proof}"
    );
    assert!(
        !proof.contains(":rule bv_bitblast"),
        "closed concat folding must use Carcara's evaluate rule, not AY's private bv_bitblast rule:\n{proof}"
    );
    assert!(
        proof.contains(":rule evaluate"),
        "closed concat folding must be certified by evaluate:\n{proof}"
    );
    assert!(
        proof.contains(":rule distinct_elim"),
        "surface distinct must be linked to its canonical disequality:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(&carcara, label, QF_ABV_PINNED_CONCAT_UNSAT, &proof),
        "QF_ABV pinned-concat proof must be verified by Carcara without allowed trust"
    );
}

/// AY has ONE coarse `bv_bitblast` theory-lemma kind where Carcara has a
/// fine-grained `bitblast_*` suite; the two are not interchangeable, because
/// every Carcara `bitblast_*` rule concludes `(= <word-level term> (@bbterm
/// ...))` while an AY BV lemma is a word-level tautology. The bit-wise
/// idempotency identity IS exactly reconstructible from that suite, so it must
/// export as a real per-operator derivation rather than the honest `hole` it
/// used to print.
#[test]
#[timeout(120_000)]
fn test_carcara_trust_free_qf_bv_idempotent_gate_bitblast() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    for (label, operator, blast_rule, simplify_rule) in [
        (
            "trust_free_qf_bv_bvand_idempotent",
            "bvand",
            ":rule bitblast_and",
            ":rule and_simplify",
        ),
        (
            "trust_free_qf_bv_bvor_idempotent",
            "bvor",
            ":rule bitblast_or",
            ":rule or_simplify",
        ),
    ] {
        let problem = format!(
            "(set-logic QF_BV)\n\
             (declare-const x (_ BitVec 8))\n\
             (assert (not (= ({operator} x x) x)))\n\
             (check-sat)\n"
        );
        let proof = solve_unsat_and_get_proof(&problem, label);
        assert!(
            !proof.contains(":rule trust") && !proof.contains(":rule hole"),
            "{label}: bit-blast identity proof must not contain unchecked rules:\n{proof}"
        );
        assert!(
            !proof.contains(":rule bv_bitblast"),
            "{label}: AY's private coarse rule name must never reach the wire:\n{proof}"
        );
        for expected in [blast_rule, ":rule bitblast_var", simplify_rule] {
            assert!(
                proof.contains(expected),
                "{label}: identity must be derived through Carcara's per-operator \
                 bit-blasting, missing {expected}:\n{proof}"
            );
        }
        let scope = published_assumption_scope("(declare-const x (_ BitVec 8))\n", &proof);
        assert!(
            run_carcara_trust_free(&carcara, label, &scope, &proof),
            "{label}: per-operator bit-blast derivation must be verified by Carcara \
             without allowed trust"
        );
    }
}

/// The NESTED per-operator case. A Carcara `bitblast_*` rule relates exactly
/// ONE word-level operator to a `@bbterm`, so `(bvnot (bvnot x)) = x` has to
/// be blasted bottom-up: `bitblast_not`, `cong`, `bitblast_not` again.
#[test]
#[timeout(120_000)]
fn test_carcara_trust_free_qf_bv_double_negation_bitblast() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let label = "trust_free_qf_bv_double_negation";
    let problem = "(set-logic QF_BV)\n\
                   (declare-const x (_ BitVec 8))\n\
                   (assert (not (= (bvnot (bvnot x)) x)))\n\
                   (check-sat)\n";
    let proof = solve_unsat_and_get_proof(problem, label);
    assert!(
        !proof.contains(":rule trust") && !proof.contains(":rule hole"),
        "{label}: double-negation proof must not contain unchecked rules:\n{proof}"
    );
    assert!(
        !proof.contains(":rule bv_bitblast"),
        "{label}: AY's private coarse rule name must never reach the wire:\n{proof}"
    );
    for expected in [
        ":rule bitblast_not",
        ":rule bitblast_var",
        ":rule not_simplify",
    ] {
        assert!(
            proof.contains(expected),
            "{label}: missing {expected} in the nested bit-blast derivation:\n{proof}"
        );
    }
    let scope = published_assumption_scope("(declare-const x (_ BitVec 8))\n", &proof);
    assert!(
        run_carcara_trust_free(&carcara, label, &scope, &proof),
        "{label}: nested bit-blast derivation must be verified by Carcara without \
         allowed trust"
    );
}

/// NEGATIVE regression for the per-operator bit-blast lowering.
///
/// `(bvxor x x) = #x00` is a bit-vector identity AY certifies natively and
/// Carcara CAN bit-blast the operator (`bitblast_xor`), but the bit-level
/// residue is `(xor p p) = false` and no rule in the pinned build discharges
/// that in one step (`bool_simplify`, `evaluate`, `aci_simp`, `equiv_simplify`
/// and `not_simplify` were all measured to leave the term unchanged). So the
/// lowering MUST decline: the step stays an honest `hole` and the document
/// stays structurally checkable, rather than becoming `invalid` under a rule
/// name whose inference this is not.
#[test]
#[timeout(120_000)]
fn test_carcara_bvxor_self_cancellation_remains_an_honest_hole() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let label = "bvxor_self_cancellation_honest_hole";
    let problem = "(set-logic QF_BV)\n\
                   (declare-const x (_ BitVec 8))\n\
                   (assert (not (= (bvxor x x) #x00)))\n\
                   (check-sat)\n";
    let proof = solve_unsat_and_get_proof(problem, label);
    assert!(
        !proof.contains(":rule bitblast_"),
        "{label}: the per-operator lowering must not fire on an identity whose \
         bit-level residue Carcara cannot discharge:\n{proof}"
    );
    assert!(
        proof.contains(":rule hole"),
        "{label}: the uncovered identity must stay an honest hole:\n{proof}"
    );
    let scope = published_assumption_scope("(declare-const x (_ BitVec 8))\n", &proof);
    assert!(
        run_carcara(&carcara, label, &scope, &proof),
        "{label}: an honest hole must leave the rest of the document checkable, \
         never make it invalid"
    );
}
