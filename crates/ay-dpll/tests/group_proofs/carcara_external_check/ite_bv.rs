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
        if label == "trust_free_qf_lia_let_linear_and_fold" {
            // This proof deliberately certifies source-level let elimination.
            // Carcara's parser-side `--expand-let-bindings` option erases the
            // left-hand let before the `let` rule can validate it, so exercise
            // that rule in the ordinary parser mode, just like the dedicated
            // let-bridge regression below.
            let (valid, diagnostic) =
                exact_carcara_verdict(&carcara, carcara_problem, &proof);
            assert!(
                valid,
                "{label}: source-exact composed-root proof must be trust-free \
                 verifiable by carcara: {diagnostic}"
            );
        } else {
            assert!(
                run_carcara_trust_free(&carcara, label, carcara_problem, &proof),
                "{label}: composed-root proof must be trust-free verifiable by carcara"
            );
        }
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
    for (operator, blast_rule, simplify_rule) in [
        ("bvand", ":rule bitblast_and", ":rule and_simplify"),
        ("bvor", ":rule bitblast_or", ":rule or_simplify"),
    ] {
        // The lowering is per-BIT, so the width is the load-bearing axis: 8 is
        // the historical case, 32 is the width code-generator guard
        // obligations actually arrive at, and 64 is the printer's
        // `MAX_BITBLAST_LOWERING_WIDTH` boundary itself.
        for width in [8u32, 32, 64] {
            let label = format!("trust_free_qf_bv_{operator}_idempotent_w{width}");
            let label = label.as_str();
            let declarations = format!("(declare-const x (_ BitVec {width}))\n");
            let problem = format!(
                "(set-logic QF_BV)\n\
                 {declarations}\
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
            let scope = published_assumption_scope(&declarations, &proof);
            assert!(
                run_carcara_trust_free(&carcara, label, &scope, &proof),
                "{label}: per-operator bit-blast derivation must be verified by Carcara \
                 without allowed trust"
            );
        }
    }
}

/// The idempotent gate NESTED BELOW A CONGRUENCE SPINE, which is the shape a
/// verified code generator's division-guard obligations actually produce:
///
/// ```text
/// (= (ite (= t #b0..0) #b1 #b0) (ite (= (bvand t t) #b0..0) #b1 #b0))
/// ```
///
/// The gate sits two levels below the equated `ite`s, so the printer's
/// top-level idempotency lowering cannot see it. Unless the rewrite spine is
/// decomposed — small `(= t (bvand t t))` crux, then `cong` up through the `=`
/// and the `ite` — AY mints ONE coarse lemma over the whole `ite` equality that
/// it can DECIDE but not TYPESET, and the document goes out with an honest
/// `hole`. This is the family the 32-bit reproducer above is extracted from,
/// so it is pinned at the width the code generator emits.
#[test]
#[timeout(120_000)]
fn test_carcara_trust_free_qf_bv_idempotent_gate_below_ite_congruence() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let label = "trust_free_qf_bv_idempotent_gate_below_ite";
    let declarations = "(declare-const lhs (_ BitVec 32))\n";
    let problem = format!(
        "(set-logic QF_BV)\n\
         {declarations}\
         (assert (not (= (ite (= lhs (_ bv0 32)) (_ bv1 1) (_ bv0 1)) \
         (ite (= (bvand lhs lhs) (_ bv0 32)) (_ bv1 1) (_ bv0 1)))))\n\
         (check-sat)\n"
    );
    let proof = solve_unsat_and_get_proof(&problem, label);
    assert!(
        !proof.contains(":rule trust") && !proof.contains(":rule hole"),
        "{label}: the guard obligation must not go out with an unchecked step:\n{proof}"
    );
    assert!(
        !proof.contains(":rule bv_bitblast"),
        "{label}: AY's private coarse rule name must never reach the wire:\n{proof}"
    );
    // The crux must be lowered per bit AND lifted by congruence — a document
    // carrying only one of the two would not be this shape.
    for expected in [
        ":rule bitblast_and",
        ":rule bitblast_var",
        ":rule and_simplify",
        ":rule cong",
    ] {
        assert!(
            proof.contains(expected),
            "{label}: nested gate must be discharged by a per-bit lowering lifted \
             through congruence, missing {expected}:\n{proof}"
        );
    }
    let scope = published_assumption_scope(declarations, &proof);
    assert!(
        run_carcara_trust_free(&carcara, label, &scope, &proof),
        "{label}: the lifted derivation must be verified by Carcara without allowed trust"
    );
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

/// The rule of every SUB-STEP of the crux derivation, in emission order.
///
/// The printer names the crux's sub-steps after their parent step with a dotted
/// suffix (`t1.pa`, `t1.f1`, ...), so a dot in the step id is exactly the
/// "belongs to the lowered crux" marker; the surrounding `assume`/spine steps
/// carry plain ids and are skipped. Returning the rules IN ORDER is the point:
/// it lets a test pin the derivation's shape, not merely which rules appear.
fn crux_step_rules(proof: &str) -> Vec<String> {
    let mut rules = Vec::new();
    for chunk in proof.split("(step ").skip(1) {
        let Some(id) = chunk.split_whitespace().next() else {
            continue;
        };
        if !id.contains('.') {
            continue;
        }
        // Take this step's OWN rule: stop at the next step so a malformed or
        // rule-less chunk can never borrow its successor's rule name.
        let body = chunk.split("(step ").next().unwrap_or(chunk);
        if let Some(rule) = body.split(":rule ").nth(1) {
            let rule: String = rule
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if !rule.is_empty() {
                rules.push(rule);
            }
        }
    }
    rules
}

/// The UNSIGNED COMPARISON DUALITY below a congruence spine — the shape a
/// verified code generator's BOUNDS and SHIFT-RANGE guard obligations produce,
/// one guard over from the division-guard idempotency shape above:
///
/// ```text
/// (= (ite (bvuge lhs rhs) #b1 #b0) (ite (not (bvult lhs rhs)) #b1 #b0))
/// ```
///
/// The INTENDED trap set is spelled with the `bvuge` primitive; the EMITTED x86
/// `AE` condition code is the negation of the carry flag, i.e. `(not (bvult lhs
/// rhs))`. Carcara has NO `bitblast_*` rule whose conclusion carries `bvuge`, so
/// unlike every other lowering in this file the identity is reconstructed
/// through the PSEUDO-BOOLEAN family plus two checked `la_generic` clauses.
///
/// The structural assertions run unconditionally — carcara is optional here and
/// `require_carcara_or_skip` would silently skip the whole test on a box without
/// it, which is exactly how a regression to `hole` would go unnoticed.
#[test]
#[timeout(180_000)]
fn test_qf_bv_unsigned_compare_duality_below_ite_congruence() {
    let carcara = find_carcara();
    for (operator, dual, non_strict_rule, strict_rule) in [
        ("bvuge", "bvult", ":rule pbblast_bvuge", ":rule pbblast_bvult"),
        ("bvule", "bvugt", ":rule pbblast_bvule", ":rule pbblast_bvugt"),
    ] {
        // The three widths `run_guard_carrier_canary` actually requests.
        for width in [8u32, 32, 64] {
            let label = format!("unsigned_compare_duality_{operator}_w{width}");
            let label = label.as_str();
            let declarations = format!(
                "(declare-const lhs (_ BitVec {width}))\n\
                 (declare-const rhs (_ BitVec {width}))\n"
            );
            let problem = format!(
                "(set-logic QF_BV)\n\
                 {declarations}\
                 (assert (not (= (ite ({operator} lhs rhs) (_ bv1 1) (_ bv0 1)) \
                 (ite (not ({dual} lhs rhs)) (_ bv1 1) (_ bv0 1)))))\n\
                 (check-sat)\n"
            );
            let proof = solve_unsat_and_get_proof(&problem, label);
            assert!(
                !proof.contains(":rule trust") && !proof.contains(":rule hole"),
                "{label}: the guard obligation must not go out with an unchecked step:\n{proof}"
            );
            assert!(
                !proof.contains(":rule bv_bitblast"),
                "{label}: AY's private coarse rule name must never reach the wire:\n{proof}"
            );
            // The crux must be pseudo-Boolean-blasted on BOTH sides, bridged by
            // checked linear arithmetic, and lifted through the `ite` spine — a
            // document carrying only some of those would not be this derivation.
            for expected in [
                non_strict_rule,
                strict_rule,
                ":rule la_generic",
                ":rule equiv_neg1",
                ":rule equiv_neg2",
                ":rule not_not",
                ":rule cong",
            ] {
                assert!(
                    proof.contains(expected),
                    "{label}: missing {expected} in the duality derivation:\n{proof}"
                );
            }
            // PIN THE EXACT STEP SEQUENCE, not merely the set of rules used.
            // Presence alone would still pass if the steps were reordered, if a
            // step were duplicated, or if extra inferences crept in — none of
            // which is the derivation that was machine-checked. The sequence is
            // WIDTH-INVARIANT by construction: only the pseudo-Boolean sums grow
            // with the width, never the shape of the argument, so the identical
            // expectation is asserted at 8, 32 and 64.
            let emitted = crux_step_rules(&proof);
            let expected_sequence = [
                non_strict_rule.trim_start_matches(":rule "),
                strict_rule.trim_start_matches(":rule "),
                "la_generic",
                "la_generic",
                "equiv_neg1",
                "equiv_neg2",
                "resolution",
                "resolution",
                "resolution",
                "not_not",
                "resolution",
                "resolution",
                "cong",
                "symm",
                "trans",
            ];
            assert_eq!(
                emitted, expected_sequence,
                "{label}: the emitted crux derivation must be exactly the \
                 machine-checked step sequence, in order:\n{proof}"
            );
            let Some(carcara) = carcara.as_ref() else {
                continue;
            };
            let scope = published_assumption_scope(&declarations, &proof);
            assert!(
                run_carcara_trust_free(carcara, label, &scope, &proof),
                "{label}: the lifted derivation must be verified by Carcara without \
                 allowed trust"
            );
        }
    }
}

/// LOCK-STEP regression: the SIGNED duality `(bvsge a b) = (not (bvslt a b))` is
/// just as TRUE as the unsigned one, and AY decides it, but Carcara's
/// pseudo-Boolean rules for signed comparisons carry an extra negative-weight
/// sign summand — a DIFFERENT derivation this printer does not emit. The leaf
/// table must therefore decline it, leaving an honest `hole` that keeps the
/// document structurally checkable, rather than a step named after an inference
/// the printed text does not license.
#[test]
#[timeout(120_000)]
fn test_signed_compare_duality_remains_an_honest_hole() {
    let label = "signed_compare_duality_honest_hole";
    let declarations = "(declare-const lhs (_ BitVec 32))\n\
                        (declare-const rhs (_ BitVec 32))\n";
    let problem = format!(
        "(set-logic QF_BV)\n\
         {declarations}\
         (assert (not (= (ite (bvsge lhs rhs) (_ bv1 1) (_ bv0 1)) \
         (ite (not (bvslt lhs rhs)) (_ bv1 1) (_ bv0 1)))))\n\
         (check-sat)\n"
    );
    let proof = solve_unsat_and_get_proof(&problem, label);
    assert!(
        !proof.contains(":rule pbblast_"),
        "{label}: the unsigned lowering must not fire on a signed comparison:\n{proof}"
    );
    assert!(
        proof.contains(":rule hole"),
        "{label}: the uncovered identity must stay an honest hole:\n{proof}"
    );
    let Some(carcara) = find_carcara() else {
        return;
    };
    let scope = published_assumption_scope(declarations, &proof);
    assert!(
        run_carcara(&carcara, label, &scope, &proof),
        "{label}: an honest hole must leave the rest of the document checkable, \
         never make it invalid"
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
