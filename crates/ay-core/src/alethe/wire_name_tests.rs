// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::proof::TheoryLemmaKind;

#[test]
fn table_is_sorted_and_deduplicated() {
    // `is_checkable_alethe_rule` binary-searches, so an unsorted or
    // duplicated table would silently start answering "not checkable" for
    // real rules and downgrade valid proofs to holey.
    let mut sorted = CHECKABLE_ALETHE_RULES;
    sorted.sort_unstable();
    assert_eq!(CHECKABLE_ALETHE_RULES, sorted, "table must stay sorted");
    let mut seen = std::collections::HashSet::new();
    for name in CHECKABLE_ALETHE_RULES {
        assert!(seen.insert(name), "duplicate rule name in table: {name}");
    }
}

#[test]
fn every_alias_target_is_checkable_and_no_alias_is_dead() {
    for (internal, wire) in WIRE_RULE_ALIASES {
        // An alias whose target the checker does not implement would turn
        // an honest `hole` into an unknown rule name for nothing.
        assert!(
            is_checkable_alethe_rule(wire),
            "alias target {wire} must be in the checkable table"
        );
        // An alias whose source is already checkable never fires (the
        // pass-through arm wins) and is silently misleading.
        assert!(
            !is_checkable_alethe_rule(internal),
            "alias source {internal} is already checkable; the alias is dead"
        );
        assert_eq!(wire_rule_name(internal), wire);
        assert_ne!(
            wire_rule_name(internal),
            UNPROVED_STEP_RULE,
            "{internal} must reach its checked spelling, not the hole"
        );
    }
}

#[test]
fn hole_is_itself_checkable() {
    // The fallback must be a rule the checker implements, or the mapping
    // would turn one invalid proof into another.
    assert!(is_checkable_alethe_rule(UNPROVED_STEP_RULE));
    assert_eq!(wire_rule_name(UNPROVED_STEP_RULE), UNPROVED_STEP_RULE);
}

#[test]
fn real_rules_pass_through_unchanged() {
    for name in [
        "resolution",
        "th_resolution",
        "eq_congruent",
        "eq_transitive",
        "la_generic",
        "arrays_ext",
        "arrays_row",
        "arrays_idx",
        "distinct_elim",
        "cong",
        "subproof",
        "drup",
        "string_decompose",
    ] {
        assert_eq!(wire_rule_name(name), name, "{name} must not be rewritten");
    }
}

#[test]
fn every_name_the_checker_rejects_becomes_hole() {
    // Measured against carcara 1.1.0 [git main 9a352ee]: each of these
    // names produces `unknown rule` and makes the whole document invalid.
    for name in [
        "trust",
        "dt_project",
        "dt_enum_pigeonhole",
        "all_simplify",
        "arith_simplify",
        "array_ext_diff_intro",
        "bool_tautology",
        "bv_bitblast",
        "equiv",
        "extensionality",
        "fp_classification",
        "fp_rm_domain",
        "fp_rounding_mode_domain",
        "fp_to_bv",
        "ite",
        "ite_same",
        "lra_farkas",
        "nia_positivstellensatz",
        "not_false",
        "not_true",
        "nra_interval_unsat",
        "nra_positivstellensatz",
        "nra_univariate_unsat",
        "read_over_write_chain",
        "read_over_write_neg",
        "read_over_write_pos",
        "regex_intersect_empty",
        "store_permutation",
        "string_code_inj",
        "string_ground_eval",
        "string_length",
        "string_length_lemma",
        "eq_mp",
    ] {
        assert!(
            !is_checkable_alethe_rule(name),
            "{name} must not be in the checkable table"
        );
        assert_eq!(
            wire_rule_name(name),
            UNPROVED_STEP_RULE,
            "{name} must render as an honest hole, never as an unknown rule"
        );
    }
}

#[test]
fn recognized_semantic_placeholders_become_the_canonical_hole() {
    for name in ["hole", "lia_generic"] {
        assert!(
            is_checkable_alethe_rule(name),
            "{name} remains part of the checker dispatch vocabulary"
        );
        assert_eq!(wire_rule_name(name), UNPROVED_STEP_RULE);
    }
}

#[test]
fn premise_or_arg_required_table_is_sorted_and_deduped() {
    // `alethe_rule_requires_premises_or_args` binary-searches it; an
    // out-of-order entry silently stops matching and the guard goes quiet.
    for pair in PREMISE_OR_ARG_REQUIRED_ALETHE_RULES.windows(2) {
        assert!(
            pair[0] < pair[1],
            "{} must sort strictly before {}",
            pair[0],
            pair[1]
        );
    }
    for name in PREMISE_OR_ARG_REQUIRED_ALETHE_RULES {
        assert!(
            alethe_rule_requires_premises_or_args(name),
            "{name} is in the table but does not look up"
        );
    }
}

/// The trap this guard exists for: a name the checker DOES implement, and
/// which `is_checkable_alethe_rule` therefore waves through, that no bare
/// step can ever be an instance of.
#[test]
fn checkable_by_name_is_not_backable_by_a_bare_step() {
    // Measured on carcara 1.1.0 [git master 9a352ee]. Left column: the
    // rule. Right: what it demands before it looks at the clause.
    for (name, demand) in [
        ("string_decompose", "1 premise + 1 arg"),
        ("string_length_pos", "1 arg"),
        ("string_length_non_empty", "1 premise"),
        ("re_inter", "2 premises"),
        ("concat_eq", "1 premise + 1 arg"),
        ("concat_unify", "2 premises + 1 arg"),
        ("concat_conflict", "1 premise + 1 arg"),
        ("re_concat_unfold_pos", "1 premise"),
    ] {
        assert!(
            is_checkable_alethe_rule(name),
            "{name} should still be a rule the checker knows"
        );
        assert!(
            alethe_rule_requires_premises_or_args(name),
            "{name} needs {demand}; a bare step cannot back it"
        );
    }
}

/// The rules a bare theory-lemma step legitimately reaches must NOT be
/// demoted — the guard has to stay a scalpel, not a blanket.
#[test]
fn rules_a_bare_step_can_back_are_left_alone() {
    for name in [
        UNPROVED_STEP_RULE,
        "eq_transitive",
        "eq_reflexive",
        "eq_congruent",
        "eq_congruent_pred",
        "arrays_idx",
        "true",
        "false",
        // Deliberately absent: `la_generic`'s argument count is computed from
        // the conclusion, and the printer either supplies `:args` or refuses
        // the step outright. Listing it would mute that fail-loud.
        "la_generic",
    ] {
        assert!(
            !alethe_rule_requires_premises_or_args(name),
            "{name} must not be demoted"
        );
    }
}

/// The internal-only theory-rule wire-mapping audit, locked down.
///
/// The pre-existing candidates were tested as [`WIRE_RULE_ALIASES`]
/// entries against the pinned checker and failed the admissibility bar.
/// The finite-array schemas have no standard Alethe counterpart and have
/// not been assigned a lookalike rule. Every entry must therefore stay an
/// honest hole unless an exact external derivation is implemented and
/// measured. A future speculative mapping trips this test.
#[test]
fn audited_internal_theory_kinds_stay_honest_holes() {
    for internal in [
        "string_length",
        "string_length_lemma",
        "string_code_inj",
        "string_ground_eval",
        "string_containment_identity",
        "string_concat_cancellation",
        "string_ground_factor_conflict",
        "regex_intersect_empty",
        "regex_length_lower_bound",
        "lia_mod_range",
        "nra_interval_unsat",
        "nra_univariate_unsat",
        "array_finite_extensionality",
        "array_finite_select_expansion",
        "quantifier_negated_exists_dual",
    ] {
        let wire = wire_rule_name(internal);
        assert_eq!(
            wire, UNPROVED_STEP_RULE,
            "{internal} has no admissible checker counterpart; see the \
             WIRE_RULE_ALIASES admissibility bar before mapping it"
        );
        assert!(
            !alethe_rule_requires_premises_or_args(wire),
            "the hole rendering must itself be backable by a bare step"
        );
    }
}

#[test]
fn wire_rendering_preserves_internal_identity_and_exposes_holes() {
    // The soundness gates (terminal-trust, quality metrics, dedup keys)
    // match on the INTERNAL name; only the wire name changes.
    assert_eq!(AletheRule::Trust.name(), "trust");
    assert_eq!(AletheRule::Trust.wire_name(), "hole");
    assert_eq!(TheoryLemmaKind::Generic.alethe_rule(), "trust");
    assert_eq!(TheoryLemmaKind::Generic.alethe_wire_rule(), "hole");
    assert!(TheoryLemmaKind::Generic.is_trust());

    // Quantifier negation is validated by AY's native strict checker, but the
    // pinned external calculus has no exact spelling for it.
    assert_eq!(AletheRule::QntNegExists.name(), "qnt_neg_exists");
    assert_eq!(AletheRule::QntNegExists.wire_name(), "hole");

    // The native theory-lemma bridge is independently strict-checked too; the
    // external calculus likewise has no exact rule for this implication.
    assert_eq!(
        TheoryLemmaKind::QuantifierNegatedExistsDual.alethe_rule(),
        "quantifier_negated_exists_dual"
    );
    assert_eq!(
        TheoryLemmaKind::QuantifierNegatedExistsDual.alethe_wire_rule(),
        "hole"
    );

    // Datatype distinctness keeps its INTERNAL name. The installed
    // external checker does not recognize the candidate `dt_clash`
    // spelling, so the wire format must disclose the gap as a hole.
    assert_eq!(
        TheoryLemmaKind::DatatypeDistinct.alethe_rule(),
        "dt_distinct"
    );
    assert_eq!(TheoryLemmaKind::DatatypeDistinct.alethe_wire_rule(), "hole");
    assert!(!is_checkable_alethe_rule("dt_distinct"));

    // Finite-enum exhaustiveness is checked only by AY's native strict
    // checker. The pinned external Alethe calculus has no equivalent rule,
    // so the wire format must disclose the gap as a hole.
    assert_eq!(
        TheoryLemmaKind::DatatypeEnumPigeonhole.alethe_rule(),
        "dt_enum_pigeonhole"
    );
    assert_eq!(
        TheoryLemmaKind::DatatypeEnumPigeonhole.alethe_wire_rule(),
        "hole"
    );
    assert!(!is_checkable_alethe_rule("dt_enum_pigeonhole"));

    // Complete finite-array schemas are checked natively. There is no
    // standard rule with the same conclusion in the pinned external
    // calculus, so exporting either one must expose an honest hole.
    assert_eq!(
        TheoryLemmaKind::ArrayFiniteExtensionality.alethe_rule(),
        "array_finite_extensionality"
    );
    assert_eq!(
        TheoryLemmaKind::ArrayFiniteExtensionality.alethe_wire_rule(),
        "hole"
    );
    assert_eq!(
        TheoryLemmaKind::ArrayFiniteSelectExpansion.alethe_rule(),
        "array_finite_select_expansion"
    );
    assert_eq!(
        TheoryLemmaKind::ArrayFiniteSelectExpansion.alethe_wire_rule(),
        "hole"
    );

    // A theory lemma that DOES have a real Alethe rule keeps it.
    assert_eq!(TheoryLemmaKind::LraFarkas.alethe_wire_rule(), "la_generic");
    assert_eq!(TheoryLemmaKind::LiaGeneric.alethe_wire_rule(), "hole");
}

/// No name in the checkable vocabulary may be one the pinned checker rejects.
///
/// This is the invariant `is_checkable_alethe_rule` promises, stated as a test
/// rather than left to the next person to rediscover. `dt_clash` violated it:
/// probed directly against `carcara 1.1.0 [git master 9a352ee]` it answers
/// `unknown rule` and the whole document comes back `invalid`, which is the
/// one outcome the predicate exists to rule out.
///
/// The list cannot be probed from a unit test — that needs the installed
/// binary, and `ay-proof/tests/wire_rule_coverage.rs` owns that lane. What is
/// pinned here is the measured conclusion, so re-adding the name is a test
/// failure rather than a silent regression.
#[test]
fn the_pinned_checker_implements_no_datatype_rules() {
    for name in ["dt_clash", "dt_distinct", "dt_split", "dt_cons_eq"] {
        assert!(
            !is_checkable_alethe_rule(name),
            "`{name}` is a datatype rule; the pinned carcara implements none of \
             them, and claiming it is checkable turns a `holey` proof into an \
             `invalid` document"
        );
    }
}
