// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::features::StaticFeatures;

#[test]
fn logic_category_from_logic_recognizes_common_logics() {
    assert_eq!(LogicCategory::from_logic("QF_UF"), LogicCategory::QfUf);
    assert_eq!(LogicCategory::from_logic("ALL"), LogicCategory::QfUf);
    assert_eq!(
        LogicCategory::from_logic("BOOL"),
        LogicCategory::Propositional
    );
    assert_eq!(LogicCategory::from_logic("QF_BV"), LogicCategory::QfBv);
    assert_eq!(LogicCategory::from_logic("QF_DT"), LogicCategory::QfDt);
    assert_eq!(
        LogicCategory::from_logic("UNKNOWN_LOGIC"),
        LogicCategory::Other
    );
}

/// FP logic recognition (#4127).
#[test]
fn fp_logics_map_to_fp_categories() {
    assert_eq!(LogicCategory::from_logic("QF_FP"), LogicCategory::QfFp);
    assert_eq!(LogicCategory::from_logic("QF_BVFP"), LogicCategory::QfBvfp);
    assert_eq!(
        LogicCategory::from_logic("QF_ABVFP"),
        LogicCategory::QfAbvfp
    );
    assert_eq!(
        LogicCategory::from_logic("QF_AFPBV"),
        LogicCategory::QfAbvfp
    );
}

/// String logic recognition for Phase A of #3294.
#[test]
fn string_logics_map_to_string_categories() {
    assert_eq!(LogicCategory::from_logic("QF_S"), LogicCategory::QfS);
    assert_eq!(LogicCategory::from_logic("QF_SLIA"), LogicCategory::QfSlia);
    assert_eq!(LogicCategory::from_logic("QF_SNIA"), LogicCategory::QfSnia);
}

#[test]
fn qf_seqbv_logic_recognized() {
    assert_eq!(
        LogicCategory::from_logic("QF_SEQBV"),
        LogicCategory::QfSeqBv
    );
}

/// with_datatypes() upgrades LIRA-family logics to DtAuflira (#5402).
#[test]
fn test_with_datatypes_lira_upgrade() {
    assert_eq!(
        LogicCategory::QfLira.with_datatypes(),
        LogicCategory::DtAuflira
    );
    assert_eq!(
        LogicCategory::QfAuflira.with_datatypes(),
        LogicCategory::DtAuflira
    );
    // DtAuflira is idempotent
    assert_eq!(
        LogicCategory::DtAuflira.with_datatypes(),
        LogicCategory::DtAuflira
    );
}

#[test]
fn test_with_datatypes_propositional_upgrade() {
    assert_eq!(
        LogicCategory::Propositional.with_datatypes(),
        LogicCategory::QfDt
    );
}

/// with_datatypes() returns Other for unsupported DT combinations (#5430).
#[test]
fn test_with_datatypes_unsupported_returns_other() {
    // NIA + DT is not supported — must not silently drop DT axioms.
    assert_eq!(LogicCategory::QfNia.with_datatypes(), LogicCategory::Other);
    assert_eq!(LogicCategory::QfNra.with_datatypes(), LogicCategory::Other);
    assert_eq!(LogicCategory::QfNira.with_datatypes(), LogicCategory::Other);
    assert_eq!(
        LogicCategory::QfAbvfp.with_datatypes(),
        LogicCategory::Other
    );
    // String + DT is not supported.
    assert_eq!(LogicCategory::QfS.with_datatypes(), LogicCategory::Other);
    assert_eq!(LogicCategory::QfSlia.with_datatypes(), LogicCategory::Other);
}

/// _BV_LIA internal logic string parses to QfBvLia (#5503).
#[test]
fn test_bv_lia_logic_parsing() {
    assert_eq!(LogicCategory::from_logic("_BV_LIA"), LogicCategory::QfBvLia);
}

/// _STRING_BV internal logic string reuses the conservative BV/LIA bridge.
#[test]
fn test_string_bv_logic_parsing() {
    assert_eq!(
        LogicCategory::from_logic("_STRING_BV"),
        LogicCategory::QfBvLia
    );
}

/// QfBvLia + datatypes returns Other (unsupported combination #5503).
#[test]
fn test_bv_lia_with_datatypes_returns_other() {
    assert_eq!(
        LogicCategory::QfBvLia.with_datatypes(),
        LogicCategory::Other
    );
}

/// Quantified mixed int/real logics are recognized (#5888).
#[test]
fn quantified_lira_logics_recognized() {
    assert_eq!(LogicCategory::from_logic("LIRA"), LogicCategory::Lira);
    assert_eq!(LogicCategory::from_logic("NIRA"), LogicCategory::Nira);
    assert_eq!(LogicCategory::from_logic("AUFLIRA"), LogicCategory::Auflira);
}

/// Quantified LIRA + datatypes routes to DtAuflira (#5888).
#[test]
fn quantified_lira_with_datatypes() {
    assert_eq!(
        LogicCategory::Lira.with_datatypes(),
        LogicCategory::DtAuflira
    );
    assert_eq!(
        LogicCategory::Nira.with_datatypes(),
        LogicCategory::DtAuflira
    );
    assert_eq!(
        LogicCategory::Auflira.with_datatypes(),
        LogicCategory::DtAuflira
    );
}

/// UF + non-linear logics preserve UF information (#5984).
#[test]
fn nonlinear_uf_array_logics_preserve_uf() {
    // QF non-linear + UF/Arrays → dedicated UF+NIA/NRA categories
    assert_eq!(
        LogicCategory::from_logic("QF_UFNIA"),
        LogicCategory::QfUfnia
    );
    assert_eq!(
        LogicCategory::from_logic("QF_UFNRA"),
        LogicCategory::QfUfnra
    );
    assert_eq!(
        LogicCategory::from_logic("QF_UFNIRA"),
        LogicCategory::QfUfnira
    );
    assert_eq!(
        LogicCategory::from_logic("QF_AUFNIA"),
        LogicCategory::QfUfnia
    );
    assert_eq!(
        LogicCategory::from_logic("QF_AUFNRA"),
        LogicCategory::QfUfnra
    );
    assert_eq!(
        LogicCategory::from_logic("QF_AUFNIRA"),
        LogicCategory::QfUfnira
    );
}

#[test]
fn quantified_nonlinear_uf_logics_preserve_uf() {
    // Quantified NIA/NRA + UF/Arrays → UF-aware categories (#5984)
    assert_eq!(LogicCategory::from_logic("UFNIA"), LogicCategory::Ufnia);
    assert_eq!(LogicCategory::from_logic("AUFNIA"), LogicCategory::Ufnia);
    assert_eq!(LogicCategory::from_logic("UFNRA"), LogicCategory::Ufnra);
    assert_eq!(LogicCategory::from_logic("AUFNRA"), LogicCategory::Ufnra);
    assert_eq!(LogicCategory::from_logic("UFNIRA"), LogicCategory::Ufnira);
    // AUFNIRA: the model-checker/TLAPS consumer logic
    assert_eq!(LogicCategory::from_logic("AUFNIRA"), LogicCategory::Ufnira);
}

#[test]
fn quantified_array_linear_logics_recognized() {
    assert_eq!(LogicCategory::from_logic("ALIA"), LogicCategory::Auflia);
    assert_eq!(LogicCategory::from_logic("ALRA"), LogicCategory::Auflra);
    assert_eq!(LogicCategory::from_logic("ALIRA"), LogicCategory::Auflira);
}

#[test]
fn quantified_bv_logics_recognized() {
    assert_eq!(LogicCategory::from_logic("BV"), LogicCategory::QfBv);
    assert_eq!(LogicCategory::from_logic("ABV"), LogicCategory::QfAbv);
    assert_eq!(LogicCategory::from_logic("UFBV"), LogicCategory::QfUfbv);
    assert_eq!(LogicCategory::from_logic("AUFBV"), LogicCategory::QfAufbv);
}

#[test]
fn fp_lra_logic_recognized() {
    assert_eq!(LogicCategory::from_logic("QF_FPLRA"), LogicCategory::QfFp);
}

// ── with_nonlinear() tests (#6086) ──────────────────────────────

fn nl_int() -> StaticFeatures {
    StaticFeatures {
        has_nonlinear_int: true,
        ..Default::default()
    }
}

fn nl_real() -> StaticFeatures {
    StaticFeatures {
        has_nonlinear_real: true,
        ..Default::default()
    }
}

fn nl_both() -> StaticFeatures {
    StaticFeatures {
        has_nonlinear_int: true,
        has_nonlinear_real: true,
        ..Default::default()
    }
}

fn linear() -> StaticFeatures {
    StaticFeatures::default()
}

#[test]
fn with_nonlinear_noop_when_linear() {
    // Linear features → no upgrade for any category
    assert_eq!(
        LogicCategory::QfLia.with_nonlinear(&linear()),
        LogicCategory::QfLia
    );
    assert_eq!(
        LogicCategory::QfLra.with_nonlinear(&linear()),
        LogicCategory::QfLra
    );
    assert_eq!(
        LogicCategory::QfLira.with_nonlinear(&linear()),
        LogicCategory::QfLira
    );
    assert_eq!(
        LogicCategory::QfUflia.with_nonlinear(&linear()),
        LogicCategory::QfUflia
    );
    assert_eq!(
        LogicCategory::Lia.with_nonlinear(&linear()),
        LogicCategory::Lia
    );
}

#[test]
fn with_nonlinear_noop_for_already_nonlinear() {
    // Already nonlinear categories are unchanged
    assert_eq!(
        LogicCategory::QfNia.with_nonlinear(&nl_int()),
        LogicCategory::QfNia
    );
    assert_eq!(
        LogicCategory::QfNra.with_nonlinear(&nl_real()),
        LogicCategory::QfNra
    );
    assert_eq!(
        LogicCategory::QfNira.with_nonlinear(&nl_both()),
        LogicCategory::QfNira
    );
    assert_eq!(
        LogicCategory::QfSnia.with_nonlinear(&nl_int()),
        LogicCategory::QfSnia
    );
    assert_eq!(
        LogicCategory::Nia.with_nonlinear(&nl_int()),
        LogicCategory::Nia
    );
    assert_eq!(
        LogicCategory::Nra.with_nonlinear(&nl_real()),
        LogicCategory::Nra
    );
    assert_eq!(
        LogicCategory::Nira.with_nonlinear(&nl_both()),
        LogicCategory::Nira
    );
    assert_eq!(
        LogicCategory::Ufnia.with_nonlinear(&nl_int()),
        LogicCategory::Ufnia
    );
    assert_eq!(
        LogicCategory::Ufnra.with_nonlinear(&nl_real()),
        LogicCategory::Ufnra
    );
    assert_eq!(
        LogicCategory::Ufnira.with_nonlinear(&nl_both()),
        LogicCategory::Ufnira
    );
    assert_eq!(
        LogicCategory::QfUfnia.with_nonlinear(&nl_int()),
        LogicCategory::QfUfnia
    );
    assert_eq!(
        LogicCategory::QfUfnra.with_nonlinear(&nl_real()),
        LogicCategory::QfUfnra
    );
    assert_eq!(
        LogicCategory::QfUfnira.with_nonlinear(&nl_both()),
        LogicCategory::QfUfnira
    );
}

#[test]
fn with_nonlinear_qf_linear_to_nonlinear() {
    assert_eq!(
        LogicCategory::QfLia.with_nonlinear(&nl_int()),
        LogicCategory::QfNia
    );
    assert_eq!(
        LogicCategory::QfLra.with_nonlinear(&nl_real()),
        LogicCategory::QfNra
    );
    assert_eq!(
        LogicCategory::QfLira.with_nonlinear(&nl_int()),
        LogicCategory::QfNira
    );
    assert_eq!(
        LogicCategory::QfLira.with_nonlinear(&nl_real()),
        LogicCategory::QfNira
    );
    assert_eq!(
        LogicCategory::QfLira.with_nonlinear(&nl_both()),
        LogicCategory::QfNira
    );
}

#[test]
fn with_nonlinear_qf_uf_linear_to_uf_nonlinear() {
    assert_eq!(
        LogicCategory::QfUflia.with_nonlinear(&nl_int()),
        LogicCategory::QfUfnia
    );
    assert_eq!(
        LogicCategory::QfUflra.with_nonlinear(&nl_real()),
        LogicCategory::QfUfnra
    );
}

#[test]
fn with_nonlinear_qf_auf_linear_to_uf_nonlinear() {
    // AUF + nonlinear → UfN* (arrays handled via UF)
    assert_eq!(
        LogicCategory::QfAuflia.with_nonlinear(&nl_int()),
        LogicCategory::QfUfnia
    );
    assert_eq!(
        LogicCategory::QfAuflra.with_nonlinear(&nl_real()),
        LogicCategory::QfUfnra
    );
    assert_eq!(
        LogicCategory::QfAuflira.with_nonlinear(&nl_int()),
        LogicCategory::QfUfnira
    );
    assert_eq!(
        LogicCategory::QfAuflira.with_nonlinear(&nl_real()),
        LogicCategory::QfUfnira
    );
}

/// DT + nonlinear → Other (no combined DT+NIA/NRA solver; #6088).
#[test]
fn with_nonlinear_dt_to_other() {
    assert_eq!(
        LogicCategory::DtAuflia.with_nonlinear(&nl_int()),
        LogicCategory::Other
    );
    assert_eq!(
        LogicCategory::DtAuflra.with_nonlinear(&nl_real()),
        LogicCategory::Other
    );
    assert_eq!(
        LogicCategory::DtAuflira.with_nonlinear(&nl_int()),
        LogicCategory::Other
    );
    assert_eq!(
        LogicCategory::DtAuflira.with_nonlinear(&nl_real()),
        LogicCategory::Other
    );
    assert_eq!(
        LogicCategory::DtAuflira.with_nonlinear(&nl_both()),
        LogicCategory::Other
    );
}

#[test]
fn with_nonlinear_quantified_linear_to_nonlinear() {
    assert_eq!(
        LogicCategory::Lia.with_nonlinear(&nl_int()),
        LogicCategory::Nia
    );
    assert_eq!(
        LogicCategory::Lra.with_nonlinear(&nl_real()),
        LogicCategory::Nra
    );
    assert_eq!(
        LogicCategory::Lira.with_nonlinear(&nl_int()),
        LogicCategory::Nira
    );
    assert_eq!(
        LogicCategory::Lira.with_nonlinear(&nl_both()),
        LogicCategory::Nira
    );
}

#[test]
fn with_nonlinear_quantified_uf_linear_to_uf_nonlinear() {
    assert_eq!(
        LogicCategory::Uflia.with_nonlinear(&nl_int()),
        LogicCategory::Ufnia
    );
    assert_eq!(
        LogicCategory::Uflra.with_nonlinear(&nl_real()),
        LogicCategory::Ufnra
    );
    assert_eq!(
        LogicCategory::Auflia.with_nonlinear(&nl_int()),
        LogicCategory::Ufnia
    );
    assert_eq!(
        LogicCategory::Auflra.with_nonlinear(&nl_real()),
        LogicCategory::Ufnra
    );
    assert_eq!(
        LogicCategory::Auflira.with_nonlinear(&nl_int()),
        LogicCategory::Ufnira
    );
    assert_eq!(
        LogicCategory::Auflira.with_nonlinear(&nl_real()),
        LogicCategory::Ufnira
    );
}

#[test]
fn with_nonlinear_noop_for_non_arithmetic() {
    // Non-arithmetic logics are unchanged regardless of nonlinear features
    assert_eq!(
        LogicCategory::QfBv.with_nonlinear(&nl_int()),
        LogicCategory::QfBv
    );
    assert_eq!(
        LogicCategory::QfUf.with_nonlinear(&nl_real()),
        LogicCategory::QfUf
    );
    assert_eq!(
        LogicCategory::Propositional.with_nonlinear(&nl_both()),
        LogicCategory::Propositional
    );
    assert_eq!(
        LogicCategory::QfS.with_nonlinear(&nl_int()),
        LogicCategory::QfS
    );
    assert_eq!(
        LogicCategory::QfDt.with_nonlinear(&nl_int()),
        LogicCategory::QfDt
    );
    assert_eq!(
        LogicCategory::Other.with_nonlinear(&nl_both()),
        LogicCategory::Other
    );
}

#[test]
fn with_nonlinear_wrong_sort_noop() {
    // QfLia with nonlinear *real* should not upgrade (no NL int)
    assert_eq!(
        LogicCategory::QfLia.with_nonlinear(&nl_real()),
        LogicCategory::QfLia
    );
    // QfLra with nonlinear *int* should not upgrade (no NL real)
    assert_eq!(
        LogicCategory::QfLra.with_nonlinear(&nl_int()),
        LogicCategory::QfLra
    );
}

#[test]
fn with_nonlinear_slia_to_snia() {
    // QfSlia + nonlinear int → QfSnia (#6088)
    assert_eq!(
        LogicCategory::QfSlia.with_nonlinear(&nl_int()),
        LogicCategory::QfSnia
    );
    // QfSlia + nonlinear real only → no upgrade (no NL int)
    assert_eq!(
        LogicCategory::QfSlia.with_nonlinear(&nl_real()),
        LogicCategory::QfSlia
    );
}

/// Seq + nonlinear Int → Other (no combined Seq+NIA solver).
#[test]
fn with_nonlinear_seq_lia_to_other() {
    assert_eq!(
        LogicCategory::QfSeqlia.with_nonlinear(&nl_int()),
        LogicCategory::Other
    );
    // QfSeqlia with nonlinear real only → no upgrade (Seq+LIA has no reals)
    assert_eq!(
        LogicCategory::QfSeqlia.with_nonlinear(&nl_real()),
        LogicCategory::QfSeqlia
    );
}

/// BV + nonlinear Int → Other (no combined BV+NIA solver; #6088).
#[test]
fn with_nonlinear_bv_lia_to_other() {
    assert_eq!(
        LogicCategory::QfBvLia.with_nonlinear(&nl_int()),
        LogicCategory::Other
    );
    assert_eq!(
        LogicCategory::QfBvLiaIndep.with_nonlinear(&nl_int()),
        LogicCategory::Other
    );
    // BV+LIA with nonlinear real only → no upgrade (no NL int in BV+LIA)
    assert_eq!(
        LogicCategory::QfBvLia.with_nonlinear(&nl_real()),
        LogicCategory::QfBvLia
    );
    assert_eq!(
        LogicCategory::QfBvLiaIndep.with_nonlinear(&nl_real()),
        LogicCategory::QfBvLiaIndep
    );
}

// ── narrow_linear_combo_with_features() tests (#6300) ──────────

fn pure_int() -> StaticFeatures {
    StaticFeatures {
        has_int: true,
        ..Default::default()
    }
}

fn pure_real() -> StaticFeatures {
    StaticFeatures {
        has_real: true,
        ..Default::default()
    }
}

fn mixed_int_real() -> StaticFeatures {
    // Genuinely mixed Int/Real: an Int-sorted variable/UF (`has_int_var`) AND a
    // Real-sorted term. Promotion to the mixed `*LIRA` family requires GENUINE
    // Int-sort evidence, not just an Int-typed numeral (#qf-lra-lit-misroute).
    StaticFeatures {
        has_int: true,
        has_int_var: true,
        has_real: true,
        ..Default::default()
    }
}

/// Real-only formula carrying only integer LITERALS: `has_int` is set (a
/// numeral typed Int by local elaboration) but there is NO genuine Int-sort
/// evidence (`has_int_var` is false). Per SMT-LIB the numerals denote Reals.
fn real_with_int_literals() -> StaticFeatures {
    StaticFeatures {
        has_int: true,
        has_int_var: false,
        has_real: true,
        ..Default::default()
    }
}

fn with_uf() -> StaticFeatures {
    StaticFeatures {
        has_int: true,
        has_uf: true,
        ..Default::default()
    }
}

fn with_arrays() -> StaticFeatures {
    StaticFeatures {
        has_int: true,
        has_arrays: true,
        ..Default::default()
    }
}

#[test]
fn narrow_qf_uflia_to_qf_lia() {
    assert_eq!(
        LogicCategory::QfUflia.narrow_linear_combo_with_features(&pure_int()),
        LogicCategory::QfLia
    );
}

#[test]
fn narrow_qf_auflia_to_qf_lia() {
    assert_eq!(
        LogicCategory::QfAuflia.narrow_linear_combo_with_features(&pure_int()),
        LogicCategory::QfLia
    );
}

#[test]
fn narrow_qf_uflra_to_qf_lra() {
    assert_eq!(
        LogicCategory::QfUflra.narrow_linear_combo_with_features(&pure_real()),
        LogicCategory::QfLra
    );
}

#[test]
fn narrow_qf_auflra_to_qf_lra() {
    assert_eq!(
        LogicCategory::QfAuflra.narrow_linear_combo_with_features(&pure_real()),
        LogicCategory::QfLra
    );
}

#[test]
fn narrow_qf_auflira_to_qf_lira() {
    assert_eq!(
        LogicCategory::QfAuflira.narrow_linear_combo_with_features(&mixed_int_real()),
        LogicCategory::QfLira
    );
}

#[test]
fn narrow_quantified_uflia_to_lia() {
    assert_eq!(
        LogicCategory::Uflia.narrow_linear_combo_with_features(&pure_int()),
        LogicCategory::Lia
    );
}

#[test]
fn narrow_quantified_auflia_to_lia() {
    assert_eq!(
        LogicCategory::Auflia.narrow_linear_combo_with_features(&pure_int()),
        LogicCategory::Lia
    );
}

#[test]
fn narrow_quantified_auflira_to_lira() {
    assert_eq!(
        LogicCategory::Auflira.narrow_linear_combo_with_features(&mixed_int_real()),
        LogicCategory::Lira
    );
}

#[test]
fn narrow_noop_when_uf_present() {
    // Live UF terms → keep combined path
    assert_eq!(
        LogicCategory::QfUflia.narrow_linear_combo_with_features(&with_uf()),
        LogicCategory::QfUflia
    );
}

#[test]
fn narrow_noop_when_arrays_present() {
    // Live array terms → keep combined path
    assert_eq!(
        LogicCategory::QfAuflia.narrow_linear_combo_with_features(&with_arrays()),
        LogicCategory::QfAuflia
    );
}

#[test]
fn narrow_noop_for_pure_arithmetic() {
    // Already pure arithmetic — no narrowing needed
    assert_eq!(
        LogicCategory::QfLia.narrow_linear_combo_with_features(&pure_int()),
        LogicCategory::QfLia
    );
    assert_eq!(
        LogicCategory::QfLra.narrow_linear_combo_with_features(&pure_real()),
        LogicCategory::QfLra
    );
}

#[test]
fn narrow_noop_for_non_arithmetic() {
    // Non-arithmetic logics — no narrowing
    assert_eq!(
        LogicCategory::QfBv.narrow_linear_combo_with_features(&pure_int()),
        LogicCategory::QfBv
    );
    assert_eq!(
        LogicCategory::QfUf.narrow_linear_combo_with_features(&pure_int()),
        LogicCategory::QfUf
    );
}

// --- align_linear_arithmetic_sorts tests (#8969) ---

#[test]
fn align_qf_lra_with_int_to_qf_lia() {
    assert_eq!(
        LogicCategory::QfLra.align_linear_arithmetic_sorts(&pure_int()),
        LogicCategory::QfLia
    );
}

#[test]
fn align_qf_lra_with_mixed_arithmetic_to_qf_lira() {
    assert_eq!(
        LogicCategory::QfLra.align_linear_arithmetic_sorts(&mixed_int_real()),
        LogicCategory::QfLira
    );
}

#[test]
fn align_qf_uflra_with_int_to_qf_uflia() {
    assert_eq!(
        LogicCategory::QfUflra.align_linear_arithmetic_sorts(&pure_int()),
        LogicCategory::QfUflia
    );
}

#[test]
fn align_qf_uflra_with_mixed_arithmetic_to_qf_auflira() {
    assert_eq!(
        LogicCategory::QfUflra.align_linear_arithmetic_sorts(&mixed_int_real()),
        LogicCategory::QfAuflira
    );
}

#[test]
fn align_dt_auflra_with_mixed_arithmetic_to_dt_auflira() {
    assert_eq!(
        LogicCategory::DtAuflra.align_linear_arithmetic_sorts(&mixed_int_real()),
        LogicCategory::DtAuflira
    );
}

// --- #qf-lra-lit-misroute: a declared Real-only logic carrying ONLY integer
// literals (has_int from numerals, but has_int_var=false) must NOT be promoted
// to a mixed *LIRA variant — numerals denote Reals in a Real context, so it
// stays in the LRA family and is solved soundly by the LRA solver.

#[test]
fn align_qf_lra_with_int_literals_stays_qf_lra() {
    assert_eq!(
        LogicCategory::QfLra.align_linear_arithmetic_sorts(&real_with_int_literals()),
        LogicCategory::QfLra
    );
}

#[test]
fn align_qf_uflra_with_int_literals_stays_qf_uflra() {
    assert_eq!(
        LogicCategory::QfUflra.align_linear_arithmetic_sorts(&real_with_int_literals()),
        LogicCategory::QfUflra
    );
}

#[test]
fn align_dt_auflra_with_int_literals_stays_dt_auflra() {
    assert_eq!(
        LogicCategory::DtAuflra.align_linear_arithmetic_sorts(&real_with_int_literals()),
        LogicCategory::DtAuflra
    );
}

#[test]
fn align_lra_with_int_literals_stays_lra() {
    assert_eq!(
        LogicCategory::Lra.align_linear_arithmetic_sorts(&real_with_int_literals()),
        LogicCategory::Lra
    );
}

#[test]
fn align_qf_lira_with_int_literals_only_narrows_to_qf_lra() {
    // A declared QF_LIRA whose only Int evidence is numerals is satisfiability-
    // equivalent to QF_LRA (numerals are Reals); routing to LRA is sound and
    // complete. Genuine mixed Int/Real keeps QF_LIRA (covered above).
    assert_eq!(
        LogicCategory::QfLira.align_linear_arithmetic_sorts(&real_with_int_literals()),
        LogicCategory::QfLra
    );
}

#[test]
fn align_genuine_int_var_with_real_promotes_to_qf_lira() {
    // Sanity: genuine mixed (Int var + Real) still promotes — routing not broken.
    assert_eq!(
        LogicCategory::QfLra.align_linear_arithmetic_sorts(&mixed_int_real()),
        LogicCategory::QfLira
    );
}

// --- widen_with_uf tests (#7442) ---

#[test]
fn widen_qf_lia_to_qf_uflia() {
    assert_eq!(
        LogicCategory::QfLia.widen_with_uf(&with_uf()),
        LogicCategory::QfUflia
    );
}

#[test]
fn widen_qf_lra_to_qf_uflra() {
    let features = StaticFeatures {
        has_real: true,
        has_uf: true,
        ..Default::default()
    };
    assert_eq!(
        LogicCategory::QfLra.widen_with_uf(&features),
        LogicCategory::QfUflra
    );
}

#[test]
fn widen_qf_lira_to_qf_auflira() {
    let features = StaticFeatures {
        has_int: true,
        has_real: true,
        has_uf: true,
        ..Default::default()
    };
    assert_eq!(
        LogicCategory::QfLira.widen_with_uf(&features),
        LogicCategory::QfAuflira
    );
}

#[test]
fn widen_qf_bv_to_qf_ufbv() {
    let features = StaticFeatures {
        has_bv: true,
        has_uf: true,
        ..Default::default()
    };
    assert_eq!(
        LogicCategory::QfBv.widen_with_uf(&features),
        LogicCategory::QfUfbv
    );
}

#[test]
fn widen_quantified_lia_to_uflia() {
    assert_eq!(
        LogicCategory::Lia.widen_with_uf(&with_uf()),
        LogicCategory::Uflia
    );
}

#[test]
fn widen_noop_when_already_has_uf() {
    // Already UF-combined — no widening needed
    assert_eq!(
        LogicCategory::QfUflia.widen_with_uf(&with_uf()),
        LogicCategory::QfUflia
    );
    assert_eq!(
        LogicCategory::QfAuflia.widen_with_uf(&with_uf()),
        LogicCategory::QfAuflia
    );
}

#[test]
fn widen_noop_when_no_uf() {
    // No UF terms — no widening regardless of logic
    assert_eq!(
        LogicCategory::QfLia.widen_with_uf(&pure_int()),
        LogicCategory::QfLia
    );
    assert_eq!(
        LogicCategory::QfLra.widen_with_uf(&pure_real()),
        LogicCategory::QfLra
    );
}

// ── Quantified datatype logic tests (#7150) ─────────────────────

#[test]
fn quantified_dt_logics_parsed() {
    assert_eq!(LogicCategory::from_logic("UFDT"), LogicCategory::Ufdt);
    assert_eq!(LogicCategory::from_logic("DT"), LogicCategory::Ufdt);
    assert_eq!(LogicCategory::from_logic("UFDTLIA"), LogicCategory::Ufdtlia);
    assert_eq!(
        LogicCategory::from_logic("AUFDTLIA"),
        LogicCategory::Aufdtlia
    );
    assert_eq!(LogicCategory::from_logic("UFDTLRA"), LogicCategory::Ufdtlra);
    assert_eq!(
        LogicCategory::from_logic("AUFDTLRA"),
        LogicCategory::Ufdtlra
    );
    assert_eq!(
        LogicCategory::from_logic("UFDTLIRA"),
        LogicCategory::Ufdtlira
    );
    assert_eq!(
        LogicCategory::from_logic("AUFDTLIRA"),
        LogicCategory::Aufdtlira
    );
    assert_eq!(LogicCategory::from_logic("UFDTNIA"), LogicCategory::Ufdtnia);
    assert_eq!(LogicCategory::from_logic("UFDTNRA"), LogicCategory::Ufdtnra);
    assert_eq!(
        LogicCategory::from_logic("UFDTNIRA"),
        LogicCategory::Ufdtnira
    );
    assert_eq!(LogicCategory::from_logic("AUFDT"), LogicCategory::Aufdt);
    assert_eq!(LogicCategory::from_logic("ADT"), LogicCategory::Aufdt);
}

#[test]
fn qf_dt_uf_logics_route_to_existing_qf_categories() {
    // QF_ variants of DT logics route to existing QF_DT / DtAuf* categories
    assert_eq!(LogicCategory::from_logic("QF_UFDT"), LogicCategory::QfDt);
    assert_eq!(
        LogicCategory::from_logic("QF_UFDTLIA"),
        LogicCategory::DtAuflia
    );
    assert_eq!(
        LogicCategory::from_logic("QF_DTLIA"),
        LogicCategory::DtAuflia
    );
    assert_eq!(
        LogicCategory::from_logic("QF_UFDTLRA"),
        LogicCategory::DtAuflra
    );
    assert_eq!(
        LogicCategory::from_logic("QF_UFDTLIRA"),
        LogicCategory::DtAuflira
    );
}

/// QF_ALIA is recognized as an alias for QF_AUFLIA (#7891).
#[test]
fn qf_alia_routes_to_qf_auflia() {
    assert_eq!(
        LogicCategory::from_logic("QF_ALIA"),
        LogicCategory::QfAuflia
    );
}

/// Public Logic enum round-trips for newly added logics (#7891).
#[test]
fn logic_api_new_logics_round_trip() {
    use crate::Logic;

    // QF_ALIA
    let logic: Logic = "QF_ALIA".parse().expect("QF_ALIA should parse");
    assert_eq!(logic.as_str(), "QF_ALIA");

    // QF_UFDT
    let logic: Logic = "QF_UFDT".parse().expect("QF_UFDT should parse");
    assert_eq!(logic.as_str(), "QF_UFDT");

    // UFDT (and DT alias)
    let logic: Logic = "UFDT".parse().expect("UFDT should parse");
    assert_eq!(logic.as_str(), "UFDT");
    let logic: Logic = "DT".parse().expect("DT should parse as UFDT");
    assert_eq!(logic.as_str(), "UFDT");

    // UFDTLIA (and DTLIA alias)
    let logic: Logic = "UFDTLIA".parse().expect("UFDTLIA should parse");
    assert_eq!(logic.as_str(), "UFDTLIA");
    let logic: Logic = "DTLIA".parse().expect("DTLIA should parse as UFDTLIA");
    assert_eq!(logic.as_str(), "UFDTLIA");

    // UFDTNIA
    let logic: Logic = "UFDTNIA".parse().expect("UFDTNIA should parse");
    assert_eq!(logic.as_str(), "UFDTNIA");
}

/// New logics route to correct internal LogicCategory (#7891).
#[test]
fn new_logics_internal_routing() {
    // QF_ALIA -> QfAuflia (arrays + UF + LIA)
    assert_eq!(
        LogicCategory::from_logic("QF_ALIA"),
        LogicCategory::QfAuflia
    );
    // QF_UFDT -> QfDt
    assert_eq!(LogicCategory::from_logic("QF_UFDT"), LogicCategory::QfDt);
    // UFDT -> Ufdt
    assert_eq!(LogicCategory::from_logic("UFDT"), LogicCategory::Ufdt);
    // UFDTLIA -> Ufdtlia
    assert_eq!(LogicCategory::from_logic("UFDTLIA"), LogicCategory::Ufdtlia);
    // UFDTNIA -> Ufdtnia
    assert_eq!(LogicCategory::from_logic("UFDTNIA"), LogicCategory::Ufdtnia);
}

#[test]
fn quantified_dt_idempotent_with_datatypes() {
    // Quantified DT variants are already DT — with_datatypes() is idempotent
    assert_eq!(LogicCategory::Ufdt.with_datatypes(), LogicCategory::Ufdt);
    assert_eq!(
        LogicCategory::Ufdtlia.with_datatypes(),
        LogicCategory::Ufdtlia
    );
    assert_eq!(
        LogicCategory::Ufdtlira.with_datatypes(),
        LogicCategory::Ufdtlira
    );
    assert_eq!(LogicCategory::Aufdt.with_datatypes(), LogicCategory::Aufdt);
    assert_eq!(
        LogicCategory::Aufdtlia.with_datatypes(),
        LogicCategory::Aufdtlia
    );
    assert_eq!(
        LogicCategory::Aufdtlira.with_datatypes(),
        LogicCategory::Aufdtlira
    );
}

#[test]
fn quantified_dt_nonlinear_upgrade() {
    // Linear DT -> nonlinear DT when nonlinear features detected
    assert_eq!(
        LogicCategory::Ufdtlia.with_nonlinear(&nl_int()),
        LogicCategory::Ufdtnia
    );
    assert_eq!(
        LogicCategory::Ufdtlra.with_nonlinear(&nl_real()),
        LogicCategory::Ufdtnra
    );
    assert_eq!(
        LogicCategory::Ufdtlira.with_nonlinear(&nl_int()),
        LogicCategory::Ufdtnira
    );
    assert_eq!(
        LogicCategory::Aufdtlia.with_nonlinear(&nl_int()),
        LogicCategory::Ufdtnia
    );
    assert_eq!(
        LogicCategory::Aufdtlira.with_nonlinear(&nl_both()),
        LogicCategory::Ufdtnira
    );
    // Already nonlinear — noop
    assert_eq!(
        LogicCategory::Ufdtnia.with_nonlinear(&nl_int()),
        LogicCategory::Ufdtnia
    );
    assert_eq!(
        LogicCategory::Ufdtnra.with_nonlinear(&nl_real()),
        LogicCategory::Ufdtnra
    );
    assert_eq!(
        LogicCategory::Ufdtnira.with_nonlinear(&nl_both()),
        LogicCategory::Ufdtnira
    );
}

#[test]
fn quantified_dt_widen_noop() {
    // Quantified DT logics already have UF — widen_with_uf() is noop
    assert_eq!(
        LogicCategory::Ufdt.widen_with_uf(&with_uf()),
        LogicCategory::Ufdt
    );
    assert_eq!(
        LogicCategory::Ufdtlia.widen_with_uf(&with_uf()),
        LogicCategory::Ufdtlia
    );
    assert_eq!(
        LogicCategory::Aufdt.widen_with_uf(&with_uf()),
        LogicCategory::Aufdt
    );
    assert_eq!(
        LogicCategory::Aufdtlira.widen_with_uf(&with_uf()),
        LogicCategory::Aufdtlira
    );
}

#[test]
fn z3_recognizer_truth_table_pins_measured_frontier() {
    // Pins the STRUCTURAL set-logic recognizer to z3 5.0.0's measured
    // accept/`unsupported` frontier. z3 SILENTLY
    // accepts these (solve, exit 0):
    for accept in [
        "ALL",
        "HORN",
        "QF_FD",
        "FP",
        "QF_FP",
        "QF_S", // exact set
        "XLIA",
        "FOOLIA",
        "LIAX",
        "BVFOO",
        "UFO",
        "SUF",
        "A",
        "AX",
        "QF_A",
        "DTX",
        "XDT",
        "LIA2",
        "NIAGARA",
        "QF_LIA ",
        "QF_UFSLIA",
        "QF_SLRA",
        "QF_FPDTLIA",
        "UFBVDT", // substring / A-prefix / QF_A-prefix
        "ZFP",
        "FPX", // z3 5.0.0 recognizes FP as a substring (unlike 4.15.4)
        // the five named probes and their combined siblings:
        "QF_UFLIRA",
        "QF_ANIA",
        "QF_UFFPDTNIRA",
        "AUFBVDTLIA",
        "UFSLIA",
    ] {
        assert!(
            is_z3_recognized_logic(accept),
            "z3 accepts {accept:?} but is_z3_recognized_logic rejected it"
        );
    }
    // z3 IGNORES these (`unsupported` + `; ignoring unsupported logic`, exit 0):
    for reject in [
        "SAT",
        "BOOL",
        "QF_BOOL",
        "CORE",
        "S",
        "FD",
        "QF_FDX",
        "QF_X",
        "QF_",
        "PF",
        "XPF",
        "M",
        "HORNBLOWER",
        "XHORN",
        "qf_lia",
        "Qf_Lia",
        "QF_FOOBAR",
        "NOPE",
    ] {
        assert!(
            !is_z3_recognized_logic(reject),
            "z3 ignores {reject:?} but is_z3_recognized_logic accepted it"
        );
    }
}

#[test]
fn declared_logic_routes_as_all_excludes_fail_closed_and_mapped() {
    // Accepted-but-unmapped tokens route through content detection.
    assert!(declared_logic_routes_as_all("QF_UFLIRA"));
    assert!(declared_logic_routes_as_all("AUFBVDTLIA"));
    assert!(declared_logic_routes_as_all("QF_UFO"));
    // Mapped tokens keep their own routing.
    assert!(!declared_logic_routes_as_all("QF_LIA"));
    assert!(!declared_logic_routes_as_all("ALL"));
    // The fail-closed combined logics stay in the mapped (Other-dispatch) arm.
    for fc in FAIL_CLOSED_COMBINED {
        assert!(
            !declared_logic_routes_as_all(fc),
            "{fc} must NOT route as ALL (keeps sound `unknown` dispatch)"
        );
    }
}
