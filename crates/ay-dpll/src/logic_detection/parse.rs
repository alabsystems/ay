// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::LogicCategory;

/// Recognized combined logics whose component theories AY has but for which it
/// lacks a sound combined decision procedure. They are accepted at `set-logic`
/// but must NOT be routed through content detection: they stay `Other` so
/// `check_sat` returns a sound `unknown`. (#combined-bv-arith)
pub(crate) const FAIL_CLOSED_COMBINED: [&str; 4] =
    ["QF_BVLRA", "QF_AUFBVLIA", "QF_UFBVLIA", "QF_AUFBVLIRA"];

/// Whether z3 5.0.0 silently ACCEPTS `s` as a `set-logic` token (solve, exit 0)
/// rather than emitting `unsupported` + `; ignoring unsupported logic ...`.
///
/// z3's recognizer is STRUCTURAL/substring, not a whitelist — reverse-engineered
/// and pinned by an adversarial sweep against z3 5.0.0. It is
/// case-sensitive. Accept iff `s` is one of a small exact set, OR contains any
/// recognized theory-fragment substring, OR starts with `A` / `QF_A`.
///
/// AY accepts the same frontier so it matches z3's accept-vs-`unsupported`
/// output. Note: for AY this only governs the OUTPUT/exit shape and whether the
/// token is stored — an accepted-but-unmapped token still routes through the
/// same content detection as the unset case, so no verdict depends on this
/// predicate diverging from z3 on an unmeasured token.
pub(crate) fn is_z3_recognized_logic(s: &str) -> bool {
    const EXACT: [&str; 6] = ["ALL", "HORN", "QF_FD", "FP", "QF_FP", "QF_S"];
    if EXACT.contains(&s) {
        return true;
    }
    const SUBSTR: [&str; 12] = [
        "UF", "BV", "DT", "FP", "LIA", "LRA", "LIRA", "NIA", "NRA", "NIRA", "IDL", "RDL",
    ];
    if SUBSTR.iter().any(|needle| s.contains(needle)) {
        return true;
    }
    s.starts_with('A') || s.starts_with("QF_A")
}

/// Whether a STORED declared logic token should route through the same content
/// detection as `None`/`ALL` (i.e. it is an accepted-but-unmapped token). The
/// fail-closed combined logics are excluded: they must keep hitting the
/// `LogicCategory::Other` dispatch arm and answer a sound `unknown`.
pub(crate) fn declared_logic_routes_as_all(s: &str) -> bool {
    matches!(LogicCategory::from_logic(s), LogicCategory::Other)
        && !FAIL_CLOSED_COMBINED.contains(&s)
}

impl LogicCategory {
    /// Parse a logic string from set-logic command into a LogicCategory.
    pub(crate) fn from_logic(logic: &str) -> Self {
        match logic {
            // Pure propositional
            "QF_UF" => Self::QfUf,
            // SMT-LIB "ALL": accept and fall back to default solver selection (QF_UF).
            "ALL" => Self::QfUf,
            "QF_BOOL" | "BOOL" => Self::Propositional,
            // Arrays
            "QF_AX" => Self::QfAx,
            // Linear real arithmetic logics
            "QF_LRA" | "QF_RDL" => Self::QfLra,
            // Linear integer arithmetic logics
            "QF_LIA" | "QF_IDL" => Self::QfLia,
            // Non-linear arithmetic logics
            "QF_NIA" => Self::QfNia,
            "QF_NRA" => Self::QfNra,
            "QF_NIRA" => Self::QfNira,
            // Combined UF + LIA (very common in verification; also accepts QF_UFIDL)
            "QF_UFLIA" | "QF_UFIDL" => Self::QfUflia,
            // Combined UF + LRA
            "QF_UFLRA" => Self::QfUflra,
            // Combined Arrays + UF + LIA (very common in software verification)
            // QF_ALIA is a common alias (Arrays + LIA, UF implied)
            "QF_AUFLIA" | "QF_ALIA" => Self::QfAuflia,
            // Combined Arrays + UF + LRA
            "QF_AUFLRA" => Self::QfAuflra,
            // Mixed integer and real arithmetic
            "QF_LIRA" => Self::QfLira,
            // Combined Arrays + UF + mixed int/real arithmetic
            "QF_AUFLIRA" => Self::QfAuflira,
            // Bitvectors
            "QF_BV" => Self::QfBv,
            // Arrays + Bitvectors (important for Kani workloads)
            "QF_ABV" => Self::QfAbv,
            // UF + Bitvectors
            "QF_UFBV" => Self::QfUfbv,
            // Arrays + UF + Bitvectors (critical for Kani workloads)
            "QF_AUFBV" => Self::QfAufbv,
            // BV + integer arithmetic (internal, from infer_logic #5503)
            "_BV_LIA" => Self::QfBvLia,
            // BV + Int without conversion functions (internal, from infer_logic #5356)
            "_BV_LIA_INDEP" => Self::QfBvLiaIndep,
            // String + BV combined reasoning (internal, conservative #8333).
            // Reuse the BV/LIA bridge category: it only returns UNSAT from
            // sound derived constraints and otherwise returns Unknown.
            "_STRING_BV" => Self::QfBvLia,
            // Floating-point
            "QF_FP" => Self::QfFp,
            "QF_BVFP" => Self::QfBvfp,
            "QF_ABVFP" | "QF_AFPBV" => Self::QfAbvfp,
            // Strings
            "QF_S" => Self::QfS,
            "QF_SLIA" => Self::QfSlia,
            "QF_SNIA" => Self::QfSnia,
            // Generic sequences
            "QF_SEQ" => Self::QfSeq,
            "QF_SEQBV" => Self::QfSeqBv,
            "QF_SEQLIA" => Self::QfSeqlia,
            // Finite sets (card + subset over Array(T->Bool) membership carrier)
            "QF_SET" | "QF_FS" => Self::QfSet,
            "QF_SETLIA" | "QF_FSLIA" => Self::QfSetlia,
            // Multisets (count + subset over Array(T->Int) count carrier)
            "QF_MULTISET" | "QF_MS" => Self::QfMultiset,
            "QF_MSLIA" | "QF_MULTISETLIA" => Self::QfMslia,
            // Finite maps (get/dom + subset over value Array(K->V) + domain
            // Array(K->Bool) carriers)
            "QF_MAP" | "QF_FM" => Self::QfMap,
            "QF_MAPLIA" | "QF_FMLIA" => Self::QfMaplia,
            // Datatypes
            "QF_DT" => Self::QfDt,
            // Internal: Combined DT + arithmetic (used by ALL logic auto-detection)
            "_DT_AUFLIA" => Self::DtAuflia,
            "_DT_AUFLRA" => Self::DtAuflra,
            "_DT_UFBV" => Self::DtUfbv,
            "_DT_AUFBV" => Self::DtAufbv,
            "_DT_AUFLIRA" => Self::DtAuflira,
            "_DT_AX" => Self::DtAx,
            // QF non-linear + UF/Arrays: preserve UF information (#5984).
            // Without EUF congruence closure, NIA/NRA solvers can assign
            // inconsistent values to UF function applications (e.g., (f x)=1
            // and (f y)=2 when x=y), producing unsound SAT results.
            "QF_UFNIA" | "QF_AUFNIA" => Self::QfUfnia,
            "QF_UFNRA" | "QF_AUFNRA" => Self::QfUfnra,
            "QF_UFNIRA" | "QF_AUFNIRA" => Self::QfUfnira,
            // QF FP + LRA: route to FP solver (LRA constraints handled via combined path)
            "QF_FPLRA" => Self::QfFp,
            // Quantified logics (use E-matching + CEGQI)
            "LIA" => Self::Lia,
            "LRA" => Self::Lra,
            "NIA" => Self::Nia,
            "NRA" => Self::Nra,
            "UF" => Self::Uf,
            "UFLIA" => Self::Uflia,
            "UFLRA" => Self::Uflra,
            "AUFLIA" => Self::Auflia,
            "AUFLRA" => Self::Auflra,
            "LIRA" => Self::Lira,
            "NIRA" => Self::Nira,
            "AUFLIRA" => Self::Auflira,
            // Quantified NIA/NRA/NIRA + UF/Arrays: preserve UF information (#5984).
            // Returns Unknown (quantified non-linear not yet implemented) but the
            // logic is recognized rather than returning UnsupportedLogic error.
            "UFNIA" | "AUFNIA" => Self::Ufnia,
            "UFNRA" | "AUFNRA" => Self::Ufnra,
            "UFNIRA" | "AUFNIRA" => Self::Ufnira,
            // Quantified arrays + linear arithmetic
            "ALIA" => Self::Auflia,
            "ALRA" => Self::Auflra,
            "ALIRA" => Self::Auflira,
            // Quantified bitvectors: route to QF solver (finite domain expansion)
            "BV" => Self::QfBv,
            "ABV" => Self::QfAbv,
            "UFBV" => Self::QfUfbv,
            "AUFBV" => Self::QfAufbv,
            // Quantified datatype logics (#7150: ~9 SMT-COMP tracks)
            // Quantifier preprocessing strips quantifiers before theory dispatch,
            // so these route to the same DT-combined solvers as QF_ variants.
            "UFDT" | "DT" => Self::Ufdt,
            "UFDTLIA" | "DTLIA" => Self::Ufdtlia,
            "UFDTLRA" | "DTLRA" => Self::Ufdtlra,
            "UFDTLIRA" | "DTLIRA" => Self::Ufdtlira,
            "UFDTNIA" => Self::Ufdtnia,
            "UFDTNRA" => Self::Ufdtnra,
            "UFDTNIRA" => Self::Ufdtnira,
            "AUFDT" | "ADT" => Self::Aufdt,
            "AUFDTLIA" => Self::Aufdtlia,
            "AUFDTLIRA" => Self::Aufdtlira,
            // A-prefix non-linear DT: route to UF+DT+NL (arrays handled via UF)
            "AUFDTNIA" => Self::Ufdtnia,
            "AUFDTNRA" => Self::Ufdtnra,
            "AUFDTNIRA" => Self::Ufdtnira,
            "AUFDTLRA" => Self::Ufdtlra,
            // QF_ variants of DT logics: route to existing QF_DT / DtAuf* categories
            "QF_UFDT" => Self::QfDt,
            "QF_UFDTLIA" | "QF_DTLIA" => Self::DtAuflia,
            "QF_UFDTLRA" | "QF_DTLRA" => Self::DtAuflra,
            "QF_UFDTLIRA" | "QF_DTLIRA" => Self::DtAuflira,
            // Default to unsupported for unknown logics
            _ => Self::Other,
        }
    }
}
