// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Logic detection and categorization for SMT solver theory selection.
//!
//! This module provides types and functions for detecting and categorizing
//! SMT-LIB logics based on set-logic commands or formula analysis.

mod parse;
mod transforms;

#[cfg(test)]
pub(crate) use parse::FAIL_CLOSED_COMBINED;
pub(crate) use parse::{declared_logic_routes_as_all, is_z3_recognized_logic};

/// Detected logic category for theory selection.
///
/// This enum categorizes SMT-LIB logics to determine which theory solvers
/// to use during check-sat.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LogicCategory {
    /// Pure propositional (SAT)
    Propositional,
    /// QF_UF: Quantifier-free uninterpreted functions
    QfUf,
    /// QF_AX: Quantifier-free arrays with extensionality
    QfAx,
    /// QF_LRA: Quantifier-free linear real arithmetic
    QfLra,
    /// QF_LIA: Quantifier-free linear integer arithmetic
    QfLia,
    /// QF_NIA: Quantifier-free non-linear integer arithmetic
    QfNia,
    /// QF_EIA: Quantifier-free integer arithmetic with exponentiation
    QfEia,
    /// QF_NRA: Quantifier-free non-linear real arithmetic
    QfNra,
    /// QF_NIRA: Quantifier-free non-linear mixed integer/real arithmetic
    QfNira,
    /// QF_UFNIA: Quantifier-free UF + non-linear integer arithmetic (#5984)
    QfUfnia,
    /// QF_UFNRA: Quantifier-free UF + non-linear real arithmetic (#5984)
    QfUfnra,
    /// QF_UFNIRA: Quantifier-free UF + non-linear mixed int/real arithmetic (#5984)
    QfUfnira,
    /// QF_UFLIA: Quantifier-free uninterpreted functions with linear integer arithmetic
    QfUflia,
    /// QF_UFLRA: Quantifier-free uninterpreted functions with linear real arithmetic
    QfUflra,
    /// QF_AUFLIA: Quantifier-free arrays + uninterpreted functions + linear integer arithmetic
    QfAuflia,
    /// QF_AUFLRA: Quantifier-free arrays + uninterpreted functions + linear real arithmetic
    QfAuflra,
    /// QF_LIRA: Quantifier-free linear integer and real arithmetic (mixed)
    QfLira,
    /// QF_AUFLIRA: Quantifier-free arrays + uninterpreted functions + linear integer/real arithmetic
    QfAuflira,
    /// QF_BV: Quantifier-free bitvectors
    QfBv,
    /// QF_ABV: Quantifier-free arrays + bitvectors
    QfAbv,
    /// QF_UFBV: Quantifier-free uninterpreted functions + bitvectors
    QfUfbv,
    /// QF_AUFBV: Quantifier-free arrays + uninterpreted functions + bitvectors
    QfAufbv,
    /// BV + integer arithmetic (bv2nat/int2bv cross-theory). Not yet supported (#5503).
    QfBvLia,
    /// BV + integer arithmetic without conversion functions (#5356).
    /// BV and Int coexist but don't interact — route to AUFLIA (BV as UF).
    QfBvLiaIndep,
    /// QF_S: Quantifier-free strings
    QfS,
    /// QF_SLIA: Quantifier-free strings + linear integer arithmetic
    QfSlia,
    /// QF_SNIA: Quantifier-free strings + non-linear integer arithmetic
    QfSnia,
    /// QF_SEQ: Quantifier-free generic sequences (Seq T)
    QfSeq,
    /// QF_SEQBV: Quantifier-free sequences over bitvectors
    QfSeqBv,
    /// QF_SEQLIA: Quantifier-free generic sequences + linear integer arithmetic
    QfSeqlia,
    /// QF_SET: Quantifier-free finite sets (card + subset over Array(T->Bool))
    QfSet,
    /// QF_SETLIA: Quantifier-free finite sets + linear integer arithmetic
    QfSetlia,
    /// QF_MULTISET: Quantifier-free multisets (count + subset over Array(T->Int))
    QfMultiset,
    /// QF_MSLIA: Quantifier-free multisets + linear integer arithmetic
    QfMslia,
    /// QF_MAP: Quantifier-free finite maps (get/dom + subset over the value
    /// carrier Array(K->V) + domain carrier Array(K->Bool))
    QfMap,
    /// QF_MAPLIA: Quantifier-free finite maps + linear integer arithmetic
    QfMaplia,
    /// QF_FP: Quantifier-free IEEE 754 floating-point
    QfFp,
    /// QF_BVFP: Quantifier-free bitvectors + floating-point
    QfBvfp,
    /// QF_ABVFP: Quantifier-free arrays + bitvectors + floating-point
    QfAbvfp,
    /// QF_DT: Quantifier-free algebraic datatypes
    QfDt,
    /// Internal: DT + LIA combined (ALL logic with datatypes + integers)
    DtAuflia,
    /// Internal: DT + LRA combined (ALL logic with datatypes + reals)
    DtAuflra,
    /// Internal: DT + UFBV combined (ALL logic with datatypes + bitvectors)
    DtUfbv,
    /// Internal: DT + AUFBV combined (ALL logic with datatypes + arrays + bitvectors)
    DtAufbv,
    /// Internal: DT + LIRA combined (ALL logic with datatypes + mixed int/real)
    DtAuflira,
    /// Internal: DT + AX combined (ALL logic with datatypes + arrays, no BV)
    DtAx,

    // Quantified logics (use E-matching + CEGQI)
    /// LIA: Quantified linear integer arithmetic
    Lia,
    /// LRA: Quantified linear real arithmetic
    Lra,
    /// NIA: Quantified non-linear integer arithmetic
    Nia,
    /// NRA: Quantified non-linear real arithmetic
    Nra,
    /// UFNIA: Quantified UF + non-linear integer arithmetic (#5984)
    Ufnia,
    /// UFNRA: Quantified UF + non-linear real arithmetic (#5984)
    Ufnra,
    /// UFNIRA: Quantified UF + non-linear mixed int/real arithmetic (#5984)
    Ufnira,
    /// UF: Quantified uninterpreted functions
    Uf,
    /// UFLIA: Quantified UF + LIA
    Uflia,
    /// AUFLIA: Quantified Arrays + UF + LIA
    Auflia,
    /// AUFLRA: Quantified Arrays + UF + LRA
    Auflra,
    /// UFLRA: Quantified UF + LRA
    Uflra,
    /// LIRA: Quantified linear mixed integer/real arithmetic
    Lira,
    /// NIRA: Quantified non-linear mixed integer/real arithmetic
    Nira,
    /// AUFLIRA: Quantified arrays + UF + linear mixed integer/real arithmetic
    Auflira,

    // Quantified datatype logics (#7150: E-matching + CEGQI, route to DT solvers)
    /// UFDT: Quantified UF + algebraic datatypes
    Ufdt,
    /// UFDTLIA: Quantified UF + datatypes + linear integer arithmetic
    Ufdtlia,
    /// UFDTLRA: Quantified UF + datatypes + linear real arithmetic
    Ufdtlra,
    /// UFDTLIRA: Quantified UF + datatypes + linear mixed int/real arithmetic
    Ufdtlira,
    /// UFDTNIA: Quantified UF + datatypes + non-linear integer arithmetic
    Ufdtnia,
    /// UFDTNRA: Quantified UF + datatypes + non-linear real arithmetic
    Ufdtnra,
    /// UFDTNIRA: Quantified UF + datatypes + non-linear mixed int/real arithmetic
    Ufdtnira,
    /// AUFDT: Quantified arrays + UF + datatypes
    Aufdt,
    /// AUFDTLIA: Quantified arrays + UF + datatypes + linear integer arithmetic
    Aufdtlia,
    /// AUFDTLIRA: Quantified arrays + UF + datatypes + linear mixed int/real arithmetic
    Aufdtlira,

    /// Other logics (not yet supported)
    Other,
}

/// Theory kind for theory-aware solving.
///
/// Maps logic categories to the actual theory solver combination to use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TheoryKind {
    /// Pure propositional (SAT)
    Propositional,
    /// EUF theory only
    Euf,
    /// Combined EUF + Arrays theory
    ArrayEuf,
    /// Linear Real Arithmetic
    Lra,
    /// Non-linear Integer Arithmetic
    Nia,
    /// Non-linear Real Arithmetic
    Nra,
    /// Combined EUF + LRA theory
    UfLra,
    /// Combined Arrays + EUF + LRA theory
    AufLra,
    /// Bitvector theory (eager bit-blasting)
    Bv,
    /// Combined Arrays + Bitvector theory (eager bit-blasting with array axioms)
    ArrayBv,
    /// Combined UF + Bitvector theory (eager bit-blasting with EUF congruence axioms)
    UfBv,
    /// Combined Arrays + UF + Bitvector theory (eager bit-blasting with array and EUF axioms)
    AufBv,
    /// Algebraic datatypes theory
    Dt,
    /// String theory (pure QF_S)
    Strings,
    /// Sequence theory (pure QF_SEQ)
    Seq,
}

#[cfg(test)]
mod tests;
