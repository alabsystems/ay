// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT logic specification and sort conversion.

use ay_core::Sort;

use super::SolverError;

/// SMT logic specification
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Logic {
    /// SMT-LIB `ALL` logic.
    ///
    /// Sets logic to `ALL` and lets the executor auto-detect the actual
    /// theories used at check-sat time. This is useful when the formula may
    /// include datatypes (DT) and/or when the caller does not want to manually
    /// pick a specific QF_* logic upfront.
    All,
    // =========================================================================
    // Quantifier-free logics
    // =========================================================================
    /// Quantifier-free linear integer arithmetic
    QfLia,
    /// Quantifier-free linear real arithmetic
    QfLra,
    /// Quantifier-free linear integer and real arithmetic (mixed)
    ///
    /// Note: QF_LIRA support is incomplete. The solver may return Unknown
    /// for problems that mix Int and Real variables.
    QfLira,
    /// Quantifier-free uninterpreted functions
    QfUf,
    /// Quantifier-free uninterpreted functions with linear integer arithmetic
    QfUflia,
    /// Quantifier-free uninterpreted functions with linear real arithmetic
    QfUflra,
    /// Quantifier-free arrays with uninterpreted functions and linear integer arithmetic
    QfAuflia,
    /// Quantifier-free arrays with uninterpreted functions and linear real arithmetic
    QfAuflra,
    /// Quantifier-free arrays with uninterpreted functions and mixed integer/real arithmetic
    ///
    /// Note: QF_AUFLIRA support is incomplete. The solver may return Unknown
    /// for problems that mix Int and Real variables.
    QfAuflira,
    /// Quantifier-free non-linear integer arithmetic
    QfNia,
    /// Quantifier-free non-linear real arithmetic
    QfNra,
    /// Quantifier-free non-linear mixed integer/real arithmetic
    QfNira,
    /// Quantifier-free bitvectors
    QfBv,
    /// Quantifier-free uninterpreted functions with bitvectors
    QfUfbv,
    /// Quantifier-free arrays with bitvectors
    QfAbv,
    /// Quantifier-free arrays with uninterpreted functions and bitvectors
    QfAufbv,
    /// Quantifier-free uninterpreted functions with non-linear integer arithmetic
    QfUfnia,
    /// Quantifier-free uninterpreted functions with non-linear real arithmetic
    QfUfnra,
    /// Quantifier-free uninterpreted functions with non-linear mixed int/real arithmetic
    QfUfnira,
    /// Quantifier-free IEEE 754 floating-point
    QfFp,
    /// Quantifier-free bitvectors + floating-point
    QfBvfp,
    /// Quantifier-free arrays + bitvectors + floating-point
    QfAbvfp,
    /// Quantifier-free strings
    QfS,
    /// Quantifier-free strings + linear integer arithmetic
    QfSlia,
    /// Quantifier-free sequences
    QfSeq,
    /// Quantifier-free sequences + linear integer arithmetic
    QfSeqlia,
    /// Quantifier-free arrays with extensionality (no arithmetic)
    QfAx,
    /// Quantifier-free algebraic datatypes
    QfDt,
    /// Quantifier-free arrays + linear integer arithmetic (alias for QF_AUFLIA)
    QfAlia,
    /// Quantifier-free UF + algebraic datatypes
    QfUfdt,
    /// Quantifier-free strings + non-linear integer arithmetic
    QfSnia,

    // =========================================================================
    // Quantified logics (use E-matching + CEGQI)
    // =========================================================================
    /// Linear integer arithmetic with quantifiers (E-matching + CEGQI)
    Lia,
    /// Linear real arithmetic with quantifiers
    Lra,
    /// Non-linear integer arithmetic with quantifiers
    Nia,
    /// Non-linear real arithmetic with quantifiers
    Nra,
    /// Non-linear mixed integer/real arithmetic with quantifiers
    Nira,
    /// Uninterpreted functions with quantifiers (E-matching)
    Uf,
    /// Uninterpreted functions + LIA with quantifiers
    Uflia,
    /// Uninterpreted functions + LRA with quantifiers
    Uflra,
    /// Uninterpreted functions + non-linear integer arithmetic with quantifiers
    Ufnia,
    /// Uninterpreted functions + non-linear real arithmetic with quantifiers
    Ufnra,
    /// Uninterpreted functions + non-linear mixed int/real arithmetic with quantifiers
    Ufnira,
    /// Bitvectors with quantifiers
    Bv,
    /// Uninterpreted functions + bitvectors with quantifiers
    Ufbv,
    /// Arrays + UF + LIA with quantifiers
    Auflia,
    /// Arrays + UF + LRA with quantifiers
    Auflra,
    /// Mixed integer/real arithmetic with quantifiers
    Lira,
    /// Arrays + UF + mixed integer/real arithmetic with quantifiers
    Auflira,
    /// UF + algebraic datatypes with quantifiers
    Ufdt,
    /// UF + datatypes + linear integer arithmetic with quantifiers
    Ufdtlia,
    /// UF + datatypes + non-linear integer arithmetic with quantifiers
    Ufdtnia,
}

impl Logic {
    /// Returns the SMT-LIB string representation of the logic.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::All => "ALL",
            // Quantifier-free
            Self::QfLia => "QF_LIA",
            Self::QfLra => "QF_LRA",
            Self::QfLira => "QF_LIRA",
            Self::QfUf => "QF_UF",
            Self::QfUflia => "QF_UFLIA",
            Self::QfUflra => "QF_UFLRA",
            Self::QfAuflia => "QF_AUFLIA",
            Self::QfAuflra => "QF_AUFLRA",
            Self::QfAuflira => "QF_AUFLIRA",
            Self::QfNia => "QF_NIA",
            Self::QfNra => "QF_NRA",
            Self::QfNira => "QF_NIRA",
            Self::QfBv => "QF_BV",
            Self::QfUfbv => "QF_UFBV",
            Self::QfAbv => "QF_ABV",
            Self::QfAufbv => "QF_AUFBV",
            Self::QfUfnia => "QF_UFNIA",
            Self::QfUfnra => "QF_UFNRA",
            Self::QfUfnira => "QF_UFNIRA",
            Self::QfFp => "QF_FP",
            Self::QfBvfp => "QF_BVFP",
            Self::QfAbvfp => "QF_ABVFP",
            Self::QfS => "QF_S",
            Self::QfSlia => "QF_SLIA",
            Self::QfSeq => "QF_SEQ",
            Self::QfSeqlia => "QF_SEQLIA",
            Self::QfAx => "QF_AX",
            Self::QfDt => "QF_DT",
            Self::QfAlia => "QF_ALIA",
            Self::QfUfdt => "QF_UFDT",
            Self::QfSnia => "QF_SNIA",
            // Quantified
            Self::Lia => "LIA",
            Self::Lra => "LRA",
            Self::Nia => "NIA",
            Self::Nra => "NRA",
            Self::Nira => "NIRA",
            Self::Uf => "UF",
            Self::Uflia => "UFLIA",
            Self::Uflra => "UFLRA",
            Self::Ufnia => "UFNIA",
            Self::Ufnra => "UFNRA",
            Self::Ufnira => "UFNIRA",
            Self::Bv => "BV",
            Self::Ufbv => "UFBV",
            Self::Auflia => "AUFLIA",
            Self::Auflra => "AUFLRA",
            Self::Lira => "LIRA",
            Self::Auflira => "AUFLIRA",
            Self::Ufdt => "UFDT",
            Self::Ufdtlia => "UFDTLIA",
            Self::Ufdtnia => "UFDTNIA",
        }
    }
}

impl std::fmt::Display for Logic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl std::str::FromStr for Logic {
    type Err = SolverError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "QF_LIA" | "QF_IDL" => Ok(Self::QfLia),
            "QF_LRA" | "QF_RDL" => Ok(Self::QfLra),
            "QF_LIRA" => Ok(Self::QfLira),
            "QF_UF" => Ok(Self::QfUf),
            "QF_UFLIA" | "QF_UFIDL" => Ok(Self::QfUflia),
            "QF_UFLRA" => Ok(Self::QfUflra),
            "QF_AUFLIA" => Ok(Self::QfAuflia),
            "QF_AUFLRA" => Ok(Self::QfAuflra),
            "QF_AUFLIRA" => Ok(Self::QfAuflira),
            "QF_NIA" => Ok(Self::QfNia),
            "QF_NRA" => Ok(Self::QfNra),
            "QF_NIRA" => Ok(Self::QfNira),
            "QF_BV" => Ok(Self::QfBv),
            "QF_UFBV" => Ok(Self::QfUfbv),
            "QF_ABV" => Ok(Self::QfAbv),
            "QF_AUFBV" => Ok(Self::QfAufbv),
            "QF_UFNIA" | "QF_AUFNIA" => Ok(Self::QfUfnia),
            "QF_UFNRA" | "QF_AUFNRA" => Ok(Self::QfUfnra),
            "QF_UFNIRA" | "QF_AUFNIRA" => Ok(Self::QfUfnira),
            "QF_FP" | "QF_FPLRA" => Ok(Self::QfFp),
            "QF_BVFP" | "QF_FPBV" => Ok(Self::QfBvfp),
            "QF_ABVFP" | "QF_AFPBV" => Ok(Self::QfAbvfp),
            "QF_S" => Ok(Self::QfS),
            "QF_SLIA" => Ok(Self::QfSlia),
            "QF_SEQ" => Ok(Self::QfSeq),
            "QF_SEQLIA" => Ok(Self::QfSeqlia),
            "QF_AX" => Ok(Self::QfAx),
            "QF_DT" => Ok(Self::QfDt),
            "QF_ALIA" => Ok(Self::QfAlia),
            "QF_UFDT" => Ok(Self::QfUfdt),
            "QF_SNIA" => Ok(Self::QfSnia),
            "LIA" => Ok(Self::Lia),
            "LRA" => Ok(Self::Lra),
            "NIA" => Ok(Self::Nia),
            "NRA" => Ok(Self::Nra),
            "NIRA" => Ok(Self::Nira),
            "UF" => Ok(Self::Uf),
            "UFLIA" => Ok(Self::Uflia),
            "UFLRA" => Ok(Self::Uflra),
            "UFNIA" | "AUFNIA" => Ok(Self::Ufnia),
            "UFNRA" | "AUFNRA" => Ok(Self::Ufnra),
            "UFNIRA" | "AUFNIRA" => Ok(Self::Ufnira),
            "BV" => Ok(Self::Bv),
            "UFBV" => Ok(Self::Ufbv),
            "AUFLIA" | "ALIA" => Ok(Self::Auflia),
            "AUFLRA" | "ALRA" => Ok(Self::Auflra),
            "LIRA" => Ok(Self::Lira),
            "AUFLIRA" | "ALIRA" => Ok(Self::Auflira),
            "UFDT" | "DT" => Ok(Self::Ufdt),
            "UFDTLIA" | "DTLIA" => Ok(Self::Ufdtlia),
            "UFDTNIA" => Ok(Self::Ufdtnia),
            // Quantified BV + arrays: internally handled via finite-domain expansion
            "ABV" => Ok(Self::QfAbv),
            "AUFBV" => Ok(Self::QfAufbv),
            // ALL and propositional aliases
            "ALL" | "ALL_SUPPORTED" | "QF_BOOL" | "BOOL" => Ok(Self::All),
            _ => Err(SolverError::UnsupportedLogic(s.to_string())),
        }
    }
}

// ============================================================================
// Sort extension trait for command::Sort conversion (#1437)
// ============================================================================

/// Extension trait for Sort to convert to command::Sort.
///
/// This trait provides the `to_command_sort()` method for converting API Sort
/// to the frontend parser's Sort representation.
pub trait SortExt {
    /// Convert to command::Sort for use with DeclareFun.
    fn to_command_sort(&self) -> ay_frontend::command::Sort;
}

impl SortExt for Sort {
    fn to_command_sort(&self) -> ay_frontend::command::Sort {
        use ay_frontend::command::Sort as CmdSort;
        match self {
            Self::Bool => CmdSort::Simple("Bool".to_string()),
            Self::Int => CmdSort::Simple("Int".to_string()),
            Self::Real => CmdSort::Simple("Real".to_string()),
            Self::BitVec(bv) => CmdSort::Indexed("BitVec".to_string(), vec![bv.width.to_string()]),
            Self::Array(arr) => CmdSort::Parameterized(
                "Array".to_string(),
                vec![
                    arr.index_sort.to_command_sort(),
                    arr.element_sort.to_command_sort(),
                ],
            ),
            Self::String => CmdSort::Simple("String".to_string()),
            Self::RegLan => CmdSort::Simple("RegLan".to_string()),
            Self::FloatingPoint(e, s) => CmdSort::Indexed(
                "FloatingPoint".to_string(),
                vec![e.to_string(), s.to_string()],
            ),
            Self::Uninterpreted(name) => CmdSort::Simple(name.clone()),
            Self::Datatype(dt) => CmdSort::Simple(dt.name.clone()),
            Self::Seq(elem) => {
                CmdSort::Parameterized("Seq".to_string(), vec![elem.to_command_sort()])
            }
            // A `Char` lowers to a bounded `Int` code point in the engine (its
            // `[0, 196607]` invariant is attached as an FFI background axiom), so
            // a `DeclareFun` over a `Char` domain/range registers an `Int`
            // symbol. Keeps the executor `Char`-free.
            Self::Char => CmdSort::Simple("Int".to_string()),
            // A finite-domain value lowers to a bounded `Int` in the engine
            // (its `0 <= x < size` invariant is attached as an FFI background
            // axiom), exactly like `Char`. Keeps the executor FD-free.
            Self::FiniteDomain(_, _) => CmdSort::Simple("Int".to_string()),
            // A type variable behaves like the uninterpreted sort of the same
            // name for (monomorphic) solving; polymorphic instantiation is
            // rejected upstream with an honest sort error.
            Self::TypeVar(name) => CmdSort::Simple(name.clone()),
            // All current Sort variants handled above (#5692).
            other => unreachable!("unhandled Sort variant in to_command_sort(): {other:?}"),
        }
    }
}
