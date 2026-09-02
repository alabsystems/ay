// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for `Logic` type: round-trip, aliases, and error mapping.

use std::str::FromStr;

use crate::api::types::{Logic, SolverError};
use crate::api::Solver;

#[test]
fn test_logic_from_str_all_canonical() {
    // Every Logic variant round-trips through Display -> FromStr
    let all_logics = [
        Logic::All,
        Logic::QfLia,
        Logic::QfLra,
        Logic::QfLira,
        Logic::QfUf,
        Logic::QfUflia,
        Logic::QfUflra,
        Logic::QfAuflia,
        Logic::QfAuflra,
        Logic::QfAuflira,
        Logic::QfNia,
        Logic::QfEia,
        Logic::QfNra,
        Logic::QfNira,
        Logic::QfBv,
        Logic::QfUfbv,
        Logic::QfAbv,
        Logic::QfAufbv,
        Logic::QfUfbvlia,
        Logic::QfAufbvlia,
        Logic::QfUfnia,
        Logic::QfUfnra,
        Logic::QfUfnira,
        Logic::QfFp,
        Logic::QfBvfp,
        Logic::QfAbvfp,
        Logic::QfS,
        Logic::QfSlia,
        Logic::QfSeq,
        Logic::QfSeqlia,
        Logic::QfAx,
        Logic::QfDt,
        Logic::QfAlia,
        Logic::QfUfdt,
        Logic::QfSnia,
        Logic::Lia,
        Logic::Lra,
        Logic::Nia,
        Logic::Nra,
        Logic::Nira,
        Logic::Uf,
        Logic::Uflia,
        Logic::Uflra,
        Logic::Ufnia,
        Logic::Ufnra,
        Logic::Ufnira,
        Logic::Bv,
        Logic::Ufbv,
        Logic::Auflia,
        Logic::Auflra,
        Logic::Lira,
        Logic::Auflira,
        Logic::Ufdt,
        Logic::Ufdtlia,
        Logic::Ufdtnia,
    ];
    for logic in &all_logics {
        let s = logic.to_string();
        let parsed = Logic::from_str(&s).unwrap();
        assert_eq!(*logic, parsed, "round-trip failed for {s}");
    }
}

#[test]
fn test_logic_from_str_aliases() {
    assert_eq!(Logic::from_str("QF_IDL").unwrap(), Logic::QfLia);
    assert_eq!(Logic::from_str("QF_RDL").unwrap(), Logic::QfLra);
    assert_eq!(Logic::from_str("QF_FPBV").unwrap(), Logic::QfBvfp);
    assert_eq!(Logic::from_str("ALL_SUPPORTED").unwrap(), Logic::All);
    // Aliases for UF+nonlinear combinations
    assert_eq!(Logic::from_str("QF_AUFNIA").unwrap(), Logic::QfUfnia);
    assert_eq!(Logic::from_str("QF_AUFNRA").unwrap(), Logic::QfUfnra);
    assert_eq!(Logic::from_str("QF_AUFNIRA").unwrap(), Logic::QfUfnira);
    assert_eq!(Logic::from_str("AUFNIA").unwrap(), Logic::Ufnia);
    assert_eq!(Logic::from_str("AUFNRA").unwrap(), Logic::Ufnra);
    assert_eq!(Logic::from_str("AUFNIRA").unwrap(), Logic::Ufnira);
    // New aliases added for #5022
    assert_eq!(Logic::from_str("QF_UFIDL").unwrap(), Logic::QfUflia);
    assert_eq!(Logic::from_str("QF_FPLRA").unwrap(), Logic::QfFp);
    assert_eq!(Logic::from_str("ALIA").unwrap(), Logic::Auflia);
    assert_eq!(Logic::from_str("ALRA").unwrap(), Logic::Auflra);
    assert_eq!(Logic::from_str("ALIRA").unwrap(), Logic::Auflira);
    assert_eq!(Logic::from_str("ABV").unwrap(), Logic::QfAbv);
    assert_eq!(Logic::from_str("AUFBV").unwrap(), Logic::QfAufbv);
    assert_eq!(Logic::from_str("QF_BOOL").unwrap(), Logic::All);
    assert_eq!(Logic::from_str("BOOL").unwrap(), Logic::All);
}

#[test]
fn test_logic_from_str_unknown() {
    let err = Logic::from_str("BOGUS_LOGIC").unwrap_err();
    match err {
        SolverError::UnsupportedLogic(s) => assert_eq!(s, "BOGUS_LOGIC"),
        other => panic!("wrong error variant: {other:?}"),
    }
}

#[test]
fn test_named_bv_lia_combinations_are_publicly_constructible() {
    for logic in [Logic::QfUfbvlia, Logic::QfAufbvlia] {
        assert!(
            Solver::try_new(logic).is_ok(),
            "constructor rejected public logic {}",
            logic.as_str()
        );
    }

    let message = SolverError::UnsupportedLogic("INVALID_LOGIC".to_owned()).to_string();
    assert!(message.contains("QF_UFBVLIA"));
    assert!(message.contains("QF_AUFBVLIA"));
}
