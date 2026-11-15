// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent SMT-LIB checks for every integer-conversion rounding mode.
use super::super::*;
use super::generator::AcceptedClause;
use int_cast::{fp_to_bv, IntTarget};

fn accepted_cast(
    format: (u32, u32),
    bits: u64,
    width: u32,
    mode: (&str, Rm),
    target: IntTarget,
) -> Option<AcceptedClause> {
    let (eb, sb) = format;
    let source_width = eb + sb;
    let bits = BigInt::from(bits) & ((BigInt::one() << source_width as usize) - 1);
    let value = Fp::from_bits(&bits, eb, sb).expect("supported IEEE format");
    let expected = fp_to_bv(&value, mode.1, width, target)?;
    let name = match target {
        IntTarget::Signed => "fp.to_sbv",
        IntTarget::Unsigned => "fp.to_ubv",
    };
    let mut terms = TermStore::new();
    let raw = terms.mk_bitvec(bits.clone(), source_width);
    let fp = terms.mk_app(
        Symbol::indexed("to_fp", vec![eb, sb]),
        [raw],
        Sort::FloatingPoint(eb, sb),
    );
    let rm = terms.mk_app(
        Symbol::named(mode.0),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let cast = terms.mk_app(
        Symbol::indexed(name, vec![width]),
        [rm, fp],
        Sort::bitvec(width),
    );
    let want = terms.mk_bitvec(expected.clone(), width);
    let equality = terms.mk_app(Symbol::named("="), [cast, want], Sort::Bool);
    assert!(recognize_fp_ground_eval(&terms, &[equality]));
    assert!(validate_fp_ground_eval(&terms, ProofId(0), &[equality]).is_ok());
    Some(AcceptedClause {
        declarations: Vec::new(),
        literals: vec![format!(
            "(= ((_ {name} {width}) {} ((_ to_fp {eb} {sb}) (_ bv{bits} {source_width}))) (_ bv{expected} {width}))",
            mode.0
        )],
    })
}

pub(super) fn accepted_clauses() -> Vec<AcceptedClause> {
    let mut clauses = Vec::new();
    let mut random = 0x0a17_c45e_9b26_d803u64;
    for round in 0..512 {
        random ^= random << 13;
        random ^= random >> 7;
        random ^= random << 17;
        let format = [(5, 11), (8, 24), (11, 53)][round % 3];
        let width = [1, 8, 16, 32, 64, 128, 256][round % 7];
        for target in [IntTarget::Signed, IntTarget::Unsigned] {
            for mode in [
                ("RNE", Rm::Rne),
                ("RNA", Rm::Rna),
                ("RTP", Rm::Rtp),
                ("RTN", Rm::Rtn),
                ("RTZ", Rm::Rtz),
            ] {
                if let Some(clause) = accepted_cast(format, random, width, mode, target) {
                    clauses.push(clause);
                }
            }
        }
    }
    clauses
}
