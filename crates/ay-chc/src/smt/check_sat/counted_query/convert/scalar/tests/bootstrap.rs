// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;

#[test]
fn authentic_boolean_bv_attachment_enters_traced_bootstrap_under_its_original_owner() {
    let _ = ay_core::misc_cli_flags();
    let source = formula();
    let original = ample();
    let mut converted = convert(&source, &original).unwrap();
    converted
        .with_scalar_encoding(|encoding| {
            assert!(encoding.admission().shares_ledger_with(&original));
            assert!(encoding
                .rows()
                .iter()
                .any(|r| matches!(r.origin(), RowOrigin::Boolean(_))));
            assert!(encoding
                .rows()
                .iter()
                .any(|r| matches!(r.origin(), RowOrigin::Bitvector(_))));
            assert!(encoding
                .rows()
                .iter()
                .any(|r| matches!(r.origin(), RowOrigin::Link { .. })));
            // TEST bridge only: these adapter vectors are deliberately outside the
            // SAT bootstrap receipt. Production public/conjunct integration must
            // admit this adaptation and preserve its source/row derivation map.
            let rows: Vec<Vec<_>> = encoding
                .rows()
                .iter()
                .map(|r| {
                    r.literals()
                        .iter()
                        .copied()
                        .map(Literal::from_dimacs)
                        .collect()
                })
                .collect();
            let views: Vec<_> = rows.iter().map(Vec::as_slice).collect();
            let before = original.usage().unwrap();
            let input = ay_sat::initial_cnf::CountedInitialCnf::try_new(
                encoding.num_vars() as usize,
                &views,
                original.clone(),
            )
            .map_err(Error::Stopped)?;
            // Existing CountedCnf asserts its root. Do not relabel this authentic
            // root-only encoding as a separately encoded conjunct-assumption list.
            let built = input.construct_traced(&[]).map_err(Error::Stopped)?;
            assert!(built.assumptions().unwrap().is_empty());
            assert!(!built.initial_conflict().unwrap());
            assert!(built.initial_assigned_variables().unwrap() > 0);
            let after = built.usage().unwrap();
            assert_eq!(after, original.usage().unwrap());
            assert!(after.work_admitted > before.work_admitted);
            assert!(after.storage_admitted > before.storage_admitted);
            built.dispose().map_err(Error::Stopped)
        })
        .unwrap();
    converted.finish().unwrap();
    assert_eq!(original.usage().unwrap().refusal, None);
}
