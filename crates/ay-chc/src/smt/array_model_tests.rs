// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_build_term_values_map_includes_ground_indices_and_unnamed_selects() {
    let mut terms = TermStore::new();
    let bv4 = Sort::bitvec(4);
    let array = terms.mk_var("a", Sort::array(bv4.clone(), bv4));
    let index = terms.mk_bitvec(BigInt::from(3u8), 4);
    let select = terms.mk_select(array, index);

    let mut bv_term_to_bits = HbHashMap::default();
    // LSB first: 0111. The negative literals exercise polarity handling.
    bv_term_to_bits.insert(select, vec![1, -2, 3, -4]);
    let term_values = SmtContext::build_term_values_map(
        &terms,
        &None,
        &[true, false, true, true],
        &std::collections::BTreeMap::new(),
        &bv_term_to_bits,
        0,
    );

    assert_eq!(term_values.get(&index).map(String::as_str), Some("#x3"));
    assert_eq!(term_values.get(&select).map(String::as_str), Some("#x7"));
}

#[test]
fn test_array_interp_to_smt_value_preserves_symbolic_entries_6289() {
    let interp = ay_arrays::ArrayInterpretation {
        default: Some("@arr33".to_string()),
        stores: vec![("__au_k0_(_ BitVec 32)".to_string(), "@arr34".to_string())],
        index_sort: None,
        element_sort: None,
    };
    let bv32 = Sort::BitVec(ay_core::BitVecSort { width: 32 });

    assert_eq!(
        SmtContext::array_interp_to_smt_value(&interp, &bv32, &bv32),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Opaque("@arr33".to_string())),
            entries: vec![(
                SmtValue::Opaque("__au_k0".to_string()),
                SmtValue::Opaque("@arr34".to_string()),
            )],
        }
    );
}

#[test]
fn test_array_interp_to_smt_value_reverses_newest_first_duplicate_stores() {
    let interp = ay_arrays::ArrayInterpretation {
        default: Some("0".to_string()),
        // ArrayInterpretation lookup chooses the first duplicate, so 1 maps
        // to 20.  ArrayMap lookup chooses the last duplicate and therefore
        // needs the converted entries in the opposite order.
        stores: vec![
            ("1".to_string(), "20".to_string()),
            ("1".to_string(), "10".to_string()),
        ],
        index_sort: Some(Sort::Int),
        element_sort: Some(Sort::Int),
    };

    assert_eq!(
        SmtContext::array_interp_to_smt_value(&interp, &Sort::Int, &Sort::Int),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![
                (SmtValue::Int(1), SmtValue::Int(10)),
                (SmtValue::Int(1), SmtValue::Int(20)),
            ],
        }
    );
}
