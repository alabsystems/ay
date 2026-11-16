// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

fn expected(name: &str, width: u32, a: u64, b: u64) -> u64 {
    let modulus = 1u64 << width;
    let mask = modulus - 1;
    let signed = |v: u64| {
        if v >= modulus / 2 {
            v as i64 - modulus as i64
        } else {
            v as i64
        }
    };
    let (sa, sb) = (signed(a), signed(b));
    (match name {
        "bvadd" => a.wrapping_add(b),
        "bvsub" => a.wrapping_sub(b),
        "bvmul" => a * b,
        "bvand" => a & b,
        "bvor" => a | b,
        "bvxor" => a ^ b,
        "bvnand" => !(a & b),
        "bvnor" => !(a | b),
        "bvxnor" => !(a ^ b),
        "bvudiv" => a.checked_div(b).unwrap_or(mask),
        "bvurem" => {
            if b == 0 {
                a
            } else {
                a % b
            }
        }
        "bvsdiv" => {
            if sb == 0 {
                if sa < 0 {
                    1
                } else {
                    mask
                }
            } else {
                (sa / sb) as u64
            }
        }
        "bvsrem" => {
            if sb == 0 {
                a
            } else {
                (sa % sb) as u64
            }
        }
        "bvsmod" => {
            if sb == 0 {
                a
            } else {
                let r = sa % sb;
                (if r != 0 && (r < 0) != (sb < 0) {
                    r + sb
                } else {
                    r
                }) as u64
            }
        }
        "bvshl" => a << b,
        "bvlshr" => a >> b,
        "bvashr" => (sa >> b) as u64,
        _ => panic!("unknown test operation"),
    }) & mask
}

const BINARY_OPERATIONS: [&str; 17] = [
    "bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor", "bvudiv",
    "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr",
];

fn binary_cases(width: u32, samples: &[(u64, u64)]) {
    for name in BINARY_OPERATIONS {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(width));
        let y = terms.mk_var("y", Sort::bitvec(width));
        let output = operation(&mut terms, name, x, y, width);
        let original = ample();
        let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
        encoder.encode_terms(&[output]).unwrap();
        let mut ordinary = BvSolver::new(&terms);
        let ordinary_output = ordinary.get_bits(output);
        let ox = ordinary.get_bits(x);
        let oy = ordinary.get_bits(y);
        for &(a, b) in samples {
            let actual = solve_word(
                encoder.num_vars().unwrap(),
                encoder.clauses().unwrap(),
                &pins(encoder.bits(x).unwrap(), encoder.bits(y).unwrap(), a, b),
                encoder.bits(output).unwrap(),
            );
            let legacy = solve_word(
                ordinary.num_vars(),
                ordinary.clauses(),
                &pins(&ox, &oy, a, b),
                &ordinary_output,
            );
            assert_eq!(
                actual,
                expected(name, width, a, b),
                "{name}[{width}]({a},{b})"
            );
            assert_eq!(actual, legacy, "ordinary/count parity for {name}");
        }
        encoder.finish().unwrap();
    }
}

#[test]
fn original_circuits_match_small_domain_oracle_including_signed_and_zero_divisors() {
    binary_cases(3, &[(0, 0), (7, 0), (4, 7), (3, 2), (5, 3), (7, 7)]);
}

#[test]
fn width_one_operations_have_the_unique_smtlib_output_for_every_input() {
    binary_cases(1, &[(0, 0), (0, 1), (1, 0), (1, 1)]);
}

#[test]
fn full_boolean_semantics_including_implication_distinct_and_ite() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let implication = terms.mk_app(Symbol::named("=>"), [a, b], Sort::Bool);
    let distinct = terms.mk_app(Symbol::named("distinct"), [a, b], Sort::Bool);
    let equal = terms.mk_app(Symbol::named("="), [a, b], Sort::Bool);
    let ite = terms.mk_ite_raw(a, distinct, equal);
    let original = ample();
    let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    encoder
        .encode_terms(&[implication, distinct, equal, ite])
        .unwrap();
    for av in [false, true] {
        for bv in [false, true] {
            let pins = [
                (encoder.literal(a).unwrap(), av),
                (encoder.literal(b).unwrap(), bv),
            ];
            for (root, expected) in [
                (implication, !av || bv),
                (distinct, av != bv),
                (equal, av == bv),
                (ite, if av { av != bv } else { av == bv }),
            ] {
                let actual = solve_word(
                    encoder.num_vars().unwrap(),
                    encoder.clauses().unwrap(),
                    &pins,
                    &[encoder.literal(root).unwrap()],
                );
                assert_eq!(actual, u64::from(expected));
            }
        }
    }
    encoder.finish().unwrap();
}

#[test]
fn constant_only_width129_and_indexed_wiring_still_pay_for_scratch() {
    let mut terms = TermStore::new();
    let value = terms.mk_bitvec(BigInt::from(5u32), 129);
    let shift = terms.mk_bitvec(BigInt::from(2u32), 129);
    let left = operation(&mut terms, "bvshl", value, shift, 129);
    let product = operation(&mut terms, "bvmul", value, shift, 129);
    let not = terms.mk_app(Symbol::named("bvnot"), [value], Sort::bitvec(129));
    let extract = terms.mk_app(
        Symbol::indexed("extract", vec![7, 0]),
        [left],
        Sort::bitvec(8),
    );
    let extend = terms.mk_app(
        Symbol::indexed("sign_extend", vec![121]),
        [extract],
        Sort::bitvec(129),
    );
    let original = ample();
    let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    let before = original.usage().unwrap();
    encoder.encode_terms(&[left, product, not, extend]).unwrap();
    let after = original.usage().unwrap();
    assert!(after.storage_admitted > before.storage_admitted + 129 * 4 * 4);
    assert_eq!(encoder.bits(extend).unwrap().len(), 129);
    let actual = solve_word(
        encoder.num_vars().unwrap(),
        encoder.clauses().unwrap(),
        &[],
        encoder.bits(extract).unwrap(),
    );
    assert_eq!(actual, 20);
    for (root, low, high) in [
        (left, 20u64, false),
        (product, 10, false),
        (not, !5u64, true),
        (extend, 20, false),
    ] {
        let expected: Vec<bool> = (0..129)
            .map(|bit| {
                if bit < 64 {
                    low & (1u64 << bit) != 0
                } else {
                    high
                }
            })
            .collect();
        assert_unique_bits(
            encoder.num_vars().unwrap(),
            encoder.clauses().unwrap(),
            &[],
            encoder.bits(root).unwrap(),
            &expected,
        );
    }
    encoder.finish().unwrap();
}

#[test]
fn comparisons_and_bvcomp_have_unique_outputs_at_width_one_and_three() {
    for width in [1u32, 3] {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::bitvec(width));
        let b = terms.mk_var("b", Sort::bitvec(width));
        let mut roots = Vec::new();
        for name in [
            "=", "distinct", "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt",
            "bvsge", "bvcomp",
        ] {
            let sort = if name == "bvcomp" {
                Sort::bitvec(1)
            } else {
                Sort::Bool
            };
            roots.push((name, terms.mk_app(Symbol::named(name), [a, b], sort)));
        }
        let original = ample();
        let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
        encoder
            .encode_terms(&roots.iter().map(|(_, root)| *root).collect::<Vec<_>>())
            .unwrap();
        let modulus = 1u64 << width;
        let signed = |v: u64| {
            if v >= modulus / 2 {
                v as i64 - modulus as i64
            } else {
                v as i64
            }
        };
        for av in 0..modulus {
            for bv in 0..modulus {
                let pins = pins(encoder.bits(a).unwrap(), encoder.bits(b).unwrap(), av, bv);
                for &(name, root) in &roots {
                    let expected = match name {
                        "=" | "bvcomp" => av == bv,
                        "distinct" => av != bv,
                        "bvult" => av < bv,
                        "bvule" => av <= bv,
                        "bvugt" => av > bv,
                        "bvuge" => av >= bv,
                        "bvslt" => signed(av) < signed(bv),
                        "bvsle" => signed(av) <= signed(bv),
                        "bvsgt" => signed(av) > signed(bv),
                        "bvsge" => signed(av) >= signed(bv),
                        _ => unreachable!(),
                    };
                    let literal = if name == "bvcomp" {
                        encoder.bits(root).unwrap()[0]
                    } else {
                        encoder.literal(root).unwrap()
                    };
                    assert_unique_bits(
                        encoder.num_vars().unwrap(),
                        encoder.clauses().unwrap(),
                        &pins,
                        &[literal],
                        &[expected],
                    );
                }
            }
        }
        encoder.finish().unwrap();
    }
}

#[test]
fn indexed_extract_extension_repeat_rotate_and_concat_preserve_exact_bit_positions() {
    type IndexedCase = (&'static str, &'static [u32], u32, fn(u64, u64) -> u64);

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(3));
    let b = terms.mk_var("b", Sort::bitvec(3));
    let cases: [IndexedCase; 10] = [
        ("extract", &[1, 1], 1, |a, _| (a >> 1) & 1),
        ("extract", &[2, 0], 3, |a, _| a),
        ("zero_extend", &[2], 5, |a, _| a),
        ("sign_extend", &[2], 5, |a, _| {
            if a & 4 != 0 {
                a | 0b1_1000
            } else {
                a
            }
        }),
        ("rotate_left", &[0], 3, |a, _| a),
        ("rotate_left", &[1], 3, |a, _| ((a << 1) | (a >> 2)) & 7),
        ("rotate_left", &[8], 3, |a, _| ((a << 2) | (a >> 1)) & 7),
        ("rotate_right", &[8], 3, |a, _| ((a >> 2) | (a << 1)) & 7),
        ("repeat", &[1], 3, |a, _| a),
        ("repeat", &[3], 9, |a, _| a | (a << 3) | (a << 6)),
    ];
    let mut outputs = Vec::new();
    for &(name, indices, width, expected) in &cases {
        let root = terms.mk_app(
            Symbol::indexed(name, indices.to_vec()),
            [a],
            Sort::bitvec(width),
        );
        outputs.push((root, expected));
    }
    let concat = terms.mk_app(Symbol::named("concat"), [a, b], Sort::bitvec(6));
    outputs.push((concat, |a, b| (a << 3) | b));
    let original = ample();
    let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    encoder
        .encode_terms(&outputs.iter().map(|(root, _)| *root).collect::<Vec<_>>())
        .unwrap();
    for av in 0..8 {
        for bv in [0, 3, 7] {
            let pins = pins(encoder.bits(a).unwrap(), encoder.bits(b).unwrap(), av, bv);
            for &(root, expected) in &outputs {
                assert_eq!(
                    solve_word(
                        encoder.num_vars().unwrap(),
                        encoder.clauses().unwrap(),
                        &pins,
                        encoder.bits(root).unwrap()
                    ),
                    expected(av, bv)
                );
            }
        }
    }
    encoder.finish().unwrap();
}

#[test]
fn unary_and_bv_ite_do_not_leave_either_selected_word_underconstrained() {
    for width in [1u32, 3] {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::bitvec(width));
        let b = terms.mk_var("b", Sort::bitvec(width));
        let select = terms.mk_var("select", Sort::Bool);
        let not = terms.mk_app(Symbol::named("bvnot"), [a], Sort::bitvec(width));
        let neg = terms.mk_app(Symbol::named("bvneg"), [a], Sort::bitvec(width));
        let ite = terms.mk_ite_raw(select, a, b);
        let original = ample();
        let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
        encoder.encode_terms(&[not, neg, ite]).unwrap();
        let modulus = 1u64 << width;
        let mask = modulus - 1;
        for av in 0..modulus {
            for bv in [0, mask] {
                for selected in [false, true] {
                    let mut pins = pins(encoder.bits(a).unwrap(), encoder.bits(b).unwrap(), av, bv);
                    pins.push((encoder.literal(select).unwrap(), selected));
                    for (root, expected) in [
                        (not, !av & mask),
                        (neg, av.wrapping_neg() & mask),
                        (ite, if selected { av } else { bv }),
                    ] {
                        assert_eq!(
                            solve_word(
                                encoder.num_vars().unwrap(),
                                encoder.clauses().unwrap(),
                                &pins,
                                encoder.bits(root).unwrap()
                            ),
                            expected
                        );
                    }
                }
            }
        }
        encoder.finish().unwrap();
    }
}

#[test]
fn uniqueness_oracle_rejects_a_free_output_and_an_inconsistent_cnf() {
    // A single chosen SAT model is insufficient for a free output.
    assert!(std::panic::catch_unwind(|| solve_word(1, &[], &[], &[1])).is_err());
    // UNSAT alone must not let an inconsistent encoding pass vacuously.
    let contradictory = [CnfClause::unit(1), CnfClause::unit(-1)];
    assert!(std::panic::catch_unwind(|| assert_unique_bits(
        1,
        &contradictory,
        &[],
        &[1],
        &[false]
    ))
    .is_err());
}

#[test]
fn paid_continuation_primitives_can_connect_late_read_words_without_a_new_owner() {
    let terms = TermStore::new();
    let original = ample();
    let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    let a = encoder.fresh_bits(3).unwrap();
    let b = encoder.fresh_bits(3).unwrap();
    let selector = encoder.fresh_bits(1).unwrap()[0];
    let output = encoder.mux_words(&a, &b, selector).unwrap();
    let equal = encoder.equal_words(&output, &a).unwrap();
    encoder.add_clause(&[equal]).unwrap();
    let before = original.usage().unwrap();
    for selected in [false, true] {
        let mut pins = pins(&a, &b, 5, 5);
        pins.push((selector, selected));
        assert_eq!(
            solve_word(
                encoder.num_vars().unwrap(),
                encoder.clauses().unwrap(),
                &pins,
                &output
            ),
            5
        );
    }
    let extra = encoder.fresh_bits(2).unwrap();
    assert!(extra[0].unsigned_abs() > output.iter().map(|l| l.unsigned_abs()).max().unwrap());
    assert!(original.usage().unwrap().work_admitted > before.work_admitted);
    encoder.finish().unwrap();
}
