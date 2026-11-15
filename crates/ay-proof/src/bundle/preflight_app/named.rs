// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod core;
mod numeric;

#[derive(Clone, Copy)]
enum Rule {
    Equal,
    Distinct,
    Not,
    Bools,
    Implies,
    Ite,
    Select,
    Store,
    ConstArray,
    BvUnary,
    BvBinary,
    BvCompare,
    Concat,
    IndexedBvOnly,
    FpCompose,
    FpUnary,
    FpClassify,
    FpCompare,
    IndexedFpOnly,
}

const RULES: &[(Rule, &[&str])] = &[
    (Rule::Equal, &["="]),
    (Rule::Distinct, &["distinct"]),
    (Rule::Not, &["not"]),
    (Rule::Bools, &["and", "or", "xor"]),
    (Rule::Implies, &["=>"]),
    (Rule::Ite, &["ite"]),
    (Rule::Select, &["select"]),
    (Rule::Store, &["store"]),
    (Rule::ConstArray, &["const-array"]),
    (Rule::BvUnary, &["bvnot", "bvneg"]),
    (
        Rule::BvBinary,
        &[
            "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor", "bvadd", "bvsub", "bvmul",
            "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr",
        ],
    ),
    (
        Rule::BvCompare,
        &[
            "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
        ],
    ),
    (Rule::Concat, &["concat"]),
    (
        Rule::IndexedBvOnly,
        &[
            "extract",
            "zero_extend",
            "sign_extend",
            "rotate_left",
            "rotate_right",
            "repeat",
        ],
    ),
    (Rule::FpCompose, &["fp"]),
    (Rule::FpUnary, &["fp.abs", "fp.neg"]),
    (
        Rule::FpClassify,
        &[
            "fp.isNaN",
            "fp.isInfinite",
            "fp.isZero",
            "fp.isNormal",
            "fp.isSubnormal",
            "fp.isPositive",
            "fp.isNegative",
        ],
    ),
    (
        Rule::FpCompare,
        &["fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq"],
    ),
    (
        Rule::IndexedFpOnly,
        &["+zero", "-zero", "+oo", "-oo", "NaN"],
    ),
];

pub(super) fn validate(app: &mut App<'_, '_>) -> Result<(), ProofCheckError> {
    for &(rule, names) in RULES {
        app.charge(1, 0)?;
        for &name in names {
            if !app.named(name)? {
                continue;
            }
            return match rule {
                Rule::Equal
                | Rule::Distinct
                | Rule::Not
                | Rule::Bools
                | Rule::Implies
                | Rule::Ite
                | Rule::Select
                | Rule::Store
                | Rule::ConstArray => core::validate(app, rule),
                Rule::BvUnary | Rule::BvBinary | Rule::BvCompare | Rule::Concat => {
                    numeric::bitvector(app, rule)
                }
                Rule::FpCompose | Rule::FpUnary | Rule::FpClassify | Rule::FpCompare => {
                    numeric::floating_point(app, rule)
                }
                Rule::IndexedBvOnly => app.invalid("bit-vector operator must be an indexed symbol"),
                Rule::IndexedFpOnly => {
                    app.invalid("floating-point literal must be an indexed symbol")
                }
            };
        }
    }
    // Preserve the limited legacy builtin table, including unconstrained
    // named arithmetic/string operators and arbitrary UF signatures.
    Ok(())
}
