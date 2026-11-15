// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn sequence_power_symbolic_equality_preserves_models_and_negations() {
    for base in ["ab", "λ🦀", "a.*"] {
        let mut terms = TermStore::new();
        let literal = terms.mk_string(base.to_string());
        let count = terms.mk_var("n".to_string(), Sort::Int);
        let word = terms.mk_var("t".to_string(), Sort::String);
        let power = app(&mut terms, "seq.power", &[literal, count], Sort::String);
        let equality = terms.mk_eq(power, word);
        let negation = terms.mk_not(equality);
        for copies in -2i64..=4 {
            let expected = base.repeat(copies.max(0) as usize);
            for target in ["", "ab", "abab", "aba", "ba", "λ🦀", "λ🦀λ🦀", "a.*a.*"] {
                let model = StubModel::new()
                    .with(count, ModelValue::Int(int(copies)))
                    .with(word, ModelValue::Str(target.to_string()));
                let positive = verdict(&terms, &model, &[equality]);
                let negative = verdict(&terms, &model, &[negation]);
                if expected == target {
                    assert_confirmed(&positive);
                    assert_violates(&negative);
                } else {
                    assert_violates(&positive);
                    assert_confirmed(&negative);
                }
            }
        }
    }
}
