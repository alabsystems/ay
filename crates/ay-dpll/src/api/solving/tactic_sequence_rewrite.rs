// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Sequence repetition rewriting from Z3 5.3.3 seq_rewriter::mk_seq_power.
//! Expansion is an equivalence with no fresh symbols or model conversion.
use super::{field_to_bv::Borrowed, tactic_parameters::Steps, tactics::TacticFailure};
use ay_core::term::{reserve_counted, CountedTermBuilder, TermConstructionAdmission};
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use num_traits::{Signed, ToPrimitive, Zero};

fn failed() -> TacticFailure {
    TacticFailure::new("sequence rewriting requires original admission and well-typed operands")
}

pub(super) fn rewrite(
    store: &mut TermStore,
    roots: &[TermId],
    maximum: u32,
    budget: &mut Steps,
    owner: &dyn TermConstructionAdmission,
) -> Result<Vec<TermId>, TacticFailure> {
    let seen = super::tactic_solve_eqs::reachable(store, roots, owner)?;
    let mut mapped = Vec::new();
    reserve_counted(&mut mapped, seen.len(), owner).map_err(|_| failed())?;
    owner.admit(seen.len(), 0).map_err(|_| failed())?;
    mapped.resize(seen.len(), None);
    let borrowed = Borrowed(owner);
    let mut builder = CountedTermBuilder::with_admission(store, &borrowed).map_err(|_| failed())?;
    let mut children = Vec::new();
    for index in 0..seen.len() {
        if !seen[index] {
            continue;
        }
        budget.visit(owner)?;
        let id = TermId(index as u32);
        children.clear();
        super::tactic_solve_eqs::children(builder.terms().get(id), &mut children, owner)?;
        for child in &mut children {
            *child = mapped[child.index()].ok_or_else(failed)?;
        }
        let rebuilt = builder
            .rebuild_existing(id, &children)
            .map_err(|_| failed())?;
        let power = match builder.terms().get(rebuilt) {
            TermData::App(Symbol::Named(name), args) => {
                owner.admit(name.len(), 0).map_err(|_| failed())?;
                if matches!(name.as_str(), "seq.power" | "str.power")
                    && !builder.terms().is_declared_function(name)
                {
                    if args.len() != 2 {
                        return Err(failed());
                    }
                    true
                } else {
                    false
                }
            }
            _ => false,
        };
        mapped[index] = Some(if power {
            let normalized = flatten_power(&mut builder, rebuilt, budget, owner)?;
            expand(&mut builder, normalized, maximum, owner)?
        } else {
            rebuilt
        });
    }
    let mut output = Vec::new();
    reserve_counted(&mut output, roots.len(), owner).map_err(|_| failed())?;
    for root in roots {
        owner.admit(1, 0).map_err(|_| failed())?;
        output.push(mapped[root.index()].ok_or_else(failed)?);
    }
    builder.finish().map_err(|_| failed())?;
    Ok(output)
}

// Z3 seq_rewriter::mk_seq_power returns BR_REWRITE_FULL for this identity.
// Iterate over the strictly decreasing original base chain, retaining the
// SAME Steps and original admission for every generated product and power.
fn flatten_power(
    builder: &mut CountedTermBuilder<'_, '_, Borrowed<'_>>,
    mut id: TermId,
    budget: &mut Steps,
    owner: &dyn TermConstructionAdmission,
) -> Result<TermId, TacticFailure> {
    loop {
        owner.check().map_err(|_| failed())?;
        let TermData::App(Symbol::Named(head), outer) = builder.terms().get(id) else {
            return Err(failed());
        };
        owner.admit(head.len(), 0).map_err(|_| failed())?;
        if !matches!(head.as_str(), "seq.power" | "str.power")
            || builder.terms().is_declared_function(head)
        {
            return Err(failed());
        }
        let [base, n] = outer.as_slice() else {
            return Err(failed());
        };
        let (base, n) = (*base, *n);
        let TermData::App(Symbol::Named(inner_head), inner) = builder.terms().get(base) else {
            return Ok(id);
        };
        owner.admit(inner_head.len(), 0).map_err(|_| failed())?;
        if !matches!(inner_head.as_str(), "seq.power" | "str.power")
            || builder.terms().is_declared_function(inner_head)
        {
            return Ok(id);
        }
        let [word, k] = inner.as_slice() else {
            return Err(failed());
        };
        let (word, k) = (*word, *k);
        for t in [id, base, word, k, n] {
            TermStore::inspect_sort_with_progress(builder.terms().sort(t), &mut |w, b| {
                owner.admit(w, b).is_ok()
            })
            .map_err(|_| failed())?;
        }
        if builder.terms().sort(k) != &Sort::Int
            || builder.terms().sort(n) != &Sort::Int
            || builder.terms().sort(word) != builder.terms().sort(base)
            || builder.terms().sort(base) != builder.terms().sort(id)
            || !matches!(builder.terms().sort(word), Sort::String | Sort::Seq(_))
            || ((head == "str.power" || inner_head == "str.power")
                && builder.terms().sort(word) != &Sort::String)
        {
            return Err(failed());
        }
        let numeral = |term| -> Result<Option<bool>, TacticFailure> {
            match builder.terms().get(term) {
                TermData::Const(Constant::Int(v)) => {
                    owner
                        .admit(
                            usize::try_from(v.bits().div_ceil(8).max(1)).map_err(|_| failed())?,
                            0,
                        )
                        .map_err(|_| failed())?;
                    Ok(Some(v.is_positive()))
                }
                _ => Ok(None),
            }
        };
        let outer_positive = numeral(n)?;
        // Nonpositive outer powers must become empty before combining with
        // a possibly negative inner exponent.
        if outer_positive == Some(false) {
            return Ok(id);
        }
        if matches!(builder.terms().get(n), TermData::Const(Constant::Int(v)) if v.to_u32() == Some(1))
        {
            return Ok(id);
        }
        if outer_positive.is_none() && numeral(k)? != Some(true) {
            return Ok(id);
        }
        budget.visit(owner)?;
        let product = builder.integer_product(k, n).map_err(|_| failed())?;
        id = builder
            .rebuild_existing(id, &[word, product])
            .map_err(|_| failed())?;
    }
}

fn expand(
    builder: &mut CountedTermBuilder<'_, '_, Borrowed<'_>>,
    id: TermId,
    maximum: u32,
    owner: &dyn TermConstructionAdmission,
) -> Result<TermId, TacticFailure> {
    let TermData::App(Symbol::Named(name), args) = builder.terms().get(id) else {
        return Err(failed());
    };
    let string_only = name == "str.power";
    let [base, count] = args.as_slice() else {
        return Err(failed());
    };
    let (base, count) = (*base, *count);
    for term in [base, count, id] {
        TermStore::inspect_sort_with_progress(builder.terms().sort(term), &mut |work, bytes| {
            owner.admit(work, bytes).is_ok()
        })
        .map_err(|_| failed())?;
    }
    if !matches!(builder.terms().sort(base), Sort::String | Sort::Seq(_))
        || (string_only && builder.terms().sort(base) != &Sort::String)
        || builder.terms().sort(count) != &Sort::Int
        || builder.terms().sort(base) != builder.terms().sort(id)
    {
        return Err(failed());
    }
    match builder.terms().get(base) {
        TermData::Const(Constant::String(value)) if value.is_empty() => return Ok(base),
        TermData::App(Symbol::Named(name), args)
            if name == "seq.empty"
                && args.is_empty()
                && !builder.terms().is_declared_function(name) =>
        {
            return Ok(base)
        }
        _ => {}
    }
    // Count payload inspection before sign/conversion; no BigInt copy.
    let TermData::Const(Constant::Int(value)) = builder.terms().get(count) else {
        return Ok(id);
    };
    owner
        .admit(
            usize::try_from(value.bits().div_ceil(8))
                .map_err(|_| failed())?
                .max(1),
            0,
        )
        .map_err(|_| failed())?;
    if value.is_negative() || value.is_zero() {
        return builder.sequence_empty(base).map_err(|_| failed());
    }
    if value.to_u32() == Some(1) {
        return Ok(base);
    }
    let Some(mut count) = value.to_u32().filter(|n| *n <= maximum) else {
        return Ok(id);
    };
    if matches!(
        builder.terms().get(base),
        TermData::Const(Constant::String(_))
    ) {
        return builder.string_repeat(base, count).map_err(|_| failed());
    }
    // Shared binary concatenation DAG: same word as n-ary expansion, with
    // logarithmic term count and no count-sized argument allocation.
    let mut power = base;
    let mut result = None;
    while count != 0 {
        owner.admit(1, 0).map_err(|_| failed())?;
        if count & 1 != 0 {
            result = Some(match result {
                None => power,
                Some(a) => builder.sequence_concat(a, power).map_err(|_| failed())?,
            });
        }
        count >>= 1;
        if count != 0 {
            power = builder
                .sequence_concat(power, power)
                .map_err(|_| failed())?;
        }
    }
    owner.check().map_err(|_| failed())?;
    result.ok_or_else(failed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant};
    use std::sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    };

    fn owner(work: u64, memory: usize) -> CountedAdmission {
        CountedAdmission::new(
            FiniteAdmissionGrant::new(work, memory),
            None,
            Arc::new(|| false),
        )
        .unwrap()
    }
    fn run(
        store: &mut TermStore,
        root: TermId,
        maximum: u32,
        owner: &dyn TermConstructionAdmission,
    ) -> Result<TermId, TacticFailure> {
        rewrite(store, &[root], maximum, &mut Steps::new(None), owner).map(|v| v[0])
    }
    fn power(store: &mut TermStore, base: TermId, n: i32) -> TermId {
        let n = store.mk_int(n.into());
        let sort = store.sort(base).clone();
        store.mk_app_structural(Symbol::named("seq.power"), [base, n], sort)
    }
    #[test]
    fn nested_powers_combine_before_the_threshold_without_renewing_steps() {
        let mut store = TermStore::new();
        let s = store.mk_var("s", Sort::String);
        let inner = power(&mut store, s, 3);
        let middle = power(&mut store, inner, 2);
        let source = power(&mut store, middle, 3);
        let output = run(&mut store, source, 1, &owner(1 << 20, 16 << 20)).unwrap();
        let TermData::App(Symbol::Named(head), args) = store.get(output) else {
            panic!("power required")
        };
        assert_eq!(head, "seq.power");
        assert_eq!(args[0], s);
        assert!(matches!(store.get(args[1]), TermData::Const(Constant::Int(n)) if n == &18.into()));
        let stopped = rewrite(
            &mut store,
            &[source],
            1,
            &mut Steps::new(Some(1)),
            &owner(1 << 20, 16 << 20),
        );
        assert!(
            stopped.is_err(),
            "nested rewrite must retain the original Steps"
        );
        let negative = power(&mut store, inner, -2);
        let output = run(&mut store, negative, 1, &owner(1 << 20, 16 << 20)).unwrap();
        assert!(matches!(store.get(output), TermData::Const(Constant::String(s)) if s.is_empty()));
    }

    #[test]
    fn nested_symbolic_power_combines_only_with_a_known_positive_factor() {
        let mut store = TermStore::new();
        let s = store.mk_var("s", Sort::String);
        let k = store.mk_var("k", Sort::Int);
        let n = store.mk_var("n", Sort::Int);
        let inner = store.mk_app_structural(Symbol::named("seq.power"), [s, k], Sort::String);
        let source = store.mk_app_structural(Symbol::named("seq.power"), [inner, n], Sort::String);
        assert_eq!(
            run(&mut store, source, 1, &owner(1 << 20, 16 << 20)).unwrap(),
            source
        );
        let inner = power(&mut store, s, 3);
        let source = store.mk_app_structural(Symbol::named("seq.power"), [inner, n], Sort::String);
        let output = run(&mut store, source, 1, &owner(1 << 20, 16 << 20)).unwrap();
        let TermData::App(_, args) = store.get(output) else {
            panic!("power required")
        };
        assert_eq!(args[0], s);
        assert!(
            matches!(store.get(args[1]), TermData::App(Symbol::Named(h), factors) if h == "*" && factors.contains(&n))
        );
        let deep_source = power(&mut store, source, 2);
        let deep_output = run(&mut store, deep_source, 1, &owner(1 << 20, 16 << 20)).unwrap();
        let TermData::App(_, args) = store.get(deep_output) else {
            panic!("power required")
        };
        let TermData::App(_, factors) = store.get(args[1]) else {
            panic!("coefficient required")
        };
        assert_eq!(factors.len(), 2);
        assert_eq!(factors[1], n);
        assert!(
            matches!(store.get(factors[0]), TermData::Const(Constant::Int(value)) if value == &6.into())
        );
        struct View(TermId, TermId, i32);
        impl ay_model_check::ModelView for View {
            fn leaf_value(&self, id: TermId) -> Option<ay_model_check::ModelValue> {
                if id == self.0 {
                    Some(ay_model_check::ModelValue::Str("ab".into()))
                } else if id == self.1 {
                    Some(ay_model_check::ModelValue::Int(self.2.into()))
                } else {
                    None
                }
            }
        }
        for count in [-2, -1, 0, 1, 2, 3] {
            let view = View(s, n, count);
            let evaluator = ay_model_check::Evaluator::new(&store, &view);
            for (term, coefficient) in
                [(source, 3), (output, 3), (deep_source, 6), (deep_output, 6)]
            {
                let actual = evaluator.evaluate(term);
                assert!(
                    matches!(actual, ay_model_check::EvalOutcome::Value(ay_model_check::ModelValue::Str(ref word)) if word == &"ab".repeat(coefficient * usize::try_from(count).unwrap_or(0))),
                    "{count}: {actual:?}"
                );
            }
        }
        store.register_declared_function("*");
        assert!(
            run(&mut store, source, 1, &owner(1 << 20, 16 << 20)).is_err(),
            "generated multiplication may not call a declared UF"
        );
    }
    #[test]
    fn sequence_rewrite_threshold_and_literal_output_are_real() {
        let mut store = TermStore::new();
        let base = store.mk_string("aλ".into());
        let source = power(&mut store, base, 3);
        assert_eq!(
            run(&mut store, source, 2, &owner(1 << 20, 16 << 20)).unwrap(),
            source
        );
        let output = run(&mut store, source, 4, &owner(1 << 20, 16 << 20)).unwrap();
        assert!(matches!(store.get(output), TermData::Const(Constant::String(s)) if s == "aλaλaλ"));
        for n in [-4, 0, 1] {
            let source = power(&mut store, base, n);
            let output = run(&mut store, source, 0, &owner(1 << 20, 16 << 20)).unwrap();
            assert!(
                matches!(store.get(output), TermData::Const(Constant::String(s)) if s == if n == 1 {"aλ"} else {""})
            );
        }
    }
    #[test]
    fn sequence_rewrite_preserves_symbolic_models_inside_predicates() {
        struct View(TermId, String);
        impl ay_model_check::ModelView for View {
            fn leaf_value(&self, id: TermId) -> Option<ay_model_check::ModelValue> {
                (id == self.0).then(|| ay_model_check::ModelValue::Str(self.1.clone()))
            }
        }
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::String);
        let source = power(&mut store, x, 3);
        let target = store.mk_string("ababab".into());
        let root = store.mk_eq(source, target);
        let output = run(&mut store, root, 4, &owner(1 << 20, 16 << 20)).unwrap();
        assert_ne!(root, output);
        for word in ["", "a", "ab", "λ"] {
            let view = View(x, word.into());
            let eval = ay_model_check::Evaluator::new(&store, &view);
            for term in [root, output] {
                let result = eval.evaluate(term);
                assert!(
                    matches!(result, ay_model_check::EvalOutcome::Value(ay_model_check::ModelValue::Bool(v)) if v == (word == "ab")),
                    "{word}: {result:?}"
                );
            }
        }
    }

    #[test]
    fn sequence_rewrite_polymorphic_words_preserve_element_order() {
        struct View(TermId);
        impl ay_model_check::ModelView for View {
            fn leaf_value(&self, id: TermId) -> Option<ay_model_check::ModelValue> {
                use ay_model_check::ModelValue as V;
                (id == self.0).then(|| V::Seq(vec![V::Int(1.into()), V::Int(2.into())]))
            }
        }
        let mut store = TermStore::new();
        let x = store.mk_var("xs", Sort::seq(Sort::Int));
        let source = power(&mut store, x, 3);
        let output = run(&mut store, source, 4, &owner(1 << 20, 16 << 20)).unwrap();
        assert_ne!(source, output);
        let view = View(x);
        let eval = ay_model_check::Evaluator::new(&store, &view);
        for term in [source, output] {
            let result = eval.evaluate(term);
            let ay_model_check::EvalOutcome::Value(ay_model_check::ModelValue::Seq(values)) =
                result
            else {
                panic!("{result:?}")
            };
            assert_eq!(values.len(), 6);
            for (value, expected) in values.iter().zip([1, 2, 1, 2, 1, 2]) {
                assert!(
                    matches!(value, ay_model_check::ModelValue::Int(v) if v == &num_bigint::BigInt::from(expected))
                );
            }
        }
        let source = power(&mut store, x, -1);
        let output = run(&mut store, source, 0, &owner(1 << 20, 16 << 20)).unwrap();
        let eval = ay_model_check::Evaluator::new(&store, &view);
        let result = eval.evaluate(output);
        assert!(
            matches!(result, ay_model_check::EvalOutcome::Value(ay_model_check::ModelValue::Seq(v)) if v.is_empty())
        );
    }
    #[test]
    fn sequence_rewrite_refuses_original_stop_and_large_literal_storage() {
        let mut store = TermStore::new();
        let base = store.mk_string("abcdefghijklmnop".into());
        let source = power(&mut store, base, 1_000_000);
        let memory = owner(1 << 30, 1 << 20);
        let before = store.len();
        assert!(run(&mut store, source, u32::MAX, &memory).is_err());
        assert_eq!(store.len(), before);
        assert_eq!(
            memory.check(),
            Err(ay_core::original_query::CountedAdmissionError::StorageExhausted)
        );
        let stopped = Arc::new(AtomicBool::new(false));
        let flag = stopped.clone();
        let original = CountedAdmission::new(
            FiniteAdmissionGrant::new(1 << 20, 16 << 20),
            None,
            Arc::new(move || flag.load(Ordering::SeqCst)),
        )
        .unwrap();
        stopped.store(true, Ordering::SeqCst);
        assert!(run(&mut store, source, 2, &original).is_err());
        stopped.store(false, Ordering::SeqCst);
        assert!(run(&mut store, source, 2, &original).is_err());
    }

    #[test]
    fn sequence_rewrite_rejects_generated_shadowed_heads_and_bad_sorts() {
        for (sort, head, exponent) in [
            (Sort::String, "str.++", 3),
            (Sort::seq(Sort::Int), "seq.++", 3),
            (Sort::seq(Sort::Int), "seq.empty", 0),
        ] {
            let mut store = TermStore::new();
            let base = store.mk_var("x", sort);
            let source = power(&mut store, base, exponent);
            store.register_declared_function(head);
            assert!(run(&mut store, source, 4, &owner(1 << 20, 16 << 20)).is_err());
        }
        let mut store = TermStore::new();
        let base = store.mk_var("x", Sort::seq(Sort::Int));
        let n = store.mk_int(3.into());
        let malformed =
            store.mk_app_structural(Symbol::named("seq.power"), [base, n], Sort::seq(Sort::Bool));
        assert!(run(&mut store, malformed, 4, &owner(1 << 20, 16 << 20)).is_err());
        let source = power(&mut store, base, 3);
        store.register_declared_function("seq.power");
        assert_eq!(
            run(&mut store, source, 4, &owner(1 << 20, 16 << 20)).unwrap(),
            source
        );
    }
}
