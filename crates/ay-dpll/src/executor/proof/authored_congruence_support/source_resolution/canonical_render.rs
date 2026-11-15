// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Price the actual root rendering without invoking a subterm override collector.

use super::*;
use crate::executor::proof_trust_surgery_surface_audit::{
    render_roots_have_bounded_depth, render_roots_have_bounded_payload,
};

const MAX_TERMS: usize = 100_000;
const MAX_PAYLOAD_BYTES: usize = 8 * 1024 * 1024;
const MAX_RENDER_WORK: usize = 32 * 1024 * 1024;

/// Payload and exact DAG-depth checks precede recursive formatting. The real
/// printer then meters every copied byte, including repeated shared subterms.
/// A binder is syntax here; rendering it grants no source or proof authority.
pub(super) fn render(
    terms: &TermStore,
    roots: impl IntoIterator<Item = TermId>,
) -> Option<DetHashMap<TermId, String>> {
    let needed = bounded_roots(terms, roots)?;
    ay_proof::format_terms_alethe_with_overrides_bounded(
        terms,
        &needed,
        &DetHashMap::default(),
        u64::try_from(MAX_RENDER_WORK).ok()?,
    )
    .ok()
}

/// One shared actual-work cap covers BOTH effective and canonical batches;
/// neither roots nor the second rendering get an independent fresh allowance.
pub(super) fn render_pair(
    terms: &TermStore,
    roots: impl IntoIterator<Item = TermId>,
    overrides: &DetHashMap<TermId, String>,
) -> Option<(DetHashMap<TermId, String>, DetHashMap<TermId, String>)> {
    let needed = bounded_roots(terms, roots)?;
    ay_proof::format_terms_alethe_with_overrides_and_canonical_bounded(
        terms,
        &needed,
        overrides,
        &needed,
        u64::try_from(MAX_RENDER_WORK).ok()?,
    )
    .ok()
}

fn bounded_roots(
    terms: &TermStore,
    roots: impl IntoIterator<Item = TermId>,
) -> Option<Vec<TermId>> {
    let max_rows = MAX_REACHABLE_AUTHORED_ASSUMES.checked_add(MAX_PROVENANCE_REPAIR_TERMS)?;
    let mut needed = Vec::new();
    let mut seen = DetHashSet::default();
    for (index, root) in roots.into_iter().enumerate() {
        if index >= max_rows {
            return None;
        }
        if seen.insert(root) {
            needed.push(root);
        }
    }
    if !render_roots_have_bounded_depth(terms, &needed, MAX_TERMS, MAX_RENDER_WORK)
        || !render_roots_have_bounded_payload(terms, &needed, MAX_TERMS, MAX_PAYLOAD_BYTES)
    {
        return None;
    }
    Some(needed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{Sort, Symbol};

    #[test]
    fn canonical_render_prices_binders_without_collecting_subterm_overrides() {
        let mut executor = Executor::new();
        executor
            .execute_all(
                &ay_frontend::parse(
                    "(declare-const p Bool) (declare-fun P (Int) Bool) \
             (assert (and p (forall ((x Int)) (P x))))",
                )
                .unwrap(),
            )
            .unwrap();
        let root = executor.ctx.assertions[0];
        assert!(
            proof_surface_syntax::surface_override_collection_work(&executor.ctx.terms, root,)
                .is_none()
        );
        let rendered = render(&executor.ctx.terms, [root]).unwrap();
        assert_eq!(
            rendered[&root],
            ay_proof::format_term_alethe(&executor.ctx.terms, root)
        );
        assert!(rendered[&root].contains("(forall"));
    }

    #[test]
    fn canonical_render_refuses_payload_depth_and_shared_expansion_overflow() {
        let mut terms = TermStore::new();
        let wide = terms.mk_bitvec(0.into(), 9_000_000);
        assert!(render(&terms, [wide]).is_none());
        let seed = terms.mk_var("seed", Sort::Int);
        let mut deep = seed;
        for _ in 0..257 {
            deep = terms.mk_app(Symbol::named("walk"), [deep], Sort::Int);
        }
        assert!(render(&terms, [seed, deep]).is_none());
        let mut doubled = seed;
        for _ in 0..24 {
            doubled = terms.mk_app(Symbol::named("dup"), [doubled, doubled], Sort::Int);
        }
        assert!(render(&terms, [doubled]).is_none());
        assert!(render(&terms, [seed]).is_some());
    }

    #[test]
    fn canonical_render_charges_repeated_input_rows_before_deduplication() {
        let terms = TermStore::new();
        let root = terms.true_term();
        let cap = MAX_REACHABLE_AUTHORED_ASSUMES + MAX_PROVENANCE_REPAIR_TERMS;
        assert!(render(&terms, std::iter::repeat_n(root, cap)).is_some());
        assert!(render(&terms, std::iter::repeat_n(root, cap + 1)).is_none());
    }

    #[test]
    fn canonical_render_prices_constant_array_annotations_before_formatting() {
        let mut terms = TermStore::new();
        let value = terms.mk_var("value", Sort::Int);
        let shallow = terms.mk_app(
            Symbol::named("const-array"),
            [value],
            Sort::array(Sort::Int, Sort::Int),
        );
        assert!(render(&terms, [shallow]).is_some());
        let mut sort = Sort::Int;
        for _ in 0..257 {
            sort = Sort::array(Sort::Int, sort);
        }
        let value = terms.mk_var("deep_value", sort.clone());
        let result_sort = Sort::array(Sort::Int, sort);
        let deep = terms.mk_app(Symbol::named("const-array"), [value], result_sort.clone());
        assert!(!render_roots_have_bounded_payload(
            &terms,
            &[deep],
            MAX_TERMS,
            MAX_PAYLOAD_BYTES
        ));
        assert!(render(&terms, [deep]).is_none());
        // An ordinary application does not print its result sort.
        let ordinary = terms.mk_app(Symbol::named("ordinary"), [value], result_sort);
        assert!(render(&terms, [ordinary]).is_some());
    }
}
