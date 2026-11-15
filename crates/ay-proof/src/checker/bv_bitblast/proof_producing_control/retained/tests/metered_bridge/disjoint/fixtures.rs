// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy, Debug)]
pub(super) enum Route {
    Disjoint,
    Combined,
}

impl Route {
    pub(super) fn roles(self) -> &'static [&'static str] {
        match self {
            Self::Disjoint => &["disjoint_free_offset", "final_clause"],
            Self::Combined => &[
                "disjoint_free_offset",
                "outside_free_offset",
                "final_clause",
            ],
        }
    }

    pub(super) fn frames(self) -> wire::pair::FrameSet {
        match self {
            Self::Disjoint => wire::pair::FrameSet::Disjoint,
            Self::Combined => wire::pair::FrameSet::Combined,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(super) enum Source {
    Valid,
    FalseConclusion,
    MalformedOverwritten,
}

// The source shapes match native disjoint/tests/fixtures.rs; false neighbors
// keep allocation order/IDs but change the final root, not a wire role tag.
pub(super) fn fixture(route: Route, source: Source) -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(9);
    let byte = Sort::bitvec(8);
    let array = Sort::array(word.clone(), byte.clone());
    let a = terms.mk_var("a", word.clone());
    let b = terms.mk_var("b", word.clone());
    let size = terms.mk_bitvec(2.into(), 9);
    let mut before = terms.mk_var("memory", array.clone());
    let good = terms.mk_var("value", byte.clone());
    let first = match source {
        Source::MalformedOverwritten => app(&mut terms, "bvadd", &[good], byte.clone()),
        _ => good,
    };
    let (start, mut guards, outside) = match route {
        Route::Disjoint => {
            let end_a = app(&mut terms, "bvadd", &[a, size], word.clone());
            let end_b = app(&mut terms, "bvadd", &[b, size], word.clone());
            let after_b = app(&mut terms, "bvuge", &[a, end_b], Sort::Bool);
            let after_a = app(&mut terms, "bvuge", &[b, end_a], Sort::Bool);
            let separate = app(&mut terms, "or", &[after_b, after_a], Sort::Bool);
            let bound = terms.mk_bitvec(509.into(), 9);
            let nowrap_a = app(&mut terms, "bvule", &[a, bound], Sort::Bool);
            let nowrap_b = app(&mut terms, "bvule", &[b, bound], Sort::Bool);
            (a, vec![separate, nowrap_a, nowrap_b], None)
        }
        Route::Combined => {
            let start = app(&mut terms, "bvsub", &[a, size], word.clone());
            let guard = app(&mut terms, "bvuge", &[a, size], Sort::Bool);
            let below = app(&mut terms, "bvult", &[b, start], Sort::Bool);
            let above = app(&mut terms, "bvuge", &[b, a], Sort::Bool);
            let outside = app(&mut terms, "or", &[below, above], Sort::Bool);
            let output = terms.mk_var("output", word.clone());
            let extent = terms.mk_bitvec(40.into(), 9);
            let end = app(&mut terms, "bvadd", &[output, extent], word.clone());
            let below = app(&mut terms, "bvule", &[end, start], Sort::Bool);
            let above = app(&mut terms, "bvuge", &[output, a], Sort::Bool);
            let separate = app(&mut terms, "or", &[below, above], Sort::Bool);
            let bound = terms.mk_bitvec(471.into(), 9);
            let nowrap = app(&mut terms, "bvule", &[output, bound], Sort::Bool);
            (
                start,
                vec![separate, nowrap, guard],
                Some((outside, output)),
            )
        }
    };
    let after = app(&mut terms, "store", &[before, start, first], array.clone());
    let mut after = app(&mut terms, "store", &[after, start, good], array.clone());
    if let Some((_, output)) = outside {
        after = app(&mut terms, "store", &[after, output, good], array.clone());
        before = app(&mut terms, "store", &[before, output, good], array);
    }
    let after = app(&mut terms, "select", &[after, b], byte.clone());
    let before = app(&mut terms, "select", &[before, b], byte);
    let equal = app(&mut terms, "=", &[after, before], Sort::Bool);
    let property = match outside {
        Some((outside, _)) => {
            let inside = terms.mk_not_raw(outside);
            app(&mut terms, "or", &[inside, equal], Sort::Bool)
        }
        None => equal,
    };
    let negative = terms.mk_not_raw(property);
    guards.push(match source {
        Source::FalseConclusion => property,
        _ => negative,
    });
    let root = app(&mut terms, "and", &guards, Sort::Bool);
    let clause = terms.mk_not_raw(root);
    assert!(crate::checker::bv_bitblast::disjoint::Shape::recognize(&terms, &[clause]).is_some());
    assert_eq!(
        outside_frame::Shape::recognize(&terms, &[clause],).is_some(),
        matches!(route, Route::Combined),
    );
    (terms, clause)
}
