// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn binary(terms: &TermStore, term: TermId, name: &str) -> Option<[TermId; 2]> {
    terms.entry_stamp(term)?;
    let TermData::App(Symbol::Named(op), args) = terms.get(term) else {
        return None;
    };
    let [a, b] = args.as_slice() else { return None };
    terms.entry_stamp(*a)?;
    terms.entry_stamp(*b)?;
    (op == name).then_some([*a, *b])
}

pub(super) fn flatten(
    terms: &TermStore,
    term: TermId,
    output: &mut Vec<TermId>,
    nodes: &mut usize,
    depth: usize,
) -> Option<()> {
    *nodes = nodes.checked_add(1)?;
    if *nodes > MAX_NODES || depth > MAX_DEPTH {
        return None;
    }
    terms.entry_stamp(term)?;
    if let Some(children) = binary(terms, term, "and") {
        for child in children {
            flatten(terms, child, output, nodes, depth + 1)?;
        }
    } else {
        output.push(term);
    }
    Some(())
}

fn literal(terms: &TermStore, term: TermId, width: u32) -> Option<u128> {
    terms.entry_stamp(term)?;
    let TermData::Const(Constant::BitVec {
        value,
        width: actual,
    }) = terms.get(term)
    else {
        return None;
    };
    (*actual == width).then_some(value.to_u128()?)
}

fn interval(terms: &TermStore, term: TermId, width: u32) -> Option<[TermId; 3]> {
    let (condition, yes, no) = context_conditional(terms, term)?;
    if literal(terms, yes, width)? != 1 || literal(terms, no, width)? != 0 {
        return None;
    }
    let [lower, upper] = binary(terms, condition, "and")?;
    let [start, point] = binary(terms, lower, "bvule")?;
    let [same, end] = binary(terms, upper, "bvult")?;
    (point == same).then_some([start, point, end])
}

pub(super) fn leaf(
    normalizer: &mut Normalizer<'_>,
    eq: TermId,
) -> Option<(IntervalLeaf, TermId, TermId)> {
    let terms = normalizer.terms;
    let (sum, one, width) = equality(terms, &[eq])?;
    if width != normalizer.width || literal(terms, one, width)? != 1 {
        return None;
    }
    let [first_two, middle] = binary(terms, sum, "bvadd")?;
    let [before, after] = binary(terms, first_two, "bvadd")?;
    let [zero, point, start] = interval(terms, before, width)?;
    let [end, same_point, upper] = interval(terms, after, width)?;
    let [same_start, third_point, same_end] = interval(terms, middle, width)?;
    if literal(terms, zero, width)? != 0
        || same_point != point
        || third_point != point
        || same_start != start
        || same_end != end
    {
        return None;
    }
    let point_value = literal(terms, point, width)?;
    let normalized = normalizer.normalize(upper, 0)?;
    if normalized.keys().any(Option::is_some) {
        return None;
    }
    let upper_value = normalized.get(&None).copied().unwrap_or(0);
    if point_value >= upper_value {
        return None;
    }
    Some((
        IntervalLeaf {
            equality: eq,
            sum,
            point,
            upper,
            upper_value,
        },
        start,
        end,
    ))
}
