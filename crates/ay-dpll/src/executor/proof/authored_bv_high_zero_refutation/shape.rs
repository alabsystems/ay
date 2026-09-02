// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded structural recognition and raw proof-term builders.

use std::collections::VecDeque;

use ay_core::kani_compat::DetHashMap as HashMap;

use super::*;

pub(super) const MAX_EQUALITY_EDGES: usize = 4_096;
const MAX_ZERO_TEST_WIDTH: u32 = 64;

#[derive(Clone, Copy)]
pub(super) struct HighZeroTarget {
    pub(super) conjunct_index: usize,
    pub(super) disequality: TermId,
    pub(super) equality: TermId,
    pub(super) subject: TermId,
    pub(super) zero: TermId,
    pub(super) extended: TermId,
    pub(super) multiplier: TermId,
    pub(super) product: TermId,
    pub(super) extracted: TermId,
    pub(super) width: u32,
}

#[derive(Clone, Copy)]
pub(super) struct UltOneFact {
    pub(super) conjunct_index: usize,
    pub(super) literal: TermId,
    pub(super) subject: TermId,
    pub(super) width: u32,
}

#[derive(Clone, Copy)]
pub(super) struct VarEquality {
    pub(super) conjunct_index: usize,
    pub(super) equality: TermId,
    pub(super) left: TermId,
    pub(super) right: TermId,
}

#[derive(Clone, Copy)]
pub(super) struct PathHop {
    pub(super) edge_index: usize,
    pub(super) from: TermId,
    pub(super) to: TermId,
}

pub(super) fn decode_high_zero_target(
    terms: &TermStore,
    literal: TermId,
    conjunct_index: usize,
) -> Option<HighZeroTarget> {
    let TermData::Not(equality) = terms.get(literal) else {
        return None;
    };
    let equality = *equality;
    let TermData::App(Symbol::Named(eq), equality_args) = terms.get(equality) else {
        return None;
    };
    let [extracted, zero] = equality_args.as_slice() else {
        return None;
    };
    if eq != "=" {
        return None;
    }
    let (extracted, zero) = (*extracted, *zero);
    let width = terms.sort(extracted).bitvec_width()?;
    if width == 0
        || width > MAX_ZERO_TEST_WIDTH
        || terms.sort(zero) != &Sort::bitvec(width)
        || !is_bv_literal(terms, zero, 0, width)
    {
        return None;
    }
    let double_width = width.checked_mul(2)?;

    let TermData::App(Symbol::Indexed(extract, indices), extract_args) = terms.get(extracted)
    else {
        return None;
    };
    let [product] = extract_args.as_slice() else {
        return None;
    };
    if extract != "extract"
        || indices.as_slice() != [double_width.checked_sub(1)?, width]
        || terms.sort(*product) != &Sort::bitvec(double_width)
    {
        return None;
    }
    let product = *product;

    let TermData::App(Symbol::Named(mul), mul_args) = terms.get(product) else {
        return None;
    };
    let [extended, multiplier] = mul_args.as_slice() else {
        return None;
    };
    if mul != "bvmul" || terms.sort(*multiplier) != &Sort::bitvec(double_width) {
        return None;
    }
    let (extended, multiplier) = (*extended, *multiplier);
    if !matches!(terms.get(multiplier), TermData::Const(Constant::BitVec { width, .. }) if *width == double_width)
    {
        return None;
    }

    let TermData::App(Symbol::Indexed(extend, extend_indices), extend_args) = terms.get(extended)
    else {
        return None;
    };
    let [subject] = extend_args.as_slice() else {
        return None;
    };
    let subject = *subject;
    if extend != "zero_extend"
        || extend_indices.as_slice() != [width]
        || terms.sort(subject) != &Sort::bitvec(width)
        || terms.sort(extended) != &Sort::bitvec(double_width)
        || !matches!(terms.get(subject), TermData::Var(_, _))
    {
        return None;
    }

    Some(HighZeroTarget {
        conjunct_index,
        disequality: literal,
        equality,
        subject,
        zero,
        extended,
        multiplier,
        product,
        extracted,
        width,
    })
}

pub(super) fn decode_ult_one_fact(
    terms: &TermStore,
    literal: TermId,
    conjunct_index: usize,
) -> Option<UltOneFact> {
    let TermData::App(Symbol::Named(operator), args) = terms.get(literal) else {
        return None;
    };
    let [subject, one] = args.as_slice() else {
        return None;
    };
    let (subject, one) = (*subject, *one);
    let width = terms.sort(subject).bitvec_width()?;
    if operator != "bvult"
        || width == 0
        || width > MAX_ZERO_TEST_WIDTH
        || !matches!(terms.get(subject), TermData::Var(_, _))
        || !is_bv_literal(terms, one, 1, width)
    {
        return None;
    }
    Some(UltOneFact {
        conjunct_index,
        literal,
        subject,
        width,
    })
}

pub(super) fn decode_var_equality(
    terms: &TermStore,
    equality: TermId,
    conjunct_index: usize,
) -> Option<VarEquality> {
    let TermData::App(Symbol::Named(operator), args) = terms.get(equality) else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    let (left, right) = (*left, *right);
    if operator != "="
        || left == right
        || !matches!(terms.get(left), TermData::Var(_, _))
        || !matches!(terms.get(right), TermData::Var(_, _))
        || !matches!(terms.sort(left), Sort::BitVec(_))
        || !matches!(terms.sort(right), Sort::BitVec(_))
        || terms.sort(left) != terms.sort(right)
    {
        return None;
    }
    Some(VarEquality {
        conjunct_index,
        equality,
        left,
        right,
    })
}

pub(super) fn equality_path(
    edges: &[VarEquality],
    start: TermId,
    goal: TermId,
    edge_visits_remaining: &mut usize,
) -> Option<Vec<PathHop>> {
    if start == goal {
        return Some(Vec::new());
    }
    let mut parent: HashMap<TermId, (TermId, usize)> = HashMap::default();
    let mut queue = VecDeque::new();
    parent.insert(start, (start, usize::MAX));
    queue.push_back(start);
    while let Some(current) = queue.pop_front() {
        for (edge_index, edge) in edges.iter().enumerate() {
            *edge_visits_remaining = edge_visits_remaining.checked_sub(1)?;
            let next = if edge.left == current {
                edge.right
            } else if edge.right == current {
                edge.left
            } else {
                continue;
            };
            if parent.contains_key(&next) {
                continue;
            }
            parent.insert(next, (current, edge_index));
            if next == goal {
                break;
            }
            queue.push_back(next);
        }
        if parent.contains_key(&goal) {
            break;
        }
    }
    if !parent.contains_key(&goal) {
        return None;
    }
    let mut reversed = Vec::new();
    let mut current = goal;
    while current != start {
        let (previous, edge_index) = *parent.get(&current)?;
        reversed.push(PathHop {
            edge_index,
            from: previous,
            to: current,
        });
        current = previous;
    }
    reversed.reverse();
    Some(reversed)
}

pub(super) fn emit_conjunct_unit(
    terms: &mut TermStore,
    proof: &mut Proof,
    root: TermId,
    root_assume: ProofId,
    conjuncts: &[TermId],
    index: usize,
) -> Option<ProofId> {
    let conjunct = *conjuncts.get(index)?;
    let index = u32::try_from(index).ok()?;
    let not_root = raw_not(terms, root)?;
    let selected = proof.add_rule_step(
        AletheRule::AndPos(index),
        vec![not_root, conjunct],
        Vec::new(),
        vec![root],
    );
    Some(proof.add_resolution(vec![conjunct], root, selected, root_assume))
}

pub(super) fn raw_not(terms: &mut TermStore, term: TermId) -> Option<TermId> {
    let negated = terms.mk_not_raw(term);
    matches!(terms.get(negated), TermData::Not(inner) if *inner == term).then_some(negated)
}

pub(super) fn raw_equality(terms: &mut TermStore, left: TermId, right: TermId) -> Option<TermId> {
    if terms.sort(left) != terms.sort(right) {
        return None;
    }
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    matches!(
        terms.get(equality),
        TermData::App(Symbol::Named(operator), args)
            if operator == "=" && args.as_slice() == [left, right]
    )
    .then_some(equality)
}

pub(super) fn raw_application(
    terms: &mut TermStore,
    symbol: Symbol,
    args: &[TermId],
    sort: Sort,
) -> Option<TermId> {
    let term = terms.mk_app(symbol.clone(), args, sort.clone());
    matches!(
        terms.get(term),
        TermData::App(actual_symbol, actual_args)
            if *actual_symbol == symbol && actual_args.as_slice() == args && terms.sort(term) == &sort
    )
    .then_some(term)
}

fn is_bv_literal(terms: &TermStore, term: TermId, expected: u8, width: u32) -> bool {
    matches!(
        terms.get(term),
        TermData::Const(Constant::BitVec {
            value,
            width: literal_width,
        }) if *literal_width == width && *value == BigInt::from(expected)
    ) && terms.sort(term) == &Sort::bitvec(width)
}
