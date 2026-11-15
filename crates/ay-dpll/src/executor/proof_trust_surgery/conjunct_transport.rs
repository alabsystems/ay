// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked transport of an authored conjunct onto its elaborated conjunct.
//!
//! Elaboration folds closed subterms of an authored conjunct (`(= 2 0)` to
//! `false`, `(div (- 4 (mod 4 2)) 2)` to `2`), turns `(= p false)` into
//! `(not p)`, and drops disjuncts that fold to `false`. The elaborated
//! conjunction therefore no longer contains the authored conjunct, while
//! the exported proof extracts the elaborated one. These plans derive the
//! unit `(cl C)` for the elaborated conjunct `C` from the unit `(cl R)` for
//! the exact raw authored conjunct `R`, using only rules the strict checker
//! re-validates: `evaluate` for a closed subterm, `cong` above it,
//! `equiv_pos2` to move a unit across a proved equality, `false`, `or`, and
//! `resolution`. Anything else declines at planning time.

use super::*;

/// Upper bound on plan nodes, so a pathological conjunct cannot turn
/// planning into the proof's cost centre.
const MAX_TRANSPORT_NODES: usize = 256;

/// Proves `(= raw canonical)` for two distinct terms.
#[derive(Clone, Debug)]
pub(in crate::executor) enum EqualityPlan {
    /// `raw` is closed and evaluates to the constant `value`.
    Evaluate { raw: TermId, value: TermId },
    /// Integer terms whose difference is identically zero (a
    /// `LinearIdentity` lemma, `poly_simp` on the wire).
    LinearIdentity { raw: TermId, canonical: TermId },
    /// `raw` is `(bv2nat|bv2int (bvand ((_ int2bv w) x) 2^k-1))` and
    /// `canonical` is `(mod x 2^k)`, the residue `mk_bv2nat` elaborates it
    /// to: a `bv_lia_tautology` whose strict validator matches the exact
    /// identity (`ay-proof` `bv_lia_query_masked_residue`).
    MaskedResidue { raw: TermId, canonical: TermId },
    /// Same head and arity; each differing argument pair has its own plan.
    Congruence {
        raw: TermId,
        canonical: TermId,
        arguments: Vec<EqualityPlan>,
    },
}

impl EqualityPlan {
    fn raw(&self) -> TermId {
        match self {
            Self::Evaluate { raw, .. }
            | Self::LinearIdentity { raw, .. }
            | Self::MaskedResidue { raw, .. }
            | Self::Congruence { raw, .. } => *raw,
        }
    }

    fn canonical(&self) -> TermId {
        match self {
            Self::Evaluate { value, .. } => *value,
            Self::LinearIdentity { canonical, .. }
            | Self::MaskedResidue { canonical, .. }
            | Self::Congruence { canonical, .. } => *canonical,
        }
    }

    fn nodes(&self) -> usize {
        match self {
            Self::Evaluate { .. } | Self::LinearIdentity { .. } => 1,
            Self::MaskedResidue { .. } => 5,
            Self::Congruence { arguments, .. } => {
                1 + arguments.iter().map(Self::nodes).sum::<usize>()
            }
        }
    }
}

/// One node of a lifted `ite` tree.
#[derive(Clone, Debug)]
pub(in crate::executor) enum IteShape {
    /// The raw leaf value `value`; the canonical leaf is `literal`, equal to
    /// `(= k value)` or reached from it by `bridge` on the value.
    Leaf {
        value: TermId,
        literal: TermId,
        bridge: Option<EqualityPlan>,
    },
    /// The raw term `ite_term = (ite condition x y)` lifted to the canonical
    /// `(ite lifted_condition then_shape else_shape)`. When `negated`, the
    /// raw condition is `(not atom)`, `lifted_condition` corresponds to
    /// `atom`, and the branches are swapped. Condition literals are moved
    /// with one-row Farkas lemmas, so both conditions must be arithmetic
    /// comparisons.
    Node {
        ite_term: TermId,
        condition: TermId,
        negated: bool,
        lifted_condition: TermId,
        canonical: TermId,
        then_shape: Box<IteShape>,
        else_shape: Box<IteShape>,
    },
}

impl IteShape {
    fn nodes(&self) -> usize {
        match self {
            Self::Leaf { bridge, .. } => 4 + bridge.as_ref().map_or(0, EqualityPlan::nodes),
            Self::Node {
                then_shape,
                else_shape,
                ..
            } => 24 + then_shape.nodes() + else_shape.nodes(),
        }
    }

    fn canonical(&self) -> TermId {
        match self {
            Self::Leaf { literal, .. } => *literal,
            Self::Node { canonical, .. } => *canonical,
        }
    }
}

/// Why a formula is `false`.
#[derive(Clone, Debug)]
pub(in crate::executor) enum FalseRefutation {
    /// The formula is literally `false`.
    Literal,
    /// A checked equality `(= formula false)`.
    Folded(EqualityPlan),
    /// The formula is an `and` whose conjunct at `index` is false.
    FalseConjunct {
        index: u32,
        conjunct: TermId,
        inner: Box<FalseRefutation>,
    },
}

impl FalseRefutation {
    fn nodes(&self) -> usize {
        match self {
            Self::Literal => 1,
            Self::Folded(plan) => 3 + plan.nodes(),
            Self::FalseConjunct { inner, .. } => 2 + inner.nodes(),
        }
    }
}

/// One step from an authored conjunction towards a flattened conjunct.
#[derive(Clone, Debug)]
pub(in crate::executor) enum FlattenStep {
    /// Project the operand at this index of an `and`.
    AndPos(u32),
    /// Resolve away every disjunct of an `or` but `kept`.
    Prune {
        disjuncts: Vec<TermId>,
        kept: usize,
        falsified: Vec<(usize, FalseRefutation)>,
    },
}

/// How one conjunct of a flat canonical conjunction is reached from a nested
/// raw conjunction.
#[derive(Clone, Debug)]
pub(in crate::executor) struct FlattenSource {
    path: Vec<FlattenStep>,
    leaf: TermId,
    transport: Option<Box<TransportPlan>>,
}

/// Relates one literal to another inside a clause.
#[derive(Clone, Copy, Debug)]
pub(in crate::executor) enum LiteralBridge {
    /// A one-row Farkas lemma `(cl to (not from))`.
    Farkas,
    /// A top-level binary-equality reorientation.
    EqualityFlip,
}

/// Derives the unit `(cl canonical)` from the unit `(cl raw)`.
#[derive(Clone, Debug)]
pub(in crate::executor) enum TransportPlan {
    /// `(= raw canonical)` is proved directly.
    Equality(EqualityPlan),
    /// `raw` is `(= p q)` with `q` equal to `false` (by `folded`, or
    /// literally when `folded` is `None`); `canonical` is `(not p)`.
    EqualsFalse {
        p: TermId,
        folded: Option<EqualityPlan>,
    },
    /// `raw` is `(=> p q)` with `q` equal to `false` (by `folded`, or
    /// literally when `folded` is `None`); `canonical` is `(not p)`.
    ImpliesFalse {
        p: TermId,
        q: TermId,
        refutation: FalseRefutation,
    },
    /// `raw` is a (possibly nested) conjunction whose disjunctive operands
    /// may prune to one branch; `canonical` is a flat conjunction each of
    /// whose conjuncts is reached from a raw leaf along `sources[i]`.
    AndFlatten { sources: Vec<FlattenSource> },
    /// `raw` and `canonical` are linear-arithmetic literals related by one
    /// independently verified `[1, 1]` Farkas lemma `(cl canonical (not raw))`
    /// (an argument-swapped or normalized comparison).
    Farkas,
    /// `canonical` is `raw` with its top-level binary equality reoriented
    /// (possibly under one `not`): one certified `eq_symmetric` bridge.
    EqualityFlip,
    /// `raw` is `(= k T)` for a term-level `ite` tree `T`, and `canonical`
    /// is the formula-level tree `lift(k, T)`: see [`IteShape`]. Derived
    /// through `ite_intro`, `ite1`/`ite2`, `eq_transitive`, one-row Farkas
    /// condition bridges and `ite_neg1`/`ite_neg2`.
    IteTree { k: TermId, shape: IteShape },
    /// `raw` is `(or r_0 .. r_n)` and `canonical` is `(or c_0 .. c_n)`, both
    /// with pairwise-distinct disjuncts, and `pairs[j] = (i, bridge)` maps
    /// `c_j` to a distinct `r_i` that is identical (`None`) or related by a
    /// one-literal bridge.
    DisjunctionPermutation {
        raw_disjuncts: Vec<TermId>,
        canonical_disjuncts: Vec<TermId>,
        pairs: Vec<(usize, Option<LiteralBridge>)>,
    },
    /// `raw` is `(or d_0 .. d_n)` with pairwise-distinct disjuncts, every
    /// disjunct but `kept` equal to `false`, and `d_kept` transported onto
    /// `canonical` by `rest` (or identical to it when `rest` is `None`).
    DisjunctionPrune {
        disjuncts: Vec<TermId>,
        kept: usize,
        falsified: Vec<(usize, FalseRefutation)>,
        rest: Option<Box<TransportPlan>>,
    },
}

impl TransportPlan {
    pub(super) fn nodes(&self) -> usize {
        match self {
            Self::Equality(plan) => plan.nodes(),
            Self::EqualsFalse { folded, .. } => 3 + folded.as_ref().map_or(0, EqualityPlan::nodes),
            Self::IteTree { shape, .. } => shape.nodes(),
            Self::Farkas => 2,
            Self::ImpliesFalse { refutation, .. } => 5 + refutation.nodes(),
            Self::AndFlatten { sources } => sources
                .iter()
                .map(|source| {
                    3 * source.path.len()
                        + 2
                        + source.transport.as_ref().map_or(0, |plan| plan.nodes())
                })
                .sum(),
            Self::DisjunctionPermutation { pairs, .. } => 8 * pairs.len() + 2,
            Self::EqualityFlip => 5,
            Self::DisjunctionPrune {
                disjuncts,
                falsified,
                rest,
                ..
            } => {
                disjuncts.len()
                    + falsified
                        .iter()
                        .map(|(_, refutation)| 2 + refutation.nodes())
                        .sum::<usize>()
                    + rest.as_ref().map_or(0, |plan| plan.nodes())
            }
        }
    }
}

/// `raw` and `canonical` are the same binary equality with its two operands
/// swapped, optionally both under one `not`.
pub(super) fn is_top_level_equality_flip(
    terms: &ay_core::TermStore,
    raw: TermId,
    canonical: TermId,
) -> bool {
    let (raw, canonical) = match (terms.get(raw), terms.get(canonical)) {
        (TermData::Not(raw), TermData::Not(canonical)) => (*raw, *canonical),
        _ => (raw, canonical),
    };
    matches!(
        (terms.get(raw), terms.get(canonical)),
        (
            TermData::App(Symbol::Named(raw_op), raw_args),
            TermData::App(Symbol::Named(canonical_op), canonical_args),
        ) if raw_op == "="
            && canonical_op == "="
            && raw_args.len() == 2
            && canonical_args.len() == 2
            && raw_args[0] == canonical_args[1]
            && raw_args[1] == canonical_args[0]
            && raw_args[0] != raw_args[1]
    )
}

/// A (possibly negated) binary `<`, `<=`, `>`, `>=` over Int or Real.
fn is_arithmetic_comparison_literal(terms: &ay_core::TermStore, literal: TermId) -> bool {
    let atom = atom_of(terms, literal);
    matches!(
        terms.get(atom),
        TermData::App(Symbol::Named(op), args)
            if matches!(op.as_str(), "<" | "<=" | ">" | ">=")
                && args.len() == 2
                && matches!(terms.sort(args[0]), Sort::Int | Sort::Real)
    )
}

/// Congruence head of a term, for the same-head test.
fn congruence_parts(terms: &ay_core::TermStore, term: TermId) -> Option<(u8, Symbol, Vec<TermId>)> {
    match terms.get(term) {
        TermData::App(symbol, arguments) => Some((0, symbol.clone(), arguments.clone())),
        TermData::Not(inner) => Some((1, Symbol::named("not"), vec![*inner])),
        TermData::Ite(condition, then_branch, else_branch) => Some((
            2,
            Symbol::named("ite"),
            vec![*condition, *then_branch, *else_branch],
        )),
        _ => None,
    }
}

impl Executor {
    /// Plan `(= raw canonical)`; `Ok(None)` when the terms are identical.
    fn plan_conjunct_equality(
        &mut self,
        raw: TermId,
        canonical: TermId,
        nodes: &mut usize,
    ) -> Result<Option<EqualityPlan>, ()> {
        if raw == canonical {
            return Ok(None);
        }
        *nodes += 1;
        if *nodes > MAX_TRANSPORT_NODES
            || self.ctx.terms.sort(raw) != self.ctx.terms.sort(canonical)
        {
            return Err(());
        }
        if matches!(self.ctx.terms.get(canonical), TermData::Const(_)) {
            let equality = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [raw, canonical], Sort::Bool);
            if ay_proof::recognize_ground_evaluate(&self.ctx.terms, equality) {
                return Ok(Some(EqualityPlan::Evaluate {
                    raw,
                    value: canonical,
                }));
            }
            return Err(());
        }
        if matches!(self.ctx.terms.sort(canonical), Sort::Int) {
            let equality = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [raw, canonical], Sort::Bool);
            if ay_core::proof_validation::recognize_lia_linear_identity(
                &self.ctx.terms,
                &[equality],
            ) {
                return Ok(Some(EqualityPlan::LinearIdentity { raw, canonical }));
            }
            if self.masked_residue_equality_is_checkable(raw, canonical) {
                return Ok(Some(EqualityPlan::MaskedResidue { raw, canonical }));
            }
        }
        let (Some((raw_kind, raw_head, raw_arguments)), Some((kind, head, arguments))) = (
            congruence_parts(&self.ctx.terms, raw),
            congruence_parts(&self.ctx.terms, canonical),
        ) else {
            return Err(());
        };
        if raw_kind != kind || raw_head != head || raw_arguments.len() != arguments.len() {
            return Err(());
        }
        let mut planned = Vec::new();
        for (&raw_argument, &argument) in raw_arguments.iter().zip(arguments.iter()) {
            if let Some(plan) = self.plan_conjunct_equality(raw_argument, argument, nodes)? {
                planned.push(plan);
            }
        }
        if planned.is_empty() {
            return Err(());
        }
        Ok(Some(EqualityPlan::Congruence {
            raw,
            canonical,
            arguments: planned,
        }))
    }

    /// `true` when `term` is literally `false`, `Some(plan)` when it folds to
    /// it by a checked equality.
    fn plan_folds_to_false(
        &mut self,
        term: TermId,
        nodes: &mut usize,
    ) -> Result<Option<EqualityPlan>, ()> {
        let false_term = self.ctx.terms.false_term();
        match self.plan_conjunct_equality(term, false_term, nodes)? {
            None => Ok(None),
            Some(plan) => Ok(Some(plan)),
        }
    }

    /// Plan why `term` is `false`.
    fn plan_refutation(&mut self, term: TermId, nodes: &mut usize) -> Option<FalseRefutation> {
        *nodes += 1;
        if *nodes > MAX_TRANSPORT_NODES {
            return None;
        }
        if term == self.ctx.terms.false_term() {
            return Some(FalseRefutation::Literal);
        }
        if let TermData::App(Symbol::Named(op), conjuncts) = self.ctx.terms.get(term).clone() {
            if op == "and" {
                for (index, conjunct) in conjuncts.into_iter().enumerate() {
                    if let Some(inner) = self.plan_refutation(conjunct, nodes) {
                        return Some(FalseRefutation::FalseConjunct {
                            index: u32::try_from(index).ok()?,
                            conjunct,
                            inner: Box::new(inner),
                        });
                    }
                }
                return None;
            }
        }
        match self.plan_folds_to_false(term, nodes) {
            Ok(Some(plan)) => Some(FalseRefutation::Folded(plan)),
            _ => None,
        }
    }

    /// Collect every raw leaf of the conjunction `raw`, descending through
    /// nested `and`s and through `or`s whose disjuncts all refute but one.
    fn collect_flatten_leaves(
        &mut self,
        raw: TermId,
        path: &mut Vec<FlattenStep>,
        leaves: &mut Vec<(Vec<FlattenStep>, TermId)>,
        nodes: &mut usize,
    ) -> Option<()> {
        *nodes += 1;
        if *nodes > MAX_TRANSPORT_NODES {
            return None;
        }
        match self.ctx.terms.get(raw).clone() {
            TermData::App(Symbol::Named(op), operands) if op == "and" => {
                for (index, operand) in operands.into_iter().enumerate() {
                    path.push(FlattenStep::AndPos(u32::try_from(index).ok()?));
                    self.collect_flatten_leaves(operand, path, leaves, nodes)?;
                    path.pop();
                }
            }
            TermData::App(Symbol::Named(op), disjuncts) if op == "or" && disjuncts.len() >= 2 => {
                let mut kept = None;
                let mut falsified = Vec::new();
                for (index, &disjunct) in disjuncts.iter().enumerate() {
                    match self.plan_refutation(disjunct, nodes) {
                        Some(refutation) => falsified.push((index, refutation)),
                        None if kept.is_none() => kept = Some(index),
                        None => {
                            kept = None;
                            falsified.clear();
                            break;
                        }
                    }
                }
                let mut distinct = disjuncts.clone();
                distinct.sort_unstable();
                distinct.dedup();
                match kept {
                    Some(kept) if !falsified.is_empty() && distinct.len() == disjuncts.len() => {
                        let target = disjuncts[kept];
                        path.push(FlattenStep::Prune {
                            disjuncts,
                            kept,
                            falsified,
                        });
                        self.collect_flatten_leaves(target, path, leaves, nodes)?;
                        path.pop();
                    }
                    _ => leaves.push((path.clone(), raw)),
                }
            }
            _ => leaves.push((path.clone(), raw)),
        }
        Some(())
    }

    /// Plan [`TransportPlan::AndFlatten`].
    fn plan_and_flatten(
        &mut self,
        raw: TermId,
        canonical: TermId,
        nodes: &mut usize,
    ) -> Option<TransportPlan> {
        let TermData::App(Symbol::Named(op), conjuncts) = self.ctx.terms.get(canonical).clone()
        else {
            return None;
        };
        if op != "and" || conjuncts.len() < 2 {
            return None;
        }
        let mut leaves = Vec::new();
        self.collect_flatten_leaves(raw, &mut Vec::new(), &mut leaves, nodes)?;
        let mut sources = Vec::with_capacity(conjuncts.len());
        for conjunct in conjuncts {
            if let Some((path, leaf)) = leaves.iter().find(|(_, leaf)| *leaf == conjunct) {
                sources.push(FlattenSource {
                    path: path.clone(),
                    leaf: *leaf,
                    transport: None,
                });
                continue;
            }
            let mut found = None;
            for (path, leaf) in &leaves {
                if let Some(plan) = self.plan_conjunct_transport_bounded(*leaf, conjunct, nodes) {
                    found = Some(FlattenSource {
                        path: path.clone(),
                        leaf: *leaf,
                        transport: Some(Box::new(plan)),
                    });
                    break;
                }
            }
            sources.push(found?);
        }
        Some(TransportPlan::AndFlatten { sources })
    }

    /// Plan the transport of the unit `(cl raw)` onto `(cl canonical)` for
    /// two distinct terms, or `None` when no checked transport exists.
    pub(in crate::executor) fn plan_conjunct_transport(
        &mut self,
        raw: TermId,
        canonical: TermId,
    ) -> Option<TransportPlan> {
        let mut nodes = 0usize;
        self.plan_conjunct_transport_bounded(raw, canonical, &mut nodes)
    }

    fn plan_conjunct_transport_bounded(
        &mut self,
        raw: TermId,
        canonical: TermId,
        nodes: &mut usize,
    ) -> Option<TransportPlan> {
        if raw == canonical {
            return None;
        }
        if let Ok(Some(plan)) = self.plan_conjunct_equality(raw, canonical, nodes) {
            return Some(TransportPlan::Equality(plan));
        }
        if is_top_level_equality_flip(&self.ctx.terms, raw, canonical) {
            return Some(TransportPlan::EqualityFlip);
        }
        if is_arithmetic_comparison_literal(&self.ctx.terms, raw)
            && is_arithmetic_comparison_literal(&self.ctx.terms, canonical)
        {
            let raw_complement = complement_of(&mut self.ctx.terms, raw);
            if self.pair_lemma_valid(canonical, raw_complement) {
                return Some(TransportPlan::Farkas);
            }
        }
        let raw_data = self.ctx.terms.get(raw).clone();
        let canonical_data = self.ctx.terms.get(canonical).clone();
        match (raw_data, canonical_data) {
            (TermData::App(Symbol::Named(op), arguments), TermData::Not(negated))
                if op == "=" && arguments.len() == 2 && arguments[0] == negated =>
            {
                if self.ctx.terms.mk_not_raw(negated) != canonical {
                    return None;
                }
                let folded = self.plan_folds_to_false(arguments[1], nodes).ok()?;
                Some(TransportPlan::EqualsFalse { p: negated, folded })
            }
            (TermData::App(Symbol::Named(op), arguments), TermData::Not(negated))
                if op == "=>" && arguments.len() == 2 && arguments[0] == negated =>
            {
                if self.ctx.terms.mk_not_raw(negated) != canonical {
                    return None;
                }
                let refutation = self.plan_refutation(arguments[1], nodes)?;
                Some(TransportPlan::ImpliesFalse {
                    p: negated,
                    q: arguments[1],
                    refutation,
                })
            }
            (TermData::App(Symbol::Named(op), sides), TermData::Ite(..))
                if op == "=" && sides.len() == 2 =>
            {
                let (k, ite_term) = (sides[0], sides[1]);
                if !matches!(self.ctx.terms.get(ite_term), TermData::Ite(..)) {
                    return None;
                }
                let shape = self.plan_ite_shape(raw, k, ite_term, canonical, nodes)?;
                Some(TransportPlan::IteTree { k, shape })
            }
            (
                TermData::App(Symbol::Named(op), raw_disjuncts),
                TermData::App(Symbol::Named(canonical_op), canonical_disjuncts),
            ) if op == "or"
                && canonical_op == "or"
                && raw_disjuncts.len() >= 2
                && raw_disjuncts.len() == canonical_disjuncts.len()
                && self
                    .plan_disjunction_permutation(&raw_disjuncts, &canonical_disjuncts)
                    .is_some() =>
            {
                let pairs =
                    self.plan_disjunction_permutation(&raw_disjuncts, &canonical_disjuncts)?;
                Some(TransportPlan::DisjunctionPermutation {
                    raw_disjuncts,
                    canonical_disjuncts,
                    pairs,
                })
            }
            (TermData::App(Symbol::Named(op), disjuncts), _)
                if op == "or" && disjuncts.len() >= 2 =>
            {
                let mut distinct = disjuncts.clone();
                distinct.sort_unstable();
                distinct.dedup();
                if distinct.len() != disjuncts.len() {
                    return None;
                }
                let mut kept = None;
                let mut falsified = Vec::with_capacity(disjuncts.len() - 1);
                for (index, &disjunct) in disjuncts.iter().enumerate() {
                    match self.plan_refutation(disjunct, nodes) {
                        Some(refutation) => falsified.push((index, refutation)),
                        None if kept.is_none() => kept = Some(index),
                        None => return None,
                    }
                }
                let kept = kept?;
                let rest = if disjuncts[kept] == canonical {
                    None
                } else {
                    Some(Box::new(self.plan_conjunct_transport_bounded(
                        disjuncts[kept],
                        canonical,
                        nodes,
                    )?))
                };
                Some(TransportPlan::DisjunctionPrune {
                    disjuncts,
                    kept,
                    falsified,
                    rest,
                })
            }
            (TermData::App(Symbol::Named(op), _), _) if op == "and" => {
                self.plan_and_flatten(raw, canonical, nodes)
            }
            _ => None,
        }
        .filter(|plan| plan.nodes() <= MAX_TRANSPORT_NODES)
    }

    /// A one-literal bridge from `from` to `to`, when one is checkable.
    fn plan_transport_literal_bridge(&mut self, from: TermId, to: TermId) -> Option<LiteralBridge> {
        if is_top_level_equality_flip(&self.ctx.terms, from, to) {
            return Some(LiteralBridge::EqualityFlip);
        }
        if is_arithmetic_comparison_literal(&self.ctx.terms, from)
            && is_arithmetic_comparison_literal(&self.ctx.terms, to)
        {
            let complement = complement_of(&mut self.ctx.terms, from);
            if self.pair_lemma_valid(to, complement) {
                return Some(LiteralBridge::Farkas);
            }
        }
        None
    }

    /// Match every canonical disjunct to a distinct raw disjunct, exact
    /// matches first. Both sides must be duplicate-free.
    fn plan_disjunction_permutation(
        &mut self,
        raw: &[TermId],
        canonical: &[TermId],
    ) -> Option<Vec<(usize, Option<LiteralBridge>)>> {
        let distinct = |terms: &[TermId]| {
            let mut sorted = terms.to_vec();
            sorted.sort_unstable();
            sorted.dedup();
            sorted.len() == terms.len()
        };
        if !distinct(raw) || !distinct(canonical) || raw == canonical {
            return None;
        }
        let mut used = vec![false; raw.len()];
        let mut pairs: Vec<Option<(usize, Option<LiteralBridge>)>> = vec![None; canonical.len()];
        for (j, &target) in canonical.iter().enumerate() {
            if let Some(i) = raw.iter().position(|&source| source == target) {
                used[i] = true;
                pairs[j] = Some((i, None));
            }
        }
        for (j, &target) in canonical.iter().enumerate() {
            if pairs[j].is_some() {
                continue;
            }
            let mut found = None;
            for (i, &source) in raw.iter().enumerate() {
                if used[i] {
                    continue;
                }
                if let Some(bridge) = self.plan_transport_literal_bridge(source, target) {
                    found = Some((i, Some(bridge)));
                    break;
                }
            }
            let (i, bridge) = found?;
            used[i] = true;
            pairs[j] = Some((i, bridge));
        }
        pairs.into_iter().collect()
    }

    /// Emit the proof of `(= raw canonical)`; returns the step and the
    /// equality term it concludes.
    fn emit_conjunct_equality(
        &mut self,
        proof: &mut Proof,
        plan: &EqualityPlan,
    ) -> (ProofId, TermId) {
        let equality = self.ctx.terms.mk_app(
            Symbol::named("="),
            [plan.raw(), plan.canonical()],
            Sort::Bool,
        );
        let step = match plan {
            EqualityPlan::Evaluate { .. } => {
                proof.add_rule_step(AletheRule::Evaluate, vec![equality], Vec::new(), Vec::new())
            }
            EqualityPlan::LinearIdentity { .. } => proof.add_step(ProofStep::TheoryLemma {
                theory: "LIA".to_string(),
                clause: vec![equality],
                farkas: Some(FarkasAnnotation::from_ints(&[1])),
                kind: TheoryLemmaKind::LiaGeneric,
                lia: Some(ay_core::LiaAnnotation::LinearIdentity),
            }),
            EqualityPlan::MaskedResidue { .. } => {
                self.emit_masked_residue_equality(proof, equality)
            }
            EqualityPlan::Congruence { arguments, .. } => {
                let premises = arguments
                    .iter()
                    .map(|argument| self.emit_conjunct_equality(proof, argument).0)
                    .collect();
                proof.add_rule_step(AletheRule::Cong, vec![equality], premises, Vec::new())
            }
        };
        (step, equality)
    }

    /// The residue shape [`EqualityPlan::MaskedResidue`] names, confirmed by
    /// the strict validator's own query over `(= (= raw canonical) false)`.
    fn masked_residue_equality_is_checkable(&mut self, raw: TermId, canonical: TermId) -> bool {
        let is_app = |terms: &ay_core::TermStore, term: TermId, heads: &[&str]| {
            matches!(terms.get(term), TermData::App(Symbol::Named(name), _)
                if heads.contains(&name.as_str()))
        };
        if !is_app(&self.ctx.terms, raw, &["bv2nat", "bv2int"])
            || !is_app(&self.ctx.terms, canonical, &["mod"])
        {
            return false;
        }
        let refuted = self.masked_residue_refuted_root(raw, canonical);
        ay_proof::authenticate_bv_lia_unsat_query(&self.ctx.terms, &[refuted], None).is_ok()
    }

    /// `(= (= raw canonical) false)`.
    fn masked_residue_refuted_root(&mut self, raw: TermId, canonical: TermId) -> TermId {
        let equality = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [raw, canonical], Sort::Bool);
        let false_term = self.ctx.terms.false_term();
        self.ctx
            .terms
            .mk_app(Symbol::named("="), [equality, false_term], Sort::Bool)
    }

    /// `(cl equality)` for a planned [`EqualityPlan::MaskedResidue`]:
    ///
    /// ```text
    /// (cl (not (= E false)))       bv_lia_tautology (validator re-derives it)
    /// (cl (= E false) E false)     equiv_neg2
    /// (cl E false)                 resolution
    /// (cl (not false))             false
    /// (cl E)                       resolution
    /// ```
    fn emit_masked_residue_equality(&mut self, proof: &mut Proof, equality: TermId) -> ProofId {
        let false_term = self.ctx.terms.false_term();
        let refuted = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [equality, false_term], Sort::Bool);
        let not_refuted = self.ctx.terms.mk_not_raw(refuted);
        let not_false = self.ctx.terms.mk_not_raw(false_term);
        let lemma = proof.add_theory_lemma_with_kind(
            "BV/LIA",
            vec![not_refuted],
            TheoryLemmaKind::BvLiaTautology,
        );
        let introduction = proof.add_rule_step(
            AletheRule::EquivNeg2,
            vec![refuted, equality, false_term],
            Vec::new(),
            Vec::new(),
        );
        let with_false =
            proof.add_resolution(vec![equality, false_term], refuted, lemma, introduction);
        let false_axiom =
            proof.add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new());
        proof.add_resolution(vec![equality], false_term, false_axiom, with_false)
    }

    /// Move the unit `(cl from)` across the proved `(= from to)`.
    fn transport_across_equality(
        &mut self,
        proof: &mut Proof,
        unit: ProofId,
        from: TermId,
        to: TermId,
        equality_step: ProofId,
        equality: TermId,
    ) -> ProofId {
        let terms = &mut self.ctx.terms;
        let not_equality = terms.mk_not_raw(equality);
        let not_from = terms.mk_not_raw(from);
        let tautology = proof.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_equality, not_from, to],
            Vec::new(),
            Vec::new(),
        );
        let implication =
            proof.add_resolution(vec![not_from, to], equality, tautology, equality_step);
        proof.add_resolution(vec![to], from, implication, unit)
    }

    /// Derive `(cl (not term))` from `refutation`.
    fn emit_refutation(
        &mut self,
        proof: &mut Proof,
        term: TermId,
        refutation: &FalseRefutation,
    ) -> ProofId {
        match refutation {
            FalseRefutation::Literal => self.emit_refuted_disjunct(proof, term, None),
            FalseRefutation::Folded(plan) => self.emit_refuted_disjunct(proof, term, Some(plan)),
            FalseRefutation::FalseConjunct {
                index,
                conjunct,
                inner,
            } => {
                let refuted_conjunct = self.emit_refutation(proof, *conjunct, inner);
                let not_term = self.ctx.terms.mk_not_raw(term);
                let projection = proof.add_rule_step(
                    AletheRule::AndPos(*index),
                    vec![not_term, *conjunct],
                    Vec::new(),
                    vec![term],
                );
                proof.add_resolution(vec![not_term], *conjunct, refuted_conjunct, projection)
            }
        }
    }

    /// Derive `(cl (not term))` for a term that is `false` or folds to it.
    fn emit_refuted_disjunct(
        &mut self,
        proof: &mut Proof,
        term: TermId,
        folded: Option<&EqualityPlan>,
    ) -> ProofId {
        let false_term = self.ctx.terms.false_term();
        let not_false = self.ctx.terms.mk_not_raw(false_term);
        let false_axiom =
            proof.add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new());
        let Some(plan) = folded else {
            return false_axiom;
        };
        let (equality_step, equality) = self.emit_conjunct_equality(proof, plan);
        let terms = &mut self.ctx.terms;
        let not_equality = terms.mk_not_raw(equality);
        let not_term = terms.mk_not_raw(term);
        let tautology = proof.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_equality, not_term, false_term],
            Vec::new(),
            Vec::new(),
        );
        let without_false = proof.add_resolution(
            vec![not_equality, not_term],
            false_term,
            false_axiom,
            tautology,
        );
        proof.add_resolution(vec![not_term], equality, without_false, equality_step)
    }

    /// Emit `plan`, deriving `(cl canonical)` from the unit `(cl raw)`.
    pub(in crate::executor) fn emit_conjunct_transport(
        &mut self,
        proof: &mut Proof,
        unit: ProofId,
        raw: TermId,
        canonical: TermId,
        plan: &TransportPlan,
    ) -> ProofId {
        match plan {
            TransportPlan::Equality(equality_plan) => {
                let (step, equality) = self.emit_conjunct_equality(proof, equality_plan);
                self.transport_across_equality(proof, unit, raw, canonical, step, equality)
            }
            TransportPlan::EqualsFalse { p, folded } => {
                let false_term = self.ctx.terms.false_term();
                let (unit, equals_false) = match folded {
                    None => (unit, raw),
                    Some(folded) => {
                        let (argument_step, _) = self.emit_conjunct_equality(proof, folded);
                        let equals_false =
                            self.ctx
                                .terms
                                .mk_app(Symbol::named("="), [*p, false_term], Sort::Bool);
                        let equality = self.ctx.terms.mk_app(
                            Symbol::named("="),
                            [raw, equals_false],
                            Sort::Bool,
                        );
                        let step = proof.add_rule_step(
                            AletheRule::Cong,
                            vec![equality],
                            vec![argument_step],
                            Vec::new(),
                        );
                        (
                            self.transport_across_equality(
                                proof,
                                unit,
                                raw,
                                equals_false,
                                step,
                                equality,
                            ),
                            equals_false,
                        )
                    }
                };
                // `(cl (not (= p false)) (not p) false)` and `(cl (not false))`
                // resolve to `(cl (not (= p false)) (not p))`; the unit
                // `(= p false)` then leaves `(cl (not p))`.
                let terms = &mut self.ctx.terms;
                let not_equals_false = terms.mk_not_raw(equals_false);
                let not_p = terms.mk_not_raw(*p);
                let not_false = terms.mk_not_raw(false_term);
                let tautology = proof.add_rule_step(
                    AletheRule::EquivPos2,
                    vec![not_equals_false, not_p, false_term],
                    Vec::new(),
                    Vec::new(),
                );
                let false_axiom =
                    proof.add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new());
                let without_false = proof.add_resolution(
                    vec![not_equals_false, not_p],
                    false_term,
                    false_axiom,
                    tautology,
                );
                proof.add_resolution(vec![not_p], equals_false, without_false, unit)
            }
            TransportPlan::DisjunctionPermutation {
                raw_disjuncts,
                canonical_disjuncts,
                pairs,
            } => {
                let mut clause = raw_disjuncts.clone();
                let mut current =
                    proof.add_rule_step(AletheRule::Or, clause.clone(), vec![unit], Vec::new());
                for (&(i, bridge), &target) in pairs.iter().zip(canonical_disjuncts.iter()) {
                    let Some(bridge) = bridge else {
                        continue;
                    };
                    let source = raw_disjuncts[i];
                    // Planning made both disjunct lists duplicate-free, so the
                    // raw literal is present exactly once.
                    let Some(position) = clause.iter().position(|&literal| literal == source)
                    else {
                        continue;
                    };
                    clause[position] = target;
                    current = match bridge {
                        LiteralBridge::Farkas => {
                            let complement = complement_of(&mut self.ctx.terms, source);
                            let pivot = atom_of(&self.ctx.terms, source);
                            let lemma = Executor::add_pair_lemma(proof, target, complement);
                            proof.add_resolution(clause.clone(), pivot, lemma, current)
                        }
                        LiteralBridge::EqualityFlip => {
                            let (pivot, step) = self.add_eq_flip_bridge(proof, source, target);
                            proof.add_resolution(clause.clone(), pivot, current, step)
                        }
                    };
                }
                for (position, &target) in canonical_disjuncts.iter().enumerate() {
                    let _ = position;
                    let complement = self.ctx.terms.mk_not_raw(target);
                    let link = proof.add_rule_step(
                        AletheRule::OrNeg,
                        vec![canonical, complement],
                        Vec::new(),
                        Vec::new(),
                    );
                    if let Some(at) = clause.iter().position(|&literal| literal == target) {
                        let _ = clause.remove(at);
                    }
                    clause.push(canonical);
                    current = proof.add_resolution(clause.clone(), target, current, link);
                }
                proof.add_rule_step(
                    AletheRule::Contraction,
                    vec![canonical],
                    vec![current],
                    Vec::new(),
                )
            }
            TransportPlan::ImpliesFalse { p, q, refutation } => {
                let refuted = self.emit_refutation(proof, *q, refutation);
                let terms = &mut self.ctx.terms;
                let not_raw = terms.mk_not_raw(raw);
                let not_p = terms.mk_not_raw(*p);
                let elimination = proof.add_rule_step(
                    AletheRule::ImpliesPos,
                    vec![not_raw, not_p, *q],
                    Vec::new(),
                    Vec::new(),
                );
                let without_q =
                    proof.add_resolution(vec![not_raw, not_p], *q, refuted, elimination);
                proof.add_resolution(vec![not_p], raw, without_q, unit)
            }
            TransportPlan::AndFlatten { sources } => {
                let mut units = Vec::with_capacity(sources.len());
                let TermData::App(_, conjuncts) = self.ctx.terms.get(canonical).clone() else {
                    return unit;
                };
                for (source, &conjunct) in sources.iter().zip(conjuncts.iter()) {
                    let mut current = unit;
                    let mut current_term = raw;
                    for step in &source.path {
                        match step {
                            FlattenStep::AndPos(index) => {
                                let TermData::App(_, operands) =
                                    self.ctx.terms.get(current_term).clone()
                                else {
                                    return unit;
                                };
                                let Some(&operand) = operands.get(*index as usize) else {
                                    return unit;
                                };
                                let not_term = self.ctx.terms.mk_not_raw(current_term);
                                let projection = proof.add_rule_step(
                                    AletheRule::AndPos(*index),
                                    vec![not_term, operand],
                                    Vec::new(),
                                    vec![current_term],
                                );
                                current = proof.add_resolution(
                                    vec![operand],
                                    current_term,
                                    projection,
                                    current,
                                );
                                current_term = operand;
                            }
                            FlattenStep::Prune {
                                disjuncts,
                                kept,
                                falsified,
                            } => {
                                current = self.emit_prune(proof, current, disjuncts, falsified);
                                current_term = disjuncts[*kept];
                            }
                        }
                    }
                    debug_assert_eq!(current_term, source.leaf);
                    let conjunct_unit = match &source.transport {
                        None => current,
                        Some(plan) => self.emit_conjunct_transport(
                            proof,
                            current,
                            source.leaf,
                            conjunct,
                            plan,
                        ),
                    };
                    units.push(conjunct_unit);
                }
                let mut clause = Vec::with_capacity(conjuncts.len() + 1);
                clause.push(canonical);
                for &conjunct in &conjuncts {
                    clause.push(self.ctx.terms.mk_not_raw(conjunct));
                }
                let mut current = proof.add_rule_step(
                    AletheRule::AndNeg,
                    clause.clone(),
                    Vec::new(),
                    vec![canonical],
                );
                for (&conjunct, &conjunct_unit) in conjuncts.iter().zip(units.iter()) {
                    let complement = self.ctx.terms.mk_not_raw(conjunct);
                    if let Some(position) = clause.iter().position(|&literal| literal == complement)
                    {
                        let _ = clause.remove(position);
                    }
                    current =
                        proof.add_resolution(clause.clone(), conjunct, current, conjunct_unit);
                }
                current
            }
            TransportPlan::Farkas => {
                let raw_complement = complement_of(&mut self.ctx.terms, raw);
                let pivot = atom_of(&self.ctx.terms, raw);
                let lemma = Executor::add_pair_lemma(proof, canonical, raw_complement);
                proof.add_resolution(vec![canonical], pivot, lemma, unit)
            }
            TransportPlan::EqualityFlip => {
                let (pivot, bridge) = self.add_eq_flip_bridge(proof, raw, canonical);
                proof.add_resolution(vec![canonical], pivot, unit, bridge)
            }
            TransportPlan::IteTree { k, shape } => {
                self.emit_ite_shape(proof, raw, unit, *k, shape, unit, &[])
            }
            TransportPlan::DisjunctionPrune {
                disjuncts,
                kept,
                falsified,
                rest,
            } => {
                let current = self.emit_prune(proof, unit, disjuncts, falsified);
                let kept_term = disjuncts[*kept];
                match rest {
                    None => current,
                    Some(rest) => {
                        self.emit_conjunct_transport(proof, current, kept_term, canonical, rest)
                    }
                }
            }
        }
    }

    /// `(cl d_kept)` from the unit `(cl (or d_0 .. d_n))` and a refutation of
    /// every other disjunct.
    fn emit_prune(
        &mut self,
        proof: &mut Proof,
        unit: ProofId,
        disjuncts: &[TermId],
        falsified: &[(usize, FalseRefutation)],
    ) -> ProofId {
        let mut clause = disjuncts.to_vec();
        let mut current =
            proof.add_rule_step(AletheRule::Or, clause.clone(), vec![unit], Vec::new());
        for (index, refutation) in falsified {
            let disjunct = disjuncts[*index];
            let refuted = self.emit_refutation(proof, disjunct, refutation);
            clause.retain(|&literal| literal != disjunct);
            current = proof.add_resolution(clause.clone(), disjunct, refuted, current);
        }
        current
    }

    /// The `ite_intro` terms for the subterm `ite_term = (ite condition u v)`
    /// of `raw`, interned without normalization (the definition must keep
    /// the exact raw condition, including a leading `not`):
    /// `(eq_then, eq_else, ite_def, and_term, intro_eq)`.
    fn ite_intro_connectives(
        &mut self,
        raw: TermId,
        condition: TermId,
        ite_term: TermId,
        u: TermId,
        v: TermId,
    ) -> Option<(TermId, TermId, TermId, TermId, TermId)> {
        let terms = &mut self.ctx.terms;
        let eq_then = terms.mk_app(Symbol::named("="), [ite_term, u], Sort::Bool);
        let eq_else = terms.mk_app(Symbol::named("="), [ite_term, v], Sort::Bool);
        let ite_def = terms.mk_ite_raw(condition, eq_then, eq_else);
        if !matches!(
            terms.get(ite_def),
            TermData::Ite(c, a, b) if *c == condition && *a == eq_then && *b == eq_else
        ) {
            return None;
        }
        let and_term = terms.mk_app(Symbol::named("and"), [raw, ite_def], Sort::Bool);
        let intro_eq = terms.mk_app(Symbol::named("="), [raw, and_term], Sort::Bool);
        Some((eq_then, eq_else, ite_def, and_term, intro_eq))
    }

    /// A term reached only through a checked transport is no longer a
    /// premise: the transport relates it to raw authored terms, so neither it
    /// nor anything below it may keep an authored spelling (the raw `assume`
    /// prints the authored text by itself).
    pub(in crate::executor) fn drop_surface_overrides_below(&mut self, roots: &[TermId]) {
        let Some(overrides) = self.last_proof_term_overrides.as_mut() else {
            return;
        };
        let mut stack: Vec<TermId> = roots.to_vec();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            overrides.remove(&term);
            match self.ctx.terms.get(term) {
                TermData::App(_, arguments) => stack.extend(arguments.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.extend([*condition, *then_branch, *else_branch]);
                }
                _ => {}
            }
        }
    }

    /// `(cl (not atom) atom)` from `eq_reflexive` and `equiv_pos2`.
    fn emit_excluded_middle(&mut self, proof: &mut Proof, atom: TermId) -> ProofId {
        let terms = &mut self.ctx.terms;
        let reflexive = terms.mk_app(Symbol::named("="), [atom, atom], Sort::Bool);
        let not_reflexive = terms.mk_not_raw(reflexive);
        let not_atom = terms.mk_not_raw(atom);
        let equality = proof.add_rule_step(
            AletheRule::EqReflexive,
            vec![reflexive],
            Vec::new(),
            Vec::new(),
        );
        let tautology = proof.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_reflexive, not_atom, atom],
            Vec::new(),
            Vec::new(),
        );
        proof.add_resolution(vec![not_atom, atom], reflexive, tautology, equality)
    }

    /// Plan the lift of the raw term `value` (a subterm of `raw`) under `k`
    /// onto the canonical formula `canonical`.
    fn plan_ite_shape(
        &mut self,
        raw: TermId,
        k: TermId,
        value: TermId,
        canonical: TermId,
        nodes: &mut usize,
    ) -> Option<IteShape> {
        *nodes += 1;
        if *nodes > MAX_TRANSPORT_NODES {
            return None;
        }
        let TermData::Ite(condition, then_value, else_value) = *self.ctx.terms.get(value) else {
            // A leaf: `(= k value)`, possibly with a rewritten value.
            let TermData::App(Symbol::Named(op), sides) = self.ctx.terms.get(canonical).clone()
            else {
                return None;
            };
            if op != "=" || sides.len() != 2 || sides[0] != k {
                return None;
            }
            let bridge = self.plan_conjunct_equality(value, sides[1], nodes).ok()?;
            return Some(IteShape::Leaf {
                value,
                literal: canonical,
                bridge,
            });
        };
        let TermData::Ite(lifted_condition, lifted_then, lifted_else) =
            *self.ctx.terms.get(canonical)
        else {
            return None;
        };
        let (negated, atom) = match *self.ctx.terms.get(condition) {
            TermData::Not(atom) => (true, atom),
            _ => (false, condition),
        };
        // Condition literals are moved with one-row Farkas lemmas in both
        // directions; planning verifies both now.
        let terms = &mut self.ctx.terms;
        let not_atom = terms.mk_not_raw(atom);
        let not_lifted = terms.mk_not_raw(lifted_condition);
        if atom != lifted_condition
            && (!is_arithmetic_comparison_literal(terms, atom)
                || !is_arithmetic_comparison_literal(terms, lifted_condition)
                || !self.pair_lemma_valid(not_atom, lifted_condition)
                || !self.pair_lemma_valid(atom, not_lifted))
        {
            return None;
        }
        let _connectives =
            self.ite_intro_connectives(raw, condition, value, then_value, else_value)?;
        let (then_raw, else_raw) = if negated {
            (else_value, then_value)
        } else {
            (then_value, else_value)
        };
        let then_shape = self.plan_ite_shape(raw, k, then_raw, lifted_then, nodes)?;
        let else_shape = self.plan_ite_shape(raw, k, else_raw, lifted_else, nodes)?;
        Some(IteShape::Node {
            ite_term: value,
            condition,
            negated,
            lifted_condition,
            canonical,
            then_shape: Box::new(then_shape),
            else_shape: Box::new(else_shape),
        })
    }

    /// Emit `shape`. `clause_proof` concludes `prefix ++ [(= k value)]`
    /// where `value` is the shape's raw term; the result concludes
    /// `prefix ++ [shape.canonical()]`.
    #[allow(clippy::too_many_arguments)]
    fn emit_ite_shape(
        &mut self,
        proof: &mut Proof,
        raw: TermId,
        raw_unit: ProofId,
        k: TermId,
        shape: &IteShape,
        clause_proof: ProofId,
        prefix: &[TermId],
    ) -> ProofId {
        match shape {
            IteShape::Leaf {
                value,
                literal,
                bridge,
            } => {
                let Some(bridge) = bridge else {
                    return clause_proof;
                };
                let terms = &mut self.ctx.terms;
                let raw_literal = terms.mk_app(Symbol::named("="), [k, *value], Sort::Bool);
                let (argument_step, _) = self.emit_conjunct_equality(proof, bridge);
                let terms = &mut self.ctx.terms;
                let equality =
                    terms.mk_app(Symbol::named("="), [raw_literal, *literal], Sort::Bool);
                let not_equality = terms.mk_not_raw(equality);
                let not_raw_literal = terms.mk_not_raw(raw_literal);
                let congruence = proof.add_rule_step(
                    AletheRule::Cong,
                    vec![equality],
                    vec![argument_step],
                    Vec::new(),
                );
                let tautology = proof.add_rule_step(
                    AletheRule::EquivPos2,
                    vec![not_equality, not_raw_literal, *literal],
                    Vec::new(),
                    Vec::new(),
                );
                let implication = proof.add_resolution(
                    vec![not_raw_literal, *literal],
                    equality,
                    tautology,
                    congruence,
                );
                let mut clause = prefix.to_vec();
                clause.push(*literal);
                proof.add_resolution(clause, raw_literal, implication, clause_proof)
            }
            IteShape::Node {
                ite_term,
                condition,
                negated,
                lifted_condition,
                canonical,
                then_shape,
                else_shape,
            } => {
                let TermData::Ite(_, then_value, else_value) = *self.ctx.terms.get(*ite_term)
                else {
                    return clause_proof;
                };
                let Some((eq_then, eq_else, ite_def, and_term, intro_eq)) =
                    self.ite_intro_connectives(raw, *condition, *ite_term, then_value, else_value)
                else {
                    return clause_proof;
                };
                let terms = &mut self.ctx.terms;
                let value_literal = terms.mk_app(Symbol::named("="), [k, *ite_term], Sort::Bool);
                let then_literal = terms.mk_app(Symbol::named("="), [k, then_value], Sort::Bool);
                let else_literal = terms.mk_app(Symbol::named("="), [k, else_value], Sort::Bool);
                let not_value_literal = terms.mk_not_raw(value_literal);
                let not_intro_eq = terms.mk_not_raw(intro_eq);
                let not_raw = terms.mk_not_raw(raw);
                let not_and = terms.mk_not_raw(and_term);
                let not_condition = terms.mk_not_raw(*condition);
                let not_eq_then = terms.mk_not_raw(eq_then);
                let not_eq_else = terms.mk_not_raw(eq_else);
                let not_lifted = terms.mk_not_raw(*lifted_condition);
                let then_canonical = then_shape.canonical();
                let else_canonical = else_shape.canonical();
                let not_then_canonical = terms.mk_not_raw(then_canonical);
                let not_else_canonical = terms.mk_not_raw(else_canonical);
                let atom = match *terms.get(*condition) {
                    TermData::Not(atom) if *negated => atom,
                    _ => *condition,
                };
                let not_atom = terms.mk_not_raw(atom);

                // `ite_intro` defines this `ite` subterm of the raw conjunct.
                let intro = proof.add_rule_step(
                    AletheRule::IteIntro,
                    vec![intro_eq],
                    Vec::new(),
                    Vec::new(),
                );
                let equiv = proof.add_rule_step(
                    AletheRule::EquivPos2,
                    vec![not_intro_eq, not_raw, and_term],
                    Vec::new(),
                    Vec::new(),
                );
                let defined = proof.add_resolution(vec![not_raw, and_term], intro_eq, equiv, intro);
                let conjunction = proof.add_resolution(vec![and_term], raw, defined, raw_unit);
                let projection = proof.add_rule_step(
                    AletheRule::AndPos(1),
                    vec![not_and, ite_def],
                    Vec::new(),
                    Vec::new(),
                );
                let definition =
                    proof.add_resolution(vec![ite_def], and_term, projection, conjunction);
                let then_branch = proof.add_rule_step(
                    AletheRule::Ite2,
                    vec![not_condition, eq_then],
                    vec![definition],
                    Vec::new(),
                );
                let else_branch = proof.add_rule_step(
                    AletheRule::Ite1,
                    vec![*condition, eq_else],
                    vec![definition],
                    Vec::new(),
                );

                // `(= k T)` and `(= T branch)` give `(= k branch)`.
                let then_transitive = proof.add_rule_step(
                    AletheRule::EqTransitive,
                    vec![not_value_literal, not_eq_then, then_literal],
                    Vec::new(),
                    Vec::new(),
                );
                let else_transitive = proof.add_rule_step(
                    AletheRule::EqTransitive,
                    vec![not_value_literal, not_eq_else, else_literal],
                    Vec::new(),
                    Vec::new(),
                );
                let then_open = proof.add_resolution(
                    vec![not_value_literal, not_condition, then_literal],
                    eq_then,
                    then_transitive,
                    then_branch,
                );
                let else_open = proof.add_resolution(
                    vec![not_value_literal, *condition, else_literal],
                    eq_else,
                    else_transitive,
                    else_branch,
                );
                let with = |extra: &[TermId]| {
                    let mut clause = prefix.to_vec();
                    clause.extend_from_slice(extra);
                    clause
                };
                let raw_then_path = proof.add_resolution(
                    with(&[not_condition, then_literal]),
                    value_literal,
                    then_open,
                    clause_proof,
                );
                let raw_else_path = proof.add_resolution(
                    with(&[*condition, else_literal]),
                    value_literal,
                    else_open,
                    clause_proof,
                );

                // Move the raw condition literal onto the lifted condition.
                // Planning verified `(cl (not atom) lifted)` and
                // `(cl atom (not lifted))`.
                let (canonical_then_path, canonical_else_path) = if atom == *lifted_condition {
                    if *negated {
                        // The raw `then` literal is `(not (not atom))`; the
                        // tautology `(cl (not atom) atom)` turns it into
                        // `atom`. The raw `else` literal already is
                        // `(not atom)`.
                        let tautology = self.emit_excluded_middle(proof, atom);
                        let lifted_else_path = proof.add_resolution(
                            with(&[atom, then_literal]),
                            *condition,
                            raw_then_path,
                            tautology,
                        );
                        (raw_else_path, lifted_else_path)
                    } else {
                        (raw_then_path, raw_else_path)
                    }
                } else if *negated {
                    let atom_implies_lifted =
                        Executor::add_pair_lemma(proof, not_atom, *lifted_condition);
                    let lifted_implies_atom = Executor::add_pair_lemma(proof, atom, not_lifted);
                    // Raw `then` runs when `atom` is false: the lifted `else`.
                    let lifted_else_path = proof.add_resolution(
                        with(&[*lifted_condition, then_literal]),
                        *condition,
                        raw_then_path,
                        atom_implies_lifted,
                    );
                    let lifted_then_path = proof.add_resolution(
                        with(&[not_lifted, else_literal]),
                        atom,
                        raw_else_path,
                        lifted_implies_atom,
                    );
                    (lifted_then_path, lifted_else_path)
                } else {
                    let atom_implies_lifted =
                        Executor::add_pair_lemma(proof, not_atom, *lifted_condition);
                    let lifted_implies_atom = Executor::add_pair_lemma(proof, atom, not_lifted);
                    let lifted_then_path = proof.add_resolution(
                        with(&[not_lifted, then_literal]),
                        atom,
                        raw_then_path,
                        lifted_implies_atom,
                    );
                    let lifted_else_path = proof.add_resolution(
                        with(&[*lifted_condition, else_literal]),
                        atom,
                        atom_implies_lifted,
                        raw_else_path,
                    );
                    (lifted_then_path, lifted_else_path)
                };

                let then_prefix = with(&[not_lifted]);
                let else_prefix = with(&[*lifted_condition]);
                let then_done = self.emit_ite_shape(
                    proof,
                    raw,
                    raw_unit,
                    k,
                    then_shape,
                    canonical_then_path,
                    &then_prefix,
                );
                let else_done = self.emit_ite_shape(
                    proof,
                    raw,
                    raw_unit,
                    k,
                    else_shape,
                    canonical_else_path,
                    &else_prefix,
                );
                let then_goal = proof.add_rule_step(
                    AletheRule::IteNeg2,
                    vec![*canonical, not_lifted, not_then_canonical],
                    Vec::new(),
                    Vec::new(),
                );
                let else_goal = proof.add_rule_step(
                    AletheRule::IteNeg1,
                    vec![*canonical, *lifted_condition, not_else_canonical],
                    Vec::new(),
                    Vec::new(),
                );
                let then_closed = proof.add_resolution(
                    with(&[not_lifted, *canonical]),
                    then_canonical,
                    then_goal,
                    then_done,
                );
                let else_closed = proof.add_resolution(
                    with(&[*lifted_condition, *canonical]),
                    else_canonical,
                    else_goal,
                    else_done,
                );
                let both = proof.add_resolution(
                    with(&[*canonical, *canonical]),
                    *lifted_condition,
                    then_closed,
                    else_closed,
                );
                proof.add_rule_step(
                    AletheRule::Contraction,
                    with(&[*canonical]),
                    vec![both],
                    Vec::new(),
                )
            }
        }
    }
}
