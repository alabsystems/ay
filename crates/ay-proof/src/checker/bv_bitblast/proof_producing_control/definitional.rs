// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The definitional retry of the proof-producing clause lowering.
//!
//! [`ProofProducingLowerer`] lowers the hash-consed source DAG into a `BvExpr`
//! TREE: a memoized term is CLONED at every reference, and every materialized
//! node is charged to the lowering's counted caps. A clause whose DAG is a few
//! hundred terms but whose expansion is not — one let-free authored assertion
//! that repeats its subterms, as external-codegen's strict-gate rows 2057–2060 do
//! (35k–134k parsed nodes over 450–650 hash-consed terms) — runs out of those
//! caps before anything is blasted, although its circuit is small, and the
//! UNSAT verdict had no proof.
//!
//! When the ordinary lowering of a clause over no array is refused because a
//! counted cap ran out (the same array exclusion the producer's sweep keeps),
//! the clause is
//! lowered again with every SHARED compound Bool/bit-vector term `t` — one
//! the lowering would copy, because the source DAG references it twice or an
//! `ite` reads it as a condition — and every term whose own lowering passes
//! [`DEFINE_ABOVE_NODES`] replaced by a fresh leaf `proof_def_<t>` of its
//! width, with its lowered operator recorded as the definition
//! `(= proof_def_<t> e_t)`. Every other term is inlined into its one parent
//! exactly as before. The producer is then asked to prove
//!
//! ```text
//! C' = C[defs] ∨ ¬def_1 ∨ … ∨ ¬def_n
//! ```
//!
//! which is `def_1 ∧ … ∧ def_n → C[defs]`. Its expression is linear in the DAG.
//!
//! Exact signed-power lowering can also start scalar naming in its first
//! lowering, before reading operands. It names only scalar results above
//! `DEFINE_ABOVE_NODES`, without a source census. Array values are not named;
//! the same functional-extension argument applies to already lowered scalar
//! results in array-containing clauses. Walk and materialization charges stay
//! in place. This does not enable the array-excluded retry described above.
//!
//! ## Why accepting `C'` accepts `C`
//!
//! Take any assignment to the ORIGINAL leaves (a free leaf the lowering
//! abstracts an operator to is one of them). Each definition's expression
//! mentions only original leaves and the leaves of terms lowered BEFORE it (an
//! operand is lowered, and defined, before the term that applies it; a term
//! lowered twice records two lowerings of the same term), so assigning each
//! `proof_def_<t>` the value of `t`, in definition order, satisfies every
//! definition. Under that
//! extension each `proof_def_<t>` equals the value of `t`'s full expansion (by
//! induction over the same order), so `C[defs]` takes the value of `C`. The
//! producer's refutation of `¬C'` — replayed independently, exactly as for an
//! ordinary clause — shows `C'` holds under EVERY assignment, this one included,
//! so `C` holds. The definitions are functional, so `¬C'` is satisfiable
//! exactly when `¬C` is: a satisfiable answer is the same genuine veto as the
//! ordinary lowering's, not an abstraction.
//!
//! The `proof_def_` namespace is disjoint from every other leaf this lowering
//! names (`proof_bool_`, `proof_bv_`, `proof_array_…`, the frame offsets), and
//! the retry runs only after the ordinary lowering was refused. First-pass
//! scalar naming for signed powers can change expression shape and copy costs;
//! preserving prior admissions therefore requires semantic regression checks.
//! A definitional lowering is under the same caps as an ordinary one, and
//! continues its walk count (`lower_clause`).

use super::super::{BvExpr, ProofProducingExpr, ProofProducingLowerer};
use ay_core::{TermData, TermId, TermStore};
use std::collections::{HashMap, HashSet};

/// An unshared term whose lowering passes this many `BvExpr` nodes is named
/// too, so no inlined expansion larger than this is ever copied by an arm
/// that reads an operand's expression more than once, as an `ite` reads its
/// condition.
const DEFINE_ABOVE_NODES: usize = 32;

/// The definitional state of one lowering.
pub(in crate::checker::bv_bitblast) struct Definitions {
    recorded: Vec<BvExpr>,
    /// Terms the lowering would copy; `None` names every compound term (the
    /// clause DAG was too large to count, and the lowering refuses it anyway).
    shared: Option<HashSet<TermId>>,
}

/// The clause's terms referenced twice, counting an `ite` condition twice
/// (both arms of its lowering read it). Walks at most the lowering's own
/// term-node and child-edge caps.
fn shared_terms(terms: &TermStore, clause: &[TermId]) -> Option<HashSet<TermId>> {
    let mut references: HashMap<TermId, usize> = HashMap::new();
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut pending: Vec<TermId> = clause.to_vec();
    let mut edges = 0_usize;
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        edges = edges.saturating_add(terms.children(term).len());
        if seen.len() > super::super::MAX_PROOF_PRODUCING_TERM_NODES
            || edges > super::super::MAX_PROOF_PRODUCING_TERM_EDGES
        {
            return None;
        }
        let condition = match terms.get(term) {
            TermData::Ite(condition, ..) => Some(*condition),
            _ => None,
        };
        for child in terms.children(term) {
            let weight = if Some(child) == condition { 2 } else { 1 };
            *references.entry(child).or_default() += weight;
            pending.push(child);
        }
    }
    Some(
        references
            .into_iter()
            .filter_map(|(term, count)| (count > 1).then_some(term))
            .collect(),
    )
}

impl ProofProducingLowerer<'_, '_> {
    /// Bound internal operand copies before exact signed-power lowering.
    /// Naming only large scalar results needs no source-DAG census. The same
    /// functional definitions and counted walks/materializations below apply;
    /// this is one lowering, including when its source contains arrays.
    pub(in crate::checker::bv_bitblast) fn record_scalar_definitions(&mut self) {
        if self.definitions.is_none() {
            self.definitions = Some(Definitions {
                recorded: Vec::new(),
                shared: Some(HashSet::new()),
            });
        }
    }

    /// Replace a freshly lowered compound term by its definition leaf when
    /// this lowering is definitional; otherwise return it unchanged.
    pub(in crate::checker::bv_bitblast) fn define(
        &mut self,
        term: TermId,
        lowered: ProofProducingExpr,
    ) -> Result<ProofProducingExpr, String> {
        let Some(definitions) = self.definitions.as_ref() else {
            return Ok(lowered);
        };
        let shared = definitions
            .shared
            .as_ref()
            .is_none_or(|shared| shared.contains(&term));
        let (expr, width, bool_sorted) = match lowered {
            ProofProducingExpr::Bool(expr) => (expr, 1, true),
            ProofProducingExpr::BitVec(expr, width) => (expr, width, false),
            array @ ProofProducingExpr::Array(_) => return Ok(array),
        };
        let atomic = matches!(expr, BvExpr::Leaf { .. } | BvExpr::Const { .. });
        let small = !atomic
            && !shared
            && self
                .count_bv_nodes(&expr)
                .is_ok_and(|n| n <= DEFINE_ABOVE_NODES);
        let leaf = if atomic || small {
            expr
        } else {
            let leaf = BvExpr::leaf(&format!("proof_def_{}", term.index()), width);
            let definition = BvExpr::eq(leaf.clone(), expr);
            let nodes = self.count_bv_nodes(&definition)?;
            self.charge_constructed_expr_nodes(nodes)?;
            if let Some(definitions) = self.definitions.as_mut() {
                definitions.recorded.push(definition);
            }
            leaf
        };
        Ok(if bool_sorted {
            ProofProducingExpr::Bool(leaf)
        } else {
            ProofProducingExpr::BitVec(leaf, width)
        })
    }

    /// Start recording definitions for `clause`: every later lowering of a
    /// compound term goes through [`Self::define`].
    pub(super) fn record_definitions(&mut self, clause: &[TermId]) {
        self.definitions = Some(Definitions {
            recorded: Vec::new(),
            shared: shared_terms(self.terms, clause),
        });
    }

    /// The disjuncts `¬def_i` that turn the lowered clause into `C'`, for the
    /// definitions `lowered` reaches.
    ///
    /// A definition nothing reads is dropped: the extract-through-`concat`
    /// slicing lowers (and so defines) a whole operand it then reads only in
    /// part, and every kept definition would still be blasted. Dropping it is
    /// sound because what is kept reads only kept leaves, so the extension in
    /// the module docs still satisfies every kept definition.
    pub(super) fn take_negated_definitions(&mut self, lowered: &[BvExpr]) -> Vec<BvExpr> {
        let Some(definitions) = self.definitions.take() else {
            return Vec::new();
        };
        let recorded = definitions.recorded;
        let index: HashMap<&str, usize> = recorded
            .iter()
            .enumerate()
            .filter_map(|(position, definition)| match definition {
                BvExpr::Eq(leaf, _) => match leaf.as_ref() {
                    BvExpr::Leaf { name, .. } => Some((name.as_str(), position)),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        let mut kept = vec![false; recorded.len()];
        let mut pending: Vec<&BvExpr> = lowered.iter().collect();
        while let Some(expr) = pending.pop() {
            match expr {
                BvExpr::Leaf { name, .. } => {
                    if let Some(&position) = index.get(name.as_str()) {
                        if !kept[position] {
                            kept[position] = true;
                            if let BvExpr::Eq(_, body) = &recorded[position] {
                                pending.push(body);
                            }
                        }
                    }
                }
                BvExpr::Const { .. } => {}
                BvExpr::ZeroExt(inner, _)
                | BvExpr::Extract { inner, .. }
                | BvExpr::SignExt(inner, _)
                | BvExpr::Not(inner) => pending.push(inner),
                BvExpr::CarryOut { lhs, rhs, .. }
                | BvExpr::Add(lhs, rhs)
                | BvExpr::Sub(lhs, rhs)
                | BvExpr::Or(lhs, rhs)
                | BvExpr::And(lhs, rhs)
                | BvExpr::Xor(lhs, rhs)
                | BvExpr::Shl(lhs, rhs)
                | BvExpr::Lshr(lhs, rhs)
                | BvExpr::Ashr(lhs, rhs)
                | BvExpr::Ult(lhs, rhs)
                | BvExpr::Eq(lhs, rhs)
                | BvExpr::Mul(lhs, rhs)
                | BvExpr::UDiv(lhs, rhs)
                | BvExpr::URem(lhs, rhs) => {
                    pending.push(lhs);
                    pending.push(rhs);
                }
            }
        }
        drop(index);
        recorded
            .into_iter()
            .zip(kept)
            .filter_map(|(definition, kept)| kept.then(|| BvExpr::not(definition)))
            .collect()
    }
}
