// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact authored refutation for a propagated unsigned-zero/high-half conflict.
//!
//! Acyclic CHC replay obligations can contain one very wide conjunction whose
//! relevant core is only
//!
//! ```text
//! x = ... = y,  y <u 1,  not (high_half(zero_extend(x) * K) = 0).
//! ```
//!
//! The eager BV solver proves the conjunction inconsistent, but the generic
//! whole-formula bit-blast is too large to export.  This lane extracts the
//! four authored facts and composes only standard checked rules: `and_pos`,
//! the already-supported `x <u 1 <=> x = 0` bit-blast identity, EUF
//! congruence/transitivity, and one closed ground-BV `evaluate` step.

use super::*;
use shape::{
    decode_high_zero_target, decode_ult_one_fact, decode_var_equality, emit_conjunct_unit,
    equality_path, raw_application, raw_equality, raw_not, HighZeroTarget, PathHop, UltOneFact,
    VarEquality, MAX_EQUALITY_EDGES,
};

mod shape;

const MAX_AUTHORED_CONJUNCTS: usize = 4_096;
const MAX_AUTHORED_ROOTS: usize = 64;
/// Recursive raw rebuilding is used only after this iterative surface gate.
/// Keep its call stack comfortably below the frontend's intentionally much
/// larger parse-depth envelope.
const MAX_AUTHORED_SURFACE_DEPTH: usize = 256;
/// Aggregate frontend term nodes admitted across all raw rebuild attempts.
const MAX_AUTHORED_SURFACE_NODES: usize = 100_000;
/// Aggregate owned token bytes admitted across every parsed root considered by
/// this lane. Structural node accounting does not bound one enormous symbol or
/// BV literal, and cloning/parsing either duplicates work proportional to its
/// byte length.
const MAX_AUTHORED_SURFACE_TOKEN_BYTES: usize = 4 * 1024 * 1024;
/// Per-token cap for decimal strings that the raw QF_BV builder will parse.
/// In particular, `(_ bvN W)` converts `N` to a `BigInt` before reducing it to
/// width `W`; allowing the full aggregate byte allowance in one decimal value
/// would leave that superlinear conversion as a repair-time denial-of-service.
/// This is far above the 128-bit values the high-zero shape can consume.
const MAX_AUTHORED_DECIMAL_TOKEN_DIGITS: usize = 4_096;
const MAX_HIGH_ZERO_TARGETS: usize = 16;
const MAX_ULT_ONE_FACTS: usize = 16;
const MAX_TARGET_ULT_PAIRS: usize = 64;
const MAX_PATH_EDGE_VISITS: usize = 1_000_000;
/// Aggregate expensive closed-BV recognizer attempts across one authored
/// repair. This shares the strict checker's structural ceiling so producer
/// discovery cannot multiply the evaluator's per-call private envelope.
const MAX_CLOSED_BV_EVALUATE_PROBES: usize = ay_proof::MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF;

impl Executor {
    /// Replace a provisional refutation with the exact small authored BV core.
    ///
    /// Every assumed term is a raw, structure-preserving rebuild of one parsed
    /// top-level assertion.  The candidate is committed only after the strict
    /// checker replays it against that exact authored scope and observes a
    /// complete empty-clause derivation.
    pub(super) fn replace_with_exact_authored_bv_high_zero_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        if self.last_proof_raw_original_assertions.is_empty()
            || self.last_proof_rebuild_originals.is_empty()
            || self.last_proof_raw_original_assertions.len() > MAX_AUTHORED_ROOTS
            || self.last_proof_rebuild_originals.len() > MAX_AUTHORED_ROOTS * 3
        {
            return;
        }

        // Select bounded roots while the parsed trees are still borrowed. A
        // derived `FrontendTerm::clone` recursively clones the whole tree, so
        // cloning the assertion vector before this admission pass would defeat
        // the depth/node gate below.
        let Some(admitted_surface_indices) =
            admitted_qfbv_surface_indices(self.ctx.assertions_parsed())
        else {
            return;
        };
        if admitted_surface_indices.is_empty() {
            return;
        }
        let parsed_len = self.ctx.assertions_parsed().len();
        // Do not call `exact_concrete_authored_scope` here: it intentionally
        // clones the complete authored ledger before deduplication. This lane
        // needs only the source-aligned prefix that contains the admitted raw
        // roots, and its own small root cap must apply before any clone.
        let Some(canonical_scope) = self.bounded_bv_high_zero_authored_scope() else {
            return;
        };
        if ay_core::misc_cli_flags().debug_cert {
            eprintln!(
                "CERT/authored-bv-high-zero: parsed={} retained={} canonical={} proof-steps={}",
                parsed_len,
                self.ctx.retains_parsed_assertions(),
                canonical_scope.len(),
                proof.steps.len()
            );
        }
        let mut eligible_roots = Vec::new();
        for surface_index in admitted_surface_indices {
            let Some(canonical_root) = self
                .proof_original_problem_assertions_slice()
                .get(surface_index)
                .copied()
            else {
                continue;
            };
            if !canonical_scope.contains(&canonical_root) {
                continue;
            }
            // Every selected tree passed the iterative gate above. Clone only
            // this one bounded root to release the context borrow before the
            // raw builder mutates the term store.
            let surface = self.ctx.assertions_parsed()[surface_index].clone();
            let Some(raw_root) = build_qfbv_pterm(&mut self.ctx.terms, &surface) else {
                continue;
            };
            let TermData::App(Symbol::Named(operator), conjuncts) =
                self.ctx.terms.get(raw_root).clone()
            else {
                continue;
            };
            if operator != "and" || conjuncts.len() < 4 || conjuncts.len() > MAX_AUTHORED_CONJUNCTS
            {
                continue;
            }
            // Authority is a fact about the exact raw TermId, not the storage
            // position of that fact. The raw ledger is intentionally a compact
            // list: source forms that cannot be rebuilt are omitted and another
            // authenticated writer deduplicates repeated roots. Requiring its
            // index to mirror `assertions_parsed` therefore rejects later valid
            // roots. Duplicate membership is unambiguous here because equal
            // TermIds denote the same exact premise in the term store.
            if !self.last_proof_raw_original_assertions.contains(&raw_root)
                || !self.last_proof_rebuild_originals.contains(&raw_root)
            {
                continue;
            }
            if !authored_bv_high_zero_shape_present(&self.ctx.terms, &conjuncts) {
                continue;
            }
            eligible_roots.push((raw_root, conjuncts));
        }
        if eligible_roots.is_empty() || self.authored_cascade_publishable(proof) {
            return;
        }

        for (raw_root, conjuncts) in eligible_roots {
            let mut candidate_scope = canonical_scope.clone();
            if !candidate_scope.contains(&raw_root) {
                candidate_scope.push(raw_root);
            }
            let Some(candidate) =
                self.build_authored_bv_high_zero_candidate(raw_root, &conjuncts, &candidate_scope)
            else {
                continue;
            };

            *proof = candidate;
            // The candidate assumes only the exact raw parsed assertion whose
            // pre-existing raw/rebuild ledger membership was authenticated
            // above. It needs no global spelling override and mints no new
            // problem authority.
            self.last_proof_term_overrides = None;
            return;
        }
    }

    /// Build only the small authenticated scope this raw-surface lane needs.
    ///
    /// `proof_original_problem_assertions_slice` is either the frozen original
    /// provenance ledger or the exact assertion prefix aligned with
    /// `assertions_parsed`. Reject on the supplied cardinality before copying;
    /// deduplicating a huge attacker-controlled vector first would make the cap
    /// cosmetic. Check-sat-assuming literals are included exactly as in
    /// `exact_concrete_authored_scope`.
    fn bounded_bv_high_zero_authored_scope(&self) -> Option<Vec<TermId>> {
        let source = self.proof_original_problem_assertions_slice();
        if source.len() != self.ctx.assertions_parsed().len() {
            return None;
        }
        let assumptions = self.last_assumptions.as_deref().unwrap_or(&[]);
        let supplied_roots = source.len().checked_add(assumptions.len())?;
        if supplied_roots > MAX_AUTHORED_ROOTS {
            return None;
        }

        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut exact = Vec::with_capacity(supplied_roots);
        for &term in source.iter().chain(assumptions) {
            if seen.insert(term) {
                exact.push(term);
            }
        }
        Some(exact)
    }

    fn build_authored_bv_high_zero_candidate(
        &mut self,
        root: TermId,
        conjuncts: &[TermId],
        authored_scope: &[TermId],
    ) -> Option<Proof> {
        let targets: Vec<HighZeroTarget> = conjuncts
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(index, conjunct)| {
                decode_high_zero_target(&self.ctx.terms, conjunct, index)
            })
            .take(MAX_HIGH_ZERO_TARGETS + 1)
            .collect();
        if targets.is_empty() || targets.len() > MAX_HIGH_ZERO_TARGETS {
            return None;
        }

        let ult_facts: Vec<UltOneFact> = conjuncts
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(index, conjunct)| decode_ult_one_fact(&self.ctx.terms, conjunct, index))
            .take(MAX_ULT_ONE_FACTS + 1)
            .collect();
        if ult_facts.is_empty() || ult_facts.len() > MAX_ULT_ONE_FACTS {
            return None;
        }

        let edges: Vec<VarEquality> = conjuncts
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(index, conjunct)| decode_var_equality(&self.ctx.terms, conjunct, index))
            .take(MAX_EQUALITY_EDGES + 1)
            .collect();
        if edges.len() > MAX_EQUALITY_EDGES {
            return None;
        }

        let mut candidate_pairs = 0_usize;
        let mut path_edge_visits = MAX_PATH_EDGE_VISITS;
        let mut closed_bv_evaluate_probes = MAX_CLOSED_BV_EVALUATE_PROBES;
        for target in targets {
            for ult in ult_facts
                .iter()
                .copied()
                .filter(|ult| ult.width == target.width)
            {
                candidate_pairs = candidate_pairs.checked_add(1)?;
                if candidate_pairs > MAX_TARGET_ULT_PAIRS {
                    return None;
                }
                let Some(path) =
                    equality_path(&edges, ult.subject, target.subject, &mut path_edge_visits)
                else {
                    continue;
                };
                if let Some(candidate) = self.emit_authored_bv_high_zero_candidate(
                    root,
                    conjuncts,
                    target,
                    ult,
                    &edges,
                    &path,
                    authored_scope,
                    &mut closed_bv_evaluate_probes,
                ) {
                    return Some(candidate);
                }
            }
        }
        None
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_authored_bv_high_zero_candidate(
        &mut self,
        root: TermId,
        conjuncts: &[TermId],
        target: HighZeroTarget,
        ult: UltOneFact,
        edges: &[VarEquality],
        path: &[PathHop],
        authored_scope: &[TermId],
        closed_bv_evaluate_probes: &mut usize,
    ) -> Option<Proof> {
        let mut candidate = Proof::new();
        let root_assume = candidate.add_assume(root, Some("authored_bv_high_zero".to_string()));

        let ult_unit = emit_conjunct_unit(
            &mut self.ctx.terms,
            &mut candidate,
            root,
            root_assume,
            conjuncts,
            ult.conjunct_index,
        )?;

        // Independently prove `y <u 1 <=> y = 0`.  This exact unit equality
        // is both re-bit-blasted by AY and lowered by the Alethe printer's
        // checked 64-bit pseudo-Boolean template.
        let zero_equality = raw_equality(&mut self.ctx.terms, ult.subject, target.zero)?;
        let zero_equivalence = raw_equality(&mut self.ctx.terms, ult.literal, zero_equality)?;
        if !ay_proof::recognize_bv_bitblast(&self.ctx.terms, &[zero_equivalence]) {
            return None;
        }
        let zero_equivalence_unit = candidate.add_theory_lemma_with_kind(
            "bv",
            vec![zero_equivalence],
            TheoryLemmaKind::BvBitBlast,
        );
        let not_equivalence = raw_not(&mut self.ctx.terms, zero_equivalence)?;
        let not_ult = raw_not(&mut self.ctx.terms, ult.literal)?;
        let implication = candidate.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_equivalence, not_ult, zero_equality],
            Vec::new(),
            Vec::new(),
        );
        let implication = candidate.add_resolution(
            vec![not_ult, zero_equality],
            zero_equivalence,
            implication,
            zero_equivalence_unit,
        );
        let mut current_zero_unit =
            candidate.add_resolution(vec![zero_equality], ult.literal, implication, ult_unit);
        let mut current_zero_equality = zero_equality;
        let mut current_subject = ult.subject;

        // Transport the zero value along the exact authored variable-equality
        // path, orienting each edge explicitly with `symm` when necessary.
        for hop in path {
            if hop.from != current_subject {
                return None;
            }
            let edge = *edges.get(hop.edge_index)?;
            let edge_unit = emit_conjunct_unit(
                &mut self.ctx.terms,
                &mut candidate,
                root,
                root_assume,
                conjuncts,
                edge.conjunct_index,
            )?;
            let toward_zero = raw_equality(&mut self.ctx.terms, hop.to, hop.from)?;
            let toward_zero_unit = if toward_zero == edge.equality {
                edge_unit
            } else {
                candidate.add_rule_step(
                    AletheRule::Symm,
                    vec![toward_zero],
                    vec![edge_unit],
                    Vec::new(),
                )
            };
            let next_zero = raw_equality(&mut self.ctx.terms, hop.to, target.zero)?;
            current_zero_unit = candidate.add_rule_step(
                AletheRule::Trans,
                vec![next_zero],
                vec![toward_zero_unit, current_zero_unit],
                Vec::new(),
            );
            current_zero_equality = next_zero;
            current_subject = hop.to;
        }
        if current_subject != target.subject {
            return None;
        }

        // Rebuild the target context with x replaced by the literal zero.  Raw
        // applications preserve the exact heads/indices needed by `cong` and
        // by Carcara's directional `evaluate` rule.
        let double_width = target.width.checked_mul(2)?;
        let TermData::App(extend_symbol, _) = self.ctx.terms.get(target.extended).clone() else {
            return None;
        };
        let extended_zero = raw_application(
            &mut self.ctx.terms,
            extend_symbol,
            &[target.zero],
            Sort::bitvec(double_width),
        )?;
        let extend_equality = raw_equality(&mut self.ctx.terms, target.extended, extended_zero)?;
        let extend_unit = candidate.add_rule_step(
            AletheRule::Cong,
            vec![extend_equality],
            vec![current_zero_unit],
            Vec::new(),
        );

        let TermData::App(mul_symbol, _) = self.ctx.terms.get(target.product).clone() else {
            return None;
        };
        let product_zero = raw_application(
            &mut self.ctx.terms,
            mul_symbol,
            &[extended_zero, target.multiplier],
            Sort::bitvec(double_width),
        )?;
        let product_equality = raw_equality(&mut self.ctx.terms, target.product, product_zero)?;
        let product_unit = candidate.add_rule_step(
            AletheRule::Cong,
            vec![product_equality],
            vec![extend_unit],
            Vec::new(),
        );

        let TermData::App(extract_symbol, _) = self.ctx.terms.get(target.extracted).clone() else {
            return None;
        };
        let extracted_zero = raw_application(
            &mut self.ctx.terms,
            extract_symbol,
            &[product_zero],
            Sort::bitvec(target.width),
        )?;
        let extract_equality = raw_equality(&mut self.ctx.terms, target.extracted, extracted_zero)?;
        let extract_unit = candidate.add_rule_step(
            AletheRule::Cong,
            vec![extract_equality],
            vec![product_unit],
            Vec::new(),
        );

        let evaluated = raw_equality(&mut self.ctx.terms, extracted_zero, target.zero)?;
        *closed_bv_evaluate_probes = closed_bv_evaluate_probes.checked_sub(1)?;
        if !ay_proof::recognize_bv_ground_evaluate(&self.ctx.terms, &[evaluated]) {
            return None;
        }
        let evaluated_unit = candidate.add_rule_step(
            AletheRule::Evaluate,
            vec![evaluated],
            Vec::new(),
            Vec::new(),
        );
        let target_equality_unit = candidate.add_rule_step(
            AletheRule::Trans,
            vec![target.equality],
            vec![extract_unit, evaluated_unit],
            Vec::new(),
        );

        let disequality_unit = emit_conjunct_unit(
            &mut self.ctx.terms,
            &mut candidate,
            root,
            root_assume,
            conjuncts,
            target.conjunct_index,
        )?;
        if conjuncts.get(target.conjunct_index) != Some(&target.disequality) {
            return None;
        }
        candidate.add_resolution(
            Vec::new(),
            target.equality,
            disequality_unit,
            target_equality_unit,
        );

        // Keep the explicit variable alive as a structural guard: if a future
        // edit accidentally changes the transported equality, the target's
        // subject equality must still be the one the path produced.
        if current_zero_equality != raw_equality(&mut self.ctx.terms, target.subject, target.zero)?
        {
            return None;
        }
        if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, authored_scope)
            .is_err()
            || !Self::proof_derives_empty_clause(&candidate)
        {
            return None;
        }
        let quality = ay_proof::check_proof_strict_with_context(
            &candidate,
            &self.ctx.terms,
            None,
            None,
            Some(authored_scope),
        )
        .ok()?;
        quality.is_complete().then_some(candidate)
    }
}

fn authored_bv_high_zero_shape_present(terms: &TermStore, conjuncts: &[TermId]) -> bool {
    conjuncts
        .iter()
        .copied()
        .enumerate()
        .any(|(index, conjunct)| decode_high_zero_target(terms, conjunct, index).is_some())
        && conjuncts
            .iter()
            .copied()
            .enumerate()
            .any(|(index, conjunct)| decode_ult_one_fact(terms, conjunct, index).is_some())
}

/// Iteratively admit only a bounded QF_BV surface before the recursive raw
/// builder sees it. The frontend parser deliberately supports far deeper terms
/// than an ordinary Rust call stack, so relying on parse success here would
/// make a proof-repair attempt a stack-overflow vector. `scheduled` counts a
/// child when it is pushed, which also prevents one enormous flat application
/// from allocating an over-cap work stack before the gate can decline it.
fn qfbv_surface_within_shared_authored_rebuild_budget(
    root: &FrontendTerm,
    aggregate_nodes_left: &mut usize,
    aggregate_token_bytes_left: &mut usize,
) -> bool {
    if *aggregate_nodes_left == 0 {
        return false;
    }
    *aggregate_nodes_left -= 1;
    let mut scheduled = 1_usize;
    let mut stack = vec![(root, 0_usize)];
    while let Some((term, depth)) = stack.pop() {
        if depth > MAX_AUTHORED_SURFACE_DEPTH {
            return false;
        }
        let children = match term {
            FrontendTerm::Const(constant) => {
                let token = match constant {
                    FrontendConstant::True | FrontendConstant::False => None,
                    FrontendConstant::Hexadecimal(token) | FrontendConstant::Binary(token) => {
                        Some(token.as_str())
                    }
                    // Integer/decimal/string constants are outside QF_BV raw
                    // rebuilding. `Constant` is non-exhaustive, so future
                    // payload variants also decline until charged explicitly.
                    FrontendConstant::Numeral(_)
                    | FrontendConstant::Decimal(_)
                    | FrontendConstant::String(_) => return false,
                    _ => return false,
                };
                if token.is_some_and(|token| {
                    !spend_authored_surface_token_bytes(aggregate_token_bytes_left, token)
                }) {
                    return false;
                }
                continue;
            }
            FrontendTerm::Symbol(name) => {
                if !spend_authored_surface_token_bytes(aggregate_token_bytes_left, name) {
                    return false;
                }
                continue;
            }
            FrontendTerm::App(name, children) => {
                if !spend_authored_surface_token_bytes(aggregate_token_bytes_left, name) {
                    return false;
                }
                children
            }
            FrontendTerm::IndexedApp(name, indices, children) => {
                if indices.is_empty() || indices.len() > 2 {
                    // Every QF_BV indexed spelling rebuilt below has one index,
                    // except `extract`, which has two. Bound the index vector's
                    // structural clone cost independently of its token bytes.
                    return false;
                }
                if name
                    .strip_prefix("bv")
                    .is_some_and(|digits| digits.len() > MAX_AUTHORED_DECIMAL_TOKEN_DIGITS)
                {
                    // The only supported indexed name with an owned decimal
                    // payload is `bvN`. Conservatively refuse any enormous
                    // `bv`-prefixed name before checking/parsing its digits.
                    return false;
                }
                if !spend_authored_surface_token_bytes(aggregate_token_bytes_left, name) {
                    return false;
                }
                for index in indices {
                    let FrontendIndex::Numeral(token) = index else {
                        // QF_BV indexed rebuilding accepts numeral indices
                        // only. Every other current or future payload variant
                        // fails before clone/parsing.
                        return false;
                    };
                    if token.len() > MAX_AUTHORED_DECIMAL_TOKEN_DIGITS {
                        return false;
                    }
                    if !spend_authored_surface_token_bytes(aggregate_token_bytes_left, token) {
                        return false;
                    }
                }
                children
            }
            _ => return false,
        };
        scheduled = match scheduled.checked_add(children.len()) {
            Some(next)
                if next <= MAX_AUTHORED_SURFACE_NODES
                    && children.len() <= *aggregate_nodes_left =>
            {
                *aggregate_nodes_left -= children.len();
                next
            }
            _ => return false,
        };
        let child_depth = match depth.checked_add(1) {
            Some(next) if next <= MAX_AUTHORED_SURFACE_DEPTH => next,
            _ if children.is_empty() => continue,
            _ => return false,
        };
        stack.extend(children.iter().map(|child| (child, child_depth)));
    }
    true
}

#[cfg(test)]
fn qfbv_surface_within_authored_rebuild_budget(root: &FrontendTerm) -> bool {
    let mut aggregate_nodes_left = MAX_AUTHORED_SURFACE_NODES;
    let mut aggregate_token_bytes_left = MAX_AUTHORED_SURFACE_TOKEN_BYTES;
    qfbv_surface_within_shared_authored_rebuild_budget(
        root,
        &mut aggregate_nodes_left,
        &mut aggregate_token_bytes_left,
    )
}

fn spend_authored_surface_token_bytes(bytes_left: &mut usize, token: &str) -> bool {
    let Some(remaining) = bytes_left.checked_sub(token.len()) else {
        return false;
    };
    *bytes_left = remaining;
    true
}

/// Return only roots that have already passed the iterative surface gate.
/// Production code is permitted to clone a parsed tree only through an index
/// returned here, making the pre-clone ordering explicit and regression-testable.
fn admitted_qfbv_surface_indices(surfaces: &[FrontendTerm]) -> Option<Vec<usize>> {
    if surfaces.is_empty() || surfaces.len() > MAX_AUTHORED_ROOTS {
        return None;
    }
    let mut aggregate_nodes_left = MAX_AUTHORED_SURFACE_NODES;
    let mut aggregate_token_bytes_left = MAX_AUTHORED_SURFACE_TOKEN_BYTES;
    let mut admitted = Vec::new();
    for (index, surface) in surfaces.iter().enumerate() {
        if aggregate_nodes_left == 0 || aggregate_token_bytes_left == 0 {
            break;
        }
        if qfbv_surface_within_shared_authored_rebuild_budget(
            surface,
            &mut aggregate_nodes_left,
            &mut aggregate_token_bytes_left,
        ) {
            admitted.push(index);
        }
    }
    Some(admitted)
}

#[cfg(test)]
mod tests;
