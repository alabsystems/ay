// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Symbol, TermId, TermStore, TheoryLemmaKind};

/// Collect assumptions and theory lemmas that are eligible for
/// `th_resolution`-style empty-clause reconstruction.
#[allow(clippy::type_complexity)]
pub(crate) fn collect_assumptions_and_theory_lemmas(
    proof: &Proof,
) -> (Vec<(ProofId, TermId)>, Vec<(ProofId, Vec<TermId>)>) {
    let mut assumptions = Vec::new();
    let mut theory_lemmas = Vec::new();

    for (idx, step) in proof.steps.iter().enumerate() {
        let id = ProofId(idx as u32);
        match step {
            ProofStep::Assume(term) => assumptions.push((id, *term)),
            ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                ..
            } if clause.len() == 1 && premises.is_empty() => assumptions.push((id, clause[0])),
            ProofStep::TheoryLemma { clause, .. } => {
                theory_lemmas.push((id, clause.clone()));
            }
            _ => {}
        }
    }

    (assumptions, theory_lemmas)
}

/// Try to derive the empty clause via a th_resolution chain (#340 Phase 0).
pub(crate) fn try_derive_empty_via_th_resolution(terms: &TermStore, proof: &mut Proof) -> bool {
    let (assumptions, theory_lemmas) = collect_assumptions_and_theory_lemmas(proof);

    if assumptions.is_empty() || theory_lemmas.is_empty() {
        return false;
    }

    for (lemma_id, lemma_clause) in &theory_lemmas {
        if let Some(chain) = match_lemma_against_assumptions(terms, lemma_clause, &assumptions) {
            build_th_resolution_chain(proof, *lemma_id, lemma_clause, chain);
            return true;
        }
    }
    false
}

/// Decode a term as an equality `(= lhs rhs)`, returning the two sides.
fn decode_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Try to derive the empty clause from a pure EUF transitivity contradiction
/// among the equality assumptions.
///
/// When the assumptions contain a set of positive equalities forming a path
/// between the two sides of a negated equality assumption `(not (= x y))`,
/// the conflict is a transitivity contradiction. We synthesize a genuine
/// `eq_transitive` theory lemma
///
///   `(cl (not (= a b)) (not (= b c)) ... (= x y))`
///
/// whose negated-equality premises form the path `x → y`, then resolve it
/// against the corresponding equality assumptions and the `(not (= x y))`
/// assumption to derive the empty clause.
///
/// The emitted lemma is carcara-checkable as `eq_transitive`: the clause
/// structure itself is the certificate (premises form a path, conclusion
/// connects the endpoints).
///
/// This handles QF_UF transitivity benchmarks where the contradiction is
/// found by eager congruence axioms at the SAT level, leaving the proof
/// tracker without an EUF theory lemma to lower. Runs before the SAT-trace
/// reconstruction, which would otherwise emit `trust`.
pub(crate) fn try_derive_empty_via_euf_transitivity(
    terms: &mut TermStore,
    proof: &mut Proof,
) -> bool {
    let (assumptions, _theory_lemmas) = collect_assumptions_and_theory_lemmas(proof);
    if assumptions.len() < 2 {
        return false;
    }

    // Partition assumptions into positive-equality edges and negated equalities.
    // `edge_assumption[eq_term]` maps a positive equality term to the
    // assumption proof id that asserts it.
    let mut edge_assumption: HashMap<TermId, ProofId> = HashMap::default();
    let mut adjacency: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
    let mut neg_eqs: Vec<(ProofId, TermId, TermId, TermId)> = Vec::new();

    for &(id, term) in &assumptions {
        if let TermData::Not(inner) = terms.get(term) {
            if let Some((a, b)) = decode_eq(terms, *inner) {
                // (id, neg_term, a, b) where neg_term = (not (= a b)).
                neg_eqs.push((id, term, a, b));
            }
        } else if let Some((a, b)) = decode_eq(terms, term) {
            if edge_assumption.insert(term, id).is_none() {
                adjacency.entry(a).or_default().push((b, term));
                adjacency.entry(b).or_default().push((a, term));
            }
        }
    }

    if edge_assumption.is_empty() || neg_eqs.is_empty() {
        return false;
    }

    // For determinism, sort adjacency lists by neighbor TermId.
    for neighbors in adjacency.values_mut() {
        neighbors.sort_unstable_by_key(|&(next, _)| next);
    }

    // Resolve the conclusion equality term for each negated-equality assumption
    // up front so we no longer need to borrow `terms` immutably inside the
    // mutating loop below.
    let candidates: Vec<(ProofId, TermId, TermId, TermId)> = neg_eqs
        .iter()
        .filter_map(|&(neg_id, neg_term, goal_lhs, goal_rhs)| {
            let TermData::Not(conclusion_eq) = terms.get(neg_term) else {
                return None;
            };
            Some((neg_id, *conclusion_eq, goal_lhs, goal_rhs))
        })
        .collect();

    for (neg_id, conclusion_eq, goal_lhs, goal_rhs) in candidates {
        let Some(path_edges) = bfs_equality_path(&adjacency, goal_lhs, goal_rhs) else {
            continue;
        };
        if path_edges.is_empty() {
            continue;
        }

        // Build the eq_transitive clause: negated path edges, then the positive
        // conclusion equality (= goal_lhs goal_rhs). The conclusion is exactly
        // the inner term of the negated-equality assumption.
        let mut lemma_clause: Vec<TermId> = Vec::with_capacity(path_edges.len() + 1);
        let mut neg_edge_for: HashMap<TermId, TermId> = HashMap::default();
        for &edge_eq in &path_edges {
            // Negated edge literal `(not (= a b))`. `mk_not_raw` hash-conses,
            // so this reuses the existing term when one is already interned.
            let neg_lit = terms.mk_not_raw(edge_eq);
            neg_edge_for.insert(edge_eq, neg_lit);
            lemma_clause.push(neg_lit);
        }
        lemma_clause.push(conclusion_eq);

        // Record the EUF transitivity lemma.
        let lemma_id = proof.add_step(ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: lemma_clause.clone(),
            farkas: None,
            kind: TheoryLemmaKind::EufTransitive,
            lia: None,
        });

        // Resolve the lemma against the edge assumptions (removing each negated
        // edge literal) and finally against the disequality assumption
        // (removing the positive conclusion literal) to reach the empty clause.
        let mut resolution_chain: Vec<(ProofId, TermId)> = Vec::with_capacity(path_edges.len() + 1);
        for &edge_eq in &path_edges {
            let edge_assume_id = edge_assumption[&edge_eq];
            let neg_lit = neg_edge_for[&edge_eq];
            resolution_chain.push((edge_assume_id, neg_lit));
        }
        resolution_chain.push((neg_id, conclusion_eq));

        let (_, current_clause) =
            apply_th_resolution_chain(proof, lemma_id, &lemma_clause, &resolution_chain);
        debug_assert!(
            current_clause.is_empty(),
            "EUF transitivity th_resolution chain did not derive empty clause"
        );
        return true;
    }

    false
}

/// BFS over the equality graph to find a path of edge-equality terms from
/// `src` to `dst`. Returns the ordered list of equality terms on the path, or
/// `None` if no path exists. An empty path (src == dst) returns `Some(vec![])`.
fn bfs_equality_path(
    adjacency: &HashMap<TermId, Vec<(TermId, TermId)>>,
    src: TermId,
    dst: TermId,
) -> Option<Vec<TermId>> {
    if src == dst {
        return Some(Vec::new());
    }
    let mut parent: HashMap<TermId, (TermId, TermId)> = HashMap::default();
    let mut queue = std::collections::VecDeque::new();
    queue.push_back(src);
    parent.insert(src, (src, TermId(u32::MAX)));

    while let Some(curr) = queue.pop_front() {
        if curr == dst {
            break;
        }
        if let Some(neighbors) = adjacency.get(&curr) {
            for &(next, edge_eq) in neighbors {
                if !parent.contains_key(&next) {
                    parent.insert(next, (curr, edge_eq));
                    queue.push_back(next);
                }
            }
        }
    }

    if !parent.contains_key(&dst) {
        return None;
    }

    let mut path = Vec::new();
    let mut curr = dst;
    while curr != src {
        let (prev, edge_eq) = parent.get(&curr).copied()?;
        path.push(edge_eq);
        curr = prev;
    }
    path.reverse();
    Some(path)
}

/// Try to derive the empty clause from two theory lemmas that each reduce
/// to complementary unit clauses against the active assumptions.
///
/// Performance: the previous implementation recomputed each lemma's
/// reduction-to-unit against *all* assumptions once per outer-loop iteration —
/// `O(L² · A)` assumption scans, which is catastrophic when a bit-blasted BV
/// refutation records thousands of unit theory lemmas against thousands of
/// assumptions (observed: 8937 lemmas × 9207 assumptions → ~7·10¹¹ hash ops,
/// > 60 s). We now index the assumptions once and reduce every lemma to its
/// residual unit exactly once (`O(A + Σ|clause|)`), then pair complementary
/// residual units. The selected `(lhs, rhs)` pair is the same
/// lexicographically-first complementary pair the nested loop would have
/// chosen, so the emitted proof is unchanged (verdict-preserving).
pub(crate) fn try_derive_empty_via_theory_packet_resolution(
    terms: &TermStore,
    proof: &mut Proof,
) -> bool {
    let (assumptions, theory_lemmas) = collect_assumptions_and_theory_lemmas(proof);
    if assumptions.is_empty() || theory_lemmas.len() < 2 {
        return false;
    }

    // Index the assumptions once. `entry(..).or_insert` keeps the FIRST
    // assumption per key, matching the original "first assumption in iteration
    // order resolves the literal" semantics.
    //   assume_by_term:   full assumption term (either polarity) -> first ProofId
    //                     (resolves a lemma literal `(not x)` against an
    //                     assumption asserting `x`, exactly as the original's
    //                     first match branch keyed on the whole assumption term)
    //   neg_assume_inner: inner atom of a `(not atom)` assume    -> first ProofId
    //                     (resolves a positive lemma literal `p` against a
    //                     `(not p)` assumption, as the original's second branch)
    let mut assume_by_term: HashMap<TermId, ProofId> = HashMap::default();
    let mut neg_assume_inner: HashMap<TermId, ProofId> = HashMap::default();
    for &(id, term) in &assumptions {
        assume_by_term.entry(term).or_insert(id);
        if let TermData::Not(inner) = terms.get(term) {
            neg_assume_inner.entry(*inner).or_insert(id);
        }
    }

    // Reduce every lemma to its residual unit exactly once.
    let matched: Vec<Option<(Vec<(ProofId, TermId)>, TermId)>> = theory_lemmas
        .iter()
        .map(|(_, clause)| {
            match_clause_to_unit_indexed(terms, clause, &assume_by_term, &neg_assume_inner)
        })
        .collect();

    for (idx, (lhs_lemma_id, lhs_clause)) in theory_lemmas.iter().enumerate() {
        let Some((lhs_chain, lhs_unit)) = &matched[idx] else {
            continue;
        };

        for (jdx, (rhs_lemma_id, rhs_clause)) in theory_lemmas.iter().enumerate().skip(idx + 1) {
            let Some((rhs_chain, rhs_unit)) = &matched[jdx] else {
                continue;
            };
            if !literals_are_complementary(terms, *lhs_unit, *rhs_unit) {
                continue;
            }

            let lhs_id = apply_th_resolution_chain(proof, *lhs_lemma_id, lhs_clause, lhs_chain).0;
            let rhs_id = apply_th_resolution_chain(proof, *rhs_lemma_id, rhs_clause, rhs_chain).0;
            proof.add_step(ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: vec![],
                premises: vec![lhs_id, rhs_id],
                args: vec![],
            });
            return true;
        }
    }

    false
}

/// Match a theory lemma's literals against assumptions for resolution.
/// Returns the resolution chain if all lemma literals can be resolved.
pub(crate) fn match_lemma_against_assumptions(
    terms: &TermStore,
    lemma_clause: &[TermId],
    assumptions: &[(ProofId, TermId)],
) -> Option<Vec<(ProofId, TermId)>> {
    let mut neg_in_lemma: HashMap<TermId, TermId> = HashMap::default();
    let mut pos_in_lemma: HashMap<TermId, TermId> = HashMap::default();
    for &lit in lemma_clause {
        if let TermData::Not(inner) = terms.get(lit) {
            neg_in_lemma.insert(*inner, lit);
        } else {
            pos_in_lemma.insert(lit, lit);
        }
    }

    let mut remaining_clause: Vec<TermId> = lemma_clause.to_vec();
    let mut resolution_chain: Vec<(ProofId, TermId)> = Vec::new();

    for &(assume_id, assume_term) in assumptions {
        if let Some(lemma_lit) = neg_in_lemma.remove(&assume_term) {
            resolution_chain.push((assume_id, lemma_lit));
            remaining_clause.retain(|&t| t != lemma_lit);
        } else if let TermData::Not(inner) = terms.get(assume_term) {
            if let Some(lemma_lit) = pos_in_lemma.remove(inner) {
                resolution_chain.push((assume_id, lemma_lit));
                remaining_clause.retain(|&t| t != lemma_lit);
            }
        }
    }

    if remaining_clause.is_empty() && !resolution_chain.is_empty() {
        Some(resolution_chain)
    } else {
        None
    }
}

/// Reduce a single theory-lemma clause to its residual literal, resolving away
/// every literal for which a complementary assumption exists, using pre-built
/// assumption indices (`assume_by_term` / `neg_assume_inner` from
/// [`try_derive_empty_via_theory_packet_resolution`]).
///
/// Returns the resolution chain (assumption id + the resolved lemma literal, in
/// first-seen clause order) together with the single residual literal, or
/// `None` when zero or more than one literal position remains unresolved.
///
/// This is the index-accelerated form of the former
/// `match_lemma_against_assumptions_to_unit`: instead of scanning all
/// assumptions per lemma (`O(A)`), each literal is resolved by an `O(1)` index
/// lookup, so a lemma costs `O(|clause|)`. A literal `lit` is resolvable iff an
/// assumption complementary to it was recorded — a `(not inner)` literal is
/// resolved by an assumption asserting `inner` (either polarity), and a positive
/// literal `p` by a `(not p)` assumption — exactly mirroring the original
/// matching. A resolved literal removes *all* of its copies from the residual
/// (as the original `retain` did), so the "exactly one residual position" test
/// is preserved verbatim.
fn match_clause_to_unit_indexed(
    terms: &TermStore,
    lemma_clause: &[TermId],
    assume_by_term: &HashMap<TermId, ProofId>,
    neg_assume_inner: &HashMap<TermId, ProofId>,
) -> Option<(Vec<(ProofId, TermId)>, TermId)> {
    // Decide resolvability per distinct literal (first-seen order) and build the
    // resolution chain for the resolved ones.
    let mut resolvable: HashMap<TermId, bool> = HashMap::default();
    let mut resolution_chain: Vec<(ProofId, TermId)> = Vec::new();
    for &lit in lemma_clause {
        if resolvable.contains_key(&lit) {
            continue;
        }
        // A `(not inner)` literal is resolved by ANY assumption asserting
        // `inner` (either polarity — mirrors the original first branch keyed on
        // the whole assumption term, so a double-negation literal `(not (not z))`
        // is still resolved by a `(not z)` assumption). A positive literal `p`
        // is resolved by a `(not p)` assumption.
        let assume = match terms.get(lit) {
            TermData::Not(inner) => assume_by_term.get(inner),
            _ => neg_assume_inner.get(&lit),
        };
        match assume {
            Some(&assume_id) => {
                resolution_chain.push((assume_id, lit));
                resolvable.insert(lit, true);
            }
            None => {
                resolvable.insert(lit, false);
            }
        }
    }

    // The residual clause is every position whose literal was not resolved
    // (duplicates included). It must be exactly one position for a unit.
    let mut residual_unit: Option<TermId> = None;
    let mut residual_count: usize = 0;
    for &lit in lemma_clause {
        if resolvable.get(&lit) == Some(&false) {
            residual_count += 1;
            if residual_count > 1 {
                return None;
            }
            residual_unit = Some(lit);
        }
    }

    match residual_count {
        1 => residual_unit.map(|unit| (resolution_chain, unit)),
        _ => None,
    }
}

/// Build a th_resolution chain from matched assumptions and lemma.
pub(crate) fn build_th_resolution_chain(
    proof: &mut Proof,
    lemma_id: ProofId,
    lemma_clause: &[TermId],
    resolution_chain: Vec<(ProofId, TermId)>,
) {
    let (_, current_clause) =
        apply_th_resolution_chain(proof, lemma_id, lemma_clause, &resolution_chain);
    debug_assert!(current_clause.is_empty());
}

pub(crate) fn apply_th_resolution_chain(
    proof: &mut Proof,
    lemma_id: ProofId,
    lemma_clause: &[TermId],
    resolution_chain: &[(ProofId, TermId)],
) -> (ProofId, Vec<TermId>) {
    let mut current_clause = lemma_clause.to_vec();
    let mut current_id = lemma_id;

    for &(assume_id, lemma_lit) in resolution_chain {
        current_clause.retain(|&t| t != lemma_lit);
        current_id = proof.add_step(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: current_clause.clone(),
            premises: vec![current_id, assume_id],
            args: vec![],
        });
    }
    (current_id, current_clause)
}

pub(crate) fn literals_are_complementary(terms: &TermStore, lhs: TermId, rhs: TermId) -> bool {
    match terms.get(lhs) {
        TermData::Not(inner) => *inner == rhs,
        _ => matches!(terms.get(rhs), TermData::Not(inner) if *inner == lhs),
    }
}

/// Try to derive the empty clause from contradictory assumptions.
pub(crate) fn try_derive_empty_via_contradictory_assumptions(
    terms: &TermStore,
    proof: &mut Proof,
) -> bool {
    let assumptions: Vec<(ProofId, TermId)> = proof
        .steps
        .iter()
        .enumerate()
        .filter_map(|(idx, step)| match step {
            ProofStep::Assume(term) => Some((ProofId(idx as u32), *term)),
            ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                ..
            } if clause.len() == 1 && premises.is_empty() => Some((ProofId(idx as u32), clause[0])),
            _ => None,
        })
        .collect();

    if assumptions.len() < 2 {
        return false;
    }

    let mut pos_atoms: HashMap<TermId, (ProofId, TermId)> = HashMap::default();
    let mut neg_atoms: Vec<(ProofId, TermId, TermId)> = Vec::new();

    for &(id, term) in &assumptions {
        if let TermData::Not(inner) = terms.get(term) {
            neg_atoms.push((id, term, *inner));
        } else {
            pos_atoms.insert(term, (id, term));
        }
    }

    for (neg_id, _neg_term, inner) in &neg_atoms {
        if let Some(&(pos_id, pos_term)) = pos_atoms.get(inner) {
            proof.add_step(ProofStep::Resolution {
                clause: vec![],
                pivot: pos_term,
                clause1: pos_id,
                clause2: *neg_id,
            });
            return true;
        }
    }

    false
}

/// Try to derive the empty clause from contradictory equality assumptions.
///
/// When the proof contains two assumptions `(= t c1)` and `(= t c2)` with
/// `c1 != c2`, synthesize a `LiaGeneric` theory lemma
/// `(not (= t c1)) (not (= t c2))` with Farkas coefficients and resolve it
/// against the two assumptions to derive the empty clause.
///
/// This handles the case where LIA preprocessing substituted `x -> c1` from
/// `(= x c1)`, making `(= x c2)` trivially false at the SAT level before the
/// theory solver produces a conflict. Without this, the proof falls through to
/// a trust-lemma fallback.
pub(crate) fn try_derive_empty_via_equality_contradiction(
    terms: &mut TermStore,
    proof: &mut Proof,
) -> bool {
    use ay_core::{Sort, Symbol};

    let assumptions: Vec<(ProofId, TermId)> = proof
        .steps
        .iter()
        .enumerate()
        .filter_map(|(idx, step)| match step {
            ProofStep::Assume(term) => Some((ProofId(idx as u32), *term)),
            _ => None,
        })
        .collect();

    if assumptions.len() < 2 {
        return false;
    }

    struct EqInfo {
        proof_id: ProofId,
        eq_term: TermId,
        key: TermId,
        constant: i64,
    }

    let extract_int_const = |term: TermId| -> Option<i64> {
        match terms.get(term) {
            TermData::Const(ay_core::Constant::Int(n)) => n.try_into().ok(),
            _ => None,
        }
    };

    let mut eq_assumptions: Vec<EqInfo> = Vec::new();
    for &(id, term) in &assumptions {
        let (lhs, rhs) = match terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                (args[0], args[1])
            }
            _ => continue,
        };
        if !matches!(terms.sort(lhs), Sort::Int) {
            continue;
        }
        if let Some(c) = extract_int_const(rhs) {
            eq_assumptions.push(EqInfo {
                proof_id: id,
                eq_term: term,
                key: lhs,
                constant: c,
            });
        } else if let Some(c) = extract_int_const(lhs) {
            eq_assumptions.push(EqInfo {
                proof_id: id,
                eq_term: term,
                key: rhs,
                constant: c,
            });
        }
    }

    for i in 0..eq_assumptions.len() {
        for j in (i + 1)..eq_assumptions.len() {
            if eq_assumptions[i].key != eq_assumptions[j].key {
                continue;
            }
            if eq_assumptions[i].constant == eq_assumptions[j].constant {
                continue;
            }

            let a = &eq_assumptions[i];
            let b = &eq_assumptions[j];

            let neg_a = terms.mk_not_raw(a.eq_term);
            let neg_b = terms.mk_not_raw(b.eq_term);
            let clause = vec![neg_a, neg_b];

            let farkas = crate::executor::proof_farkas::synthesize_equality_farkas(terms, &clause);

            let Some(farkas) = farkas else {
                continue;
            };

            let lemma_id = proof.add_step(ProofStep::TheoryLemma {
                theory: String::from("LIA"),
                kind: TheoryLemmaKind::LiaGeneric,
                clause,
                farkas: Some(farkas),
                lia: None,
            });

            let after_first = proof.add_step(ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: vec![neg_b],
                premises: vec![lemma_id, a.proof_id],
                args: vec![],
            });

            proof.add_step(ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: vec![],
                premises: vec![after_first, b.proof_id],
                args: vec![],
            });

            return true;
        }
    }

    false
}

/// Derive the empty clause by adding a trust theory lemma and resolving.
pub(crate) fn derive_empty_via_trust_lemma(terms: &mut TermStore, proof: &mut Proof) {
    let mut assumptions: Vec<(ProofId, TermId)> = proof
        .steps
        .iter()
        .enumerate()
        .filter_map(|(idx, step)| match step {
            ProofStep::Assume(term) => Some((ProofId(idx as u32), *term)),
            ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                ..
            } if clause.len() == 1 && premises.is_empty() => Some((ProofId(idx as u32), clause[0])),
            _ => None,
        })
        .collect();

    // When the proof has no resolvable assumptions (e.g. an array read-over-
    // write conflict recorded purely as single-literal theory lemmas with no
    // Assume steps), anchor the trust closer to those theory-lemma conclusions
    // instead. The lemmas already in the proof are the honest record of the
    // theory conflict; resolving a trust lemma (whose clause is the negation of
    // those conclusions) against them structurally derives the empty clause.
    // This keeps `derive_empty_via_trust_lemma` a guaranteed final fallback for
    // any proof that contains at least one unit-clause derivation.
    if assumptions.is_empty() {
        let mut seen: HashMap<TermId, ()> = HashMap::default();
        for (idx, step) in proof.steps.iter().enumerate() {
            if let ProofStep::TheoryLemma { clause, .. } = step {
                if clause.len() == 1 && seen.insert(clause[0], ()).is_none() {
                    assumptions.push((ProofId(idx as u32), clause[0]));
                }
            }
        }
    }

    if assumptions.is_empty() {
        return;
    }

    let mut negation_map: HashMap<TermId, TermId> = HashMap::default();
    let negated_clause: Vec<TermId> = assumptions
        .iter()
        .map(|&(_, term)| {
            let neg = if let TermData::Not(inner) = terms.get(term) {
                *inner
            } else {
                terms.mk_not_raw(term)
            };
            negation_map.insert(term, neg);
            neg
        })
        .collect();

    // This trust fallback is used during SAT proof reconstruction
    // when resolution cannot derive the empty clause from existing steps.
    // It is an inherent trust step (not a theory lemma), so Generic is correct
    // until proper SAT proof reconstruction eliminates the need for it.
    let lemma_id =
        proof.add_theory_lemma_with_kind("trust", negated_clause.clone(), TheoryLemmaKind::Generic);

    let mut current_clause = negated_clause;
    let mut current_id = lemma_id;

    for (assume_id, assume_term) in &assumptions {
        let neg_term = negation_map[assume_term];
        current_clause.retain(|&t| t != neg_term);

        current_id = proof.add_step(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: current_clause.clone(),
            premises: vec![current_id, *assume_id],
            args: vec![],
        });
    }

    debug_assert!(
        current_clause.is_empty(),
        "trust-lemma th_resolution chain did not derive empty clause"
    );
}
