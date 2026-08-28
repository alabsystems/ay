// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-authored-conjunction refutation: rebuilds a refutation from one
//! immutable authored `and` root by deriving its leaves, plus the root-surface
//! restore that runs after the strict commit gate.

use super::*;

// Route tags cannot collide with an `and` operand index: the source
// audit bounds every authored connective far below `u32::MAX`.
const NEGATED_IMPLIES_ANTECEDENT: u32 = u32::MAX;
const NEGATED_IMPLIES_CONSEQUENT: u32 = u32::MAX - 1;

impl Executor {
    /// Rebuild a trust-bearing refutation directly from one exact authored
    /// conjunction.
    ///
    /// Native API consumers commonly submit a theorem as one negated
    /// implication. Canonical Boolean elaboration turns
    /// `not (A -> C)` into an `and` whose leaves are the antecedent facts and
    /// `not C`; solver preprocessing then reasons over those leaves.  A leaf is
    /// not itself an authored assertion, so retaining it as an `Assume` or
    /// relabelling it as `trust` is invalid.  This reconstruction instead:
    ///
    /// 1. assumes only the immutable authored root;
    /// 2. derives every leaf with checked `and_pos` + resolution steps; and
    /// 3. proves the contradiction with reconstructed Farkas, an exportable
    ///    congruence/linear-identity chain, or strict EUF transitivity.
    ///
    /// Every candidate is atomically replayed by the strict checker and its
    /// sole assumption is independently checked against the exact source scope.
    pub(super) fn replace_with_exact_authored_conjunct_refutation(
        &mut self,
        proof: &mut Proof,
        entry: RepairEntry,
    ) {
        if entry == RepairEntry::Check && self.authored_cascade_publishable(proof) {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        let surfaces = AuthoredSurfaces {
            parsed: self.ctx.assertions_parsed().to_vec(),
            originals: self.proof_original_problem_assertions(),
        };
        for &root in &authored {
            let Some(skeleton) = ConjunctSkeleton::decode(&mut self.ctx.terms, root) else {
                continue;
            };

            if let Some(candidate) =
                build_affine_equality_refutation(&mut self.ctx.terms, &skeleton)
            {
                if self.commit_conjunct_candidate(proof, candidate, &authored, root, &surfaces) {
                    return;
                }
            }

            for (kind, farkas, boolean_rule) in
                collect_theory_candidates(&self.ctx.terms, &skeleton.blocking_clause)
            {
                let Some(candidate) = build_theory_resolution_candidate(
                    &mut self.ctx.terms,
                    &skeleton,
                    kind,
                    farkas,
                    boolean_rule,
                ) else {
                    continue;
                };
                if self.commit_conjunct_candidate(proof, candidate, &authored, root, &surfaces) {
                    return;
                }
            }
        }
    }

    /// Offer one reconstructed candidate to the strict commit gate and, when
    /// it is accepted, restore the authored root's exact surface spelling.
    ///
    /// Assumes `candidate` refutes `root` from the root assumption alone and
    /// that `authored` is the exact immutable source scope. Returns whether
    /// the candidate was committed; the search stops on `true`.
    fn commit_conjunct_candidate(
        &mut self,
        proof: &mut Proof,
        candidate: Proof,
        authored: &[TermId],
        root: TermId,
        surfaces: &AuthoredSurfaces,
    ) -> bool {
        if !self.commit_if_strictly_checked(proof, candidate, authored) {
            return false;
        }
        self.restore_authored_root_surfaces_after_rebuild(
            &[root],
            &surfaces.originals,
            &surfaces.parsed,
        );
        true
    }

    /// Restore only the exact authored spelling of the assumed root after the
    /// canonical conjunction reconstruction has passed its strict commit
    /// gate. Derived operands keep their checker-validated canonical spelling;
    /// the root override affects the `assume` line and the negative gate in
    /// `and_pos`, which the Alethe printer validates as exact complements.
    pub(super) fn restore_authored_root_surfaces_after_rebuild(
        &mut self,
        roots: &[TermId],
        originals: &[TermId],
        parsed: &[FrontendTerm],
    ) {
        if !super::super::proof_surface_syntax::surface_override_roots_have_bounded_work(
            &self.ctx.terms,
            roots.iter().copied(),
        ) {
            return;
        }
        let mut overrides = self.last_proof_term_overrides.clone().unwrap_or_default();
        if !super::super::proof_surface_syntax::surface_override_map_is_bounded(&overrides) {
            return;
        }
        for &root in roots {
            let Some(index) = originals.iter().position(|&term| term == root) else {
                return;
            };
            let Some(source) = parsed.get(index) else {
                return;
            };
            super::super::proof_surface_syntax::collect_root_surface_term_override(
                &mut self.ctx,
                root,
                source,
                &mut overrides,
            );
        }
        if !super::super::proof_surface_syntax::surface_override_map_is_bounded(&overrides) {
            return;
        }
        self.last_proof_term_overrides = Some(overrides);
    }
}

/// The exact authored source surfaces consulted after a successful commit, so
/// the assumed root can be respelled the way the problem file wrote it.
struct AuthoredSurfaces {
    originals: Vec<TermId>,
    parsed: Vec<FrontendTerm>,
}

/// One authored conjunction root decoded into everything the reconstruction
/// lanes need: the leaves with the projection path that derives each of them,
/// the clause that contradicts all leaves at once, and the pivot literal used
/// to resolve each leaf's derived unit against that clause.
///
/// `leaves`, `blocking_clause` and `pivots` are index-aligned by construction.
struct ConjunctSkeleton {
    root: TermId,
    leaves: Vec<(TermId, Vec<u32>)>,
    blocking_clause: Vec<TermId>,
    pivots: Vec<TermId>,
}

impl ConjunctSkeleton {
    /// Decode one authored root into a refutable leaf set.
    ///
    /// Prefers the exact `not (=> A B)` shape, whose leaves are the antecedent
    /// conjuncts plus the negated consequent, each tagged with the route the
    /// implication rules take; otherwise falls back to plain `and` flattening,
    /// which never yields the root itself as a leaf. Returns `None` when the
    /// root has fewer than two leaves (nothing to refute against) or more than
    /// the bound, so the caller skips the root.
    fn decode(terms: &mut TermStore, root: TermId) -> Option<Self> {
        const MAX_AUTHORED_CONJUNCTS: usize = 64;
        let mut leaves = Vec::new();
        let root_shape = terms.get(root).clone();
        if let TermData::Not(implication) = root_shape {
            if let TermData::App(Symbol::Named(operator), args) = terms.get(implication).clone() {
                if operator == "=>" && args.len() == 2 {
                    let mut antecedent_leaves = Vec::new();
                    collect_leaves(
                        terms,
                        args[0],
                        &mut Vec::new(),
                        &mut antecedent_leaves,
                        true,
                    );
                    for (leaf, mut path) in antecedent_leaves {
                        path.insert(0, NEGATED_IMPLIES_ANTECEDENT);
                        leaves.push((leaf, path));
                    }
                    let not_consequent = terms.mk_not_raw(args[1]);
                    leaves.push((not_consequent, vec![NEGATED_IMPLIES_CONSEQUENT]));
                }
            }
        }
        if leaves.is_empty() {
            collect_leaves(terms, root, &mut Vec::new(), &mut leaves, false);
        }
        if leaves.len() < 2 || leaves.len() > MAX_AUTHORED_CONJUNCTS {
            return None;
        }
        let (blocking_clause, pivots) = build_blocking_clause(terms, &leaves);
        Some(Self {
            root,
            leaves,
            blocking_clause,
            pivots,
        })
    }
}

/// Flatten nested `and` applications into their leaves, recording the operand
/// path that reaches each one.
///
/// Assumes `path` starts empty at the caller's root. `include_root` decides
/// whether a non-`and` term at depth zero counts as its own leaf: the
/// implication route needs that (the antecedent may be a single fact), the
/// plain conjunction route does not.
fn collect_leaves(
    terms: &TermStore,
    term: TermId,
    path: &mut Vec<u32>,
    leaves: &mut Vec<(TermId, Vec<u32>)>,
    include_root: bool,
) {
    if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
        if name == "and" {
            for (position, &child) in args.iter().enumerate() {
                path.push(position as u32);
                collect_leaves(terms, child, path, leaves, true);
                path.pop();
            }
            return;
        }
    }
    if include_root || !path.is_empty() {
        leaves.push((term, path.clone()));
    }
}

/// Build the clause that contradicts every leaf at once, together with the
/// pivot literal that resolves each leaf's derived unit against it.
///
/// Assumes every leaf is a literal: a negated leaf contributes its inner atom
/// as both blocking literal and pivot; a positive leaf contributes its
/// negation as the blocking literal and itself as the pivot. Both vectors stay
/// index-aligned with `leaves`.
fn build_blocking_clause(
    terms: &mut TermStore,
    leaves: &[(TermId, Vec<u32>)],
) -> (Vec<TermId>, Vec<TermId>) {
    let mut blocking_clause = Vec::with_capacity(leaves.len());
    let mut pivots = Vec::with_capacity(leaves.len());
    for &(leaf, _) in leaves {
        match terms.get(leaf).clone() {
            TermData::Not(inner) => {
                blocking_clause.push(inner);
                pivots.push(inner);
            }
            _ => {
                blocking_clause.push(terms.mk_not_raw(leaf));
                pivots.push(leaf);
            }
        }
    }
    (blocking_clause, pivots)
}

/// Derive one leaf as a unit clause from the sole root assumption.
///
/// Assumes `path` is a route recorded by [`collect_leaves`], optionally
/// prefixed by one of the negated-implication route tags. Walks the route with
/// native Alethe rules only — no generated surrogate is ever assumed — and
/// returns `None` if the route does not match the term shape it addresses.
fn derive_leaf(
    terms: &mut TermStore,
    proof: &mut Proof,
    root_assume: ProofId,
    root: TermId,
    path: &[u32],
) -> Option<ProofId> {
    let mut current_id = root_assume;
    let mut current_term = root;
    let mut positions = path;

    // Stable authored provenance now preserves the exact
    // `not (=> A B)` root instead of authorizing its elaborated
    // `(and A (not B))` surrogate. Derive the two components with the
    // native Alethe implication rules, then continue ordinary
    // `and_pos` projection inside A. No generated surrogate is ever
    // assumed.
    if let Some((&route, rest)) = positions.split_first() {
        if matches!(
            route,
            NEGATED_IMPLIES_ANTECEDENT | NEGATED_IMPLIES_CONSEQUENT
        ) {
            let TermData::Not(implication) = terms.get(root).clone() else {
                return None;
            };
            let TermData::App(Symbol::Named(operator), args) = terms.get(implication).clone()
            else {
                return None;
            };
            if operator != "=>" || args.len() != 2 {
                return None;
            }
            let component = if route == NEGATED_IMPLIES_ANTECEDENT {
                args[0]
            } else {
                terms.mk_not_raw(args[1])
            };
            let rule = if route == NEGATED_IMPLIES_ANTECEDENT {
                AletheRule::ImpliesNeg1
            } else {
                AletheRule::ImpliesNeg2
            };
            let projection =
                proof.add_rule_step(rule, vec![implication, component], Vec::new(), Vec::new());
            current_id =
                proof.add_resolution(vec![component], implication, projection, root_assume);
            current_term = component;
            positions = rest;
            if route == NEGATED_IMPLIES_CONSEQUENT && !positions.is_empty() {
                return None;
            }
        }
    }

    for &position in positions {
        let TermData::App(Symbol::Named(name), args) = terms.get(current_term) else {
            return None;
        };
        if name != "and" {
            return None;
        }
        let child = *args.get(position as usize)?;
        let not_parent = terms.mk_not_raw(current_term);
        let projection = proof.add_rule_step(
            AletheRule::AndPos(position),
            vec![not_parent, child],
            Vec::new(),
            vec![current_term],
        );
        current_id = proof.add_resolution(vec![child], current_term, projection, current_id);
        current_term = child;
    }
    Some(current_id)
}

/// One contradiction strategy for the leaf-resolution lane: a theory-lemma
/// kind with its optional Farkas annotation, or a Boolean Alethe rule stated
/// over the blocking clause.
type ConjunctTheoryCandidate = (
    TheoryLemmaKind,
    Option<FarkasAnnotation>,
    Option<AletheRule>,
);

/// Enumerate the contradiction strategies to try against the blocking clause,
/// in the order they are attempted.
///
/// Assumes `blocking_clause` is the full leaf-complement clause. A Farkas
/// certificate is offered only when the LRA solver reconstructs one that is
/// not a trust placeholder. The EUF alternative is always offered because the
/// strict checker, not this function, decides whether the clause really is a
/// valid transitivity chain.
fn collect_theory_candidates(
    terms: &TermStore,
    blocking_clause: &[TermId],
) -> Vec<ConjunctTheoryCandidate> {
    let mut theory_candidates = Vec::new();
    let mut farkas = None;
    let mut kind = TheoryLemmaKind::Generic;
    if super::super::proof_farkas::try_lra_farkas_reconstruction(
        terms,
        blocking_clause,
        &mut farkas,
        &mut kind,
    ) && !kind.is_trust()
    {
        // A rational Farkas contradiction is valid for both Real and
        // Int domains. Use the strict Farkas rule directly; the LIA
        // annotations describe integer-only arguments and are neither
        // needed nor appropriate for this rational certificate.
        theory_candidates.push((TheoryLemmaKind::LraFarkas, farkas, None));
    }
    // EUF equality transitivity is an Alethe rule rather than a
    // TheoryLemma kind. The strict checker decides whether this exact
    // blocking clause is a valid chain; non-EUF lookalikes fail closed.
    theory_candidates.push((
        TheoryLemmaKind::Generic,
        None,
        Some(AletheRule::EqTransitive),
    ));
    theory_candidates
}

/// Assemble one leaf-resolution candidate: assume the root, derive every leaf
/// by projection, state the contradiction over the blocking clause with the
/// given strategy, then resolve every derived leaf unit away.
///
/// Assumes the skeleton's three vectors are index-aligned and that the
/// blocking clause holds each leaf's complement. Returns `None` whenever the
/// candidate cannot be assembled as expected — a leaf that will not project, a
/// blocking literal missing from the residual, or a residual that does not
/// empty out — and the caller then moves to the next strategy. This function
/// only declines to offer a malformed candidate; the strict checker remains
/// the gate on validity.
fn build_theory_resolution_candidate(
    terms: &mut TermStore,
    skeleton: &ConjunctSkeleton,
    kind: TheoryLemmaKind,
    farkas: Option<FarkasAnnotation>,
    boolean_rule: Option<AletheRule>,
) -> Option<Proof> {
    let mut candidate = Proof::new();
    let root_assume = candidate.add_assume(skeleton.root, None);
    let mut leaf_units = Vec::with_capacity(skeleton.leaves.len());
    for (_, path) in &skeleton.leaves {
        let unit = derive_leaf(terms, &mut candidate, root_assume, skeleton.root, path)?;
        leaf_units.push(unit);
    }

    let mut current = if let Some(rule) = boolean_rule {
        candidate.add_rule_step(
            rule,
            skeleton.blocking_clause.clone(),
            Vec::new(),
            Vec::new(),
        )
    } else {
        candidate.add_step(ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: skeleton.blocking_clause.clone(),
            farkas,
            kind,
            lia: None,
        })
    };
    let mut residual = skeleton.blocking_clause.clone();
    for ((&pivot, &(leaf, _)), &leaf_unit) in skeleton
        .pivots
        .iter()
        .zip(skeleton.leaves.iter())
        .zip(leaf_units.iter())
    {
        let complement = if matches!(terms.get(leaf), TermData::Not(_)) {
            pivot
        } else {
            terms.mk_not_raw(leaf)
        };
        let position = residual.iter().position(|&lit| lit == complement)?;
        let _ = residual.remove(position);
        current = candidate.add_resolution(residual.clone(), pivot, current, leaf_unit);
    }
    if !residual.is_empty() {
        return None;
    }
    Some(candidate)
}

/// The authored equality leaves that justify rewriting one application's
/// arguments, discovered by [`match_argument_equality_premises`].
///
/// All three vectors are index-aligned with the application's argument list:
/// `indices` locates each premise leaf, `equalities` is that leaf's term, and
/// `replacement_args` is the other side of that equality.
struct ArgumentPremises {
    indices: Vec<usize>,
    equalities: Vec<TermId>,
    replacement_args: Vec<TermId>,
}

/// The two derived equalities that bridge the authored premises to the goal.
struct AffineBridge {
    congruence_eq: TermId,
    identity_eq: TermId,
}

/// Why one affine-equality assembly stopped without producing a proof.
enum AffineHalt {
    /// The stitched clause did not collapse to the single expected literal.
    /// The caller tries the next orientation, and the affine search continues.
    NextOrientation,
    /// A leaf projection or a resolution bookkeeping step failed. The whole
    /// affine search abandons, which is what the original `?` propagation did.
    AbandonSearch,
}

/// Build the exportable affine-equality proof used by concrete
/// arithmetic goals such as `x=2 ∧ y=3 ∧ x+y≠5`.
///
/// A single internal Farkas certificate can validate this conflict by
/// case-splitting the disequality.  Alethe `la_generic`, however, has
/// only one signed linear combination and cannot encode both branches.
/// Keep internal and exported proof authority aligned by composing
/// ordinary checkable rules instead:
///
/// * `eq_congruent` transports the authored argument equalities through
///   the arithmetic application;
/// * `LinearIdentity` evaluates the resulting constant affine term;
/// * `eq_transitive` connects those equalities to the authored goal.
///
/// Recognition is deliberately narrow.  Every application argument
/// must have its own positive equality leaf, and the constant bridge
/// must pass the checker's exact linear-identity recognizer.
fn build_affine_equality_refutation(
    terms: &mut TermStore,
    skeleton: &ConjunctSkeleton,
) -> Option<Proof> {
    for (goal_index, &(goal_leaf, ref goal_path)) in skeleton.leaves.iter().enumerate() {
        let TermData::Not(goal_eq) = terms.get(goal_leaf) else {
            continue;
        };
        let goal_eq = *goal_eq;
        let Some((goal_lhs, goal_rhs)) = decode_eq_local(terms, goal_eq) else {
            continue;
        };

        for (source_app, target) in [(goal_lhs, goal_rhs), (goal_rhs, goal_lhs)] {
            if !matches!(terms.sort(source_app), Sort::Int)
                || !matches!(terms.sort(target), Sort::Int)
            {
                continue;
            }
            let TermData::App(source_symbol, source_args) = terms.get(source_app).clone() else {
                continue;
            };
            if source_args.is_empty() {
                continue;
            }

            let Some(premises) =
                match_argument_equality_premises(terms, &skeleton.leaves, goal_index, &source_args)
            else {
                continue;
            };
            let Some(bridge) = build_affine_congruence_bridge(
                terms,
                source_app,
                &source_symbol,
                &premises.replacement_args,
                target,
            ) else {
                continue;
            };
            match assemble_affine_equality_proof(
                terms, skeleton, goal_path, goal_eq, &premises, &bridge,
            ) {
                Ok(candidate) => return Some(candidate),
                Err(AffineHalt::NextOrientation) => continue,
                Err(AffineHalt::AbandonSearch) => return None,
            }
        }
    }
    None
}

/// Match every argument of the candidate application against its own positive
/// equality leaf.
///
/// Assumes `goal_index` is the disequality leaf under refutation, which can
/// never serve as one of its own congruence premises; each argument also
/// consumes a distinct leaf, so no leaf is reused for two arguments. Only
/// positive equalities between terms of the argument's own sort qualify.
/// Returns `None` as soon as one argument has no such leaf: recognition is
/// deliberately narrow and fails closed.
fn match_argument_equality_premises(
    terms: &TermStore,
    leaves: &[(TermId, Vec<u32>)],
    goal_index: usize,
    source_args: &[TermId],
) -> Option<ArgumentPremises> {
    let mut indices = Vec::with_capacity(source_args.len());
    let mut equalities = Vec::with_capacity(source_args.len());
    let mut replacement_args = Vec::with_capacity(source_args.len());
    for &source_arg in source_args {
        let matched = leaves
            .iter()
            .enumerate()
            .find_map(|(leaf_index, &(leaf, _))| {
                if leaf_index == goal_index
                    || indices.contains(&leaf_index)
                    || matches!(terms.get(leaf), TermData::Not(_))
                {
                    return None;
                }
                let (lhs, rhs) = decode_eq_local(terms, leaf)?;
                if lhs == source_arg && terms.sort(rhs) == terms.sort(source_arg) {
                    Some((leaf_index, leaf, rhs))
                } else if rhs == source_arg && terms.sort(lhs) == terms.sort(source_arg) {
                    Some((leaf_index, leaf, lhs))
                } else {
                    None
                }
            });
        let (leaf_index, equality, replacement) = matched?;
        indices.push(leaf_index);
        equalities.push(equality);
        replacement_args.push(replacement);
    }
    Some(ArgumentPremises {
        indices,
        equalities,
        replacement_args,
    })
}

/// Build the two equalities that bridge the authored premises to the goal: the
/// congruence equality `source = replacement` and the constant identity
/// `replacement = target`.
///
/// Assumes `replacement_args` was produced by
/// [`match_argument_equality_premises`] for this same application, so the
/// rewritten application is congruent to it under those premises. Returns
/// `None` when the rewrite is a no-op, or when the constant bridge does not
/// pass the checker's exact linear-identity recognizer; the caller then tries
/// the next orientation.
fn build_affine_congruence_bridge(
    terms: &mut TermStore,
    source_app: TermId,
    source_symbol: &Symbol,
    replacement_args: &[TermId],
    target: TermId,
) -> Option<AffineBridge> {
    let app_sort = terms.sort(source_app).clone();
    let replacement_app = terms.mk_app(source_symbol.clone(), replacement_args, app_sort);
    if replacement_app == source_app {
        return None;
    }
    let congruence_eq = terms.mk_app(
        Symbol::named("="),
        [source_app, replacement_app],
        Sort::Bool,
    );
    let identity_eq = terms.mk_app(Symbol::named("="), [replacement_app, target], Sort::Bool);
    if !ay_core::proof_validation::recognize_lia_linear_identity(terms, &[identity_eq]) {
        return None;
    }
    Some(AffineBridge {
        congruence_eq,
        identity_eq,
    })
}

/// Stitch the whole affine refutation: derive the premise and goal leaves from
/// the sole root assumption, then compose congruence, linear identity and
/// transitivity into the empty clause.
///
/// Assumes `bridge` was built from `premises` for the goal equality, so
/// `eq_transitive` really does connect the two bridge equalities to the goal.
/// Every step is an ordinary checkable rule; the strict checker replays the
/// result before it can be committed.
fn assemble_affine_equality_proof(
    terms: &mut TermStore,
    skeleton: &ConjunctSkeleton,
    goal_path: &[u32],
    goal_eq: TermId,
    premises: &ArgumentPremises,
    bridge: &AffineBridge,
) -> Result<Proof, AffineHalt> {
    let mut candidate = Proof::new();
    let root_assume = candidate.add_assume(skeleton.root, None);
    let mut premise_units = Vec::with_capacity(premises.indices.len());
    for &leaf_index in &premises.indices {
        let unit = derive_leaf(
            terms,
            &mut candidate,
            root_assume,
            skeleton.root,
            &skeleton.leaves[leaf_index].1,
        )
        .ok_or(AffineHalt::AbandonSearch)?;
        premise_units.push(unit);
    }
    let goal_unit = derive_leaf(terms, &mut candidate, root_assume, skeleton.root, goal_path)
        .ok_or(AffineHalt::AbandonSearch)?;

    let congruence_unit = resolve_congruence_equality(
        terms,
        &mut candidate,
        premises,
        &premise_units,
        bridge.congruence_eq,
    )?;

    let identity = candidate.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![bridge.identity_eq],
        farkas: Some(FarkasAnnotation::new(vec![num_rational::Rational64::from(
            1,
        )])),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: Some(ay_core::LiaAnnotation::LinearIdentity),
    });
    let not_congruence = terms.mk_not_raw(bridge.congruence_eq);
    let not_identity = terms.mk_not_raw(bridge.identity_eq);
    let transitivity = candidate.add_rule_step(
        AletheRule::EqTransitive,
        vec![not_congruence, not_identity, goal_eq],
        Vec::new(),
        Vec::new(),
    );
    let goal_from_congruence = candidate.add_resolution(
        vec![not_identity, goal_eq],
        bridge.congruence_eq,
        transitivity,
        congruence_unit,
    );
    let goal = candidate.add_resolution(
        vec![goal_eq],
        bridge.identity_eq,
        goal_from_congruence,
        identity,
    );
    candidate.add_resolution(Vec::new(), goal_eq, goal, goal_unit);
    Ok(candidate)
}

/// Derive the congruence equality as a unit clause: state `eq_congruent` over
/// the whole argument list, then resolve each authored premise equality away.
///
/// Assumes `premise_units` is aligned with `premises.equalities` — one derived
/// unit clause per premise equality, in the same order. The residual must
/// collapse to exactly the congruence equality; any other residual means the
/// clause did not reduce as expected, and the caller tries the next
/// orientation instead of emitting a step it cannot account for.
fn resolve_congruence_equality(
    terms: &mut TermStore,
    candidate: &mut Proof,
    premises: &ArgumentPremises,
    premise_units: &[ProofId],
    congruence_eq: TermId,
) -> Result<ProofId, AffineHalt> {
    let mut congruence_clause = Vec::with_capacity(premises.equalities.len() + 1);
    for &equality in &premises.equalities {
        congruence_clause.push(terms.mk_not_raw(equality));
    }
    congruence_clause.push(congruence_eq);
    let mut congruence_unit = candidate.add_rule_step(
        AletheRule::EqCongruent,
        congruence_clause.clone(),
        Vec::new(),
        Vec::new(),
    );
    let mut residual = congruence_clause;
    for (&equality, &unit) in premises.equalities.iter().zip(premise_units.iter()) {
        let negated = terms.mk_not_raw(equality);
        let position = residual
            .iter()
            .position(|&lit| lit == negated)
            .ok_or(AffineHalt::AbandonSearch)?;
        let _ = residual.remove(position);
        congruence_unit =
            candidate.add_resolution(residual.clone(), equality, congruence_unit, unit);
    }
    if residual != [congruence_eq] {
        return Err(AffineHalt::NextOrientation);
    }
    Ok(congruence_unit)
}
