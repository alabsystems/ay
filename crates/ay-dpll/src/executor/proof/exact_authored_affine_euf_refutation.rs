// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-authored affine/EUF refutation: the mixed LIA/EUF value-conflict lane
//! rebuilt from authored premises as a checked Farkas + congruence +
//! transitivity composition.

use super::*;

/// Ceiling on the authored root set this reconstruction will consider at all.
const MAX_AUTHORED_ROOTS: usize = 64;
/// Ceiling on the pure-linear premise set the Farkas subset search enumerates.
const MAX_ARITH_ROOTS: usize = 12;

/// The pointwise argument equalities backing one congruence step, paired with
/// the unit proofs that establish them.
///
/// `equalities[i]` is `(= source_args[i] goal_args[i])` and `units[i]` is a
/// proof of that single-literal clause inside the candidate being built.
struct ArgumentEqualities {
    equalities: Vec<TermId>,
    units: Vec<ProofId>,
}

/// One authored `(= application value)` orientation that the paired-value lane
/// can use as a congruence endpoint.
#[derive(Clone)]
struct AppValueRoot {
    root: TermId,
    app: TermId,
    value: TermId,
    symbol: Symbol,
    args: Vec<TermId>,
}

/// One candidate pairing for the explicit-disequality lane: the authored
/// disequality to contradict, the application whose value must be transported,
/// and the authored equality that supplies that value.
struct TransportedValuePairing {
    negative_root: TermId,
    goal_equality: TermId,
    goal_app: TermId,
    goal_args: Vec<TermId>,
    value_root: TermId,
    source_app: TermId,
    source_args: Vec<TermId>,
}

/// Whether `term` is an arithmetic term built only from constants, variables,
/// and the linear operators, so that a Farkas certificate can talk about it.
fn is_pure_linear_term(terms: &TermStore, term: TermId) -> bool {
    if !matches!(terms.sort(term), Sort::Int | Sort::Real) {
        return false;
    }
    match terms.get(term) {
        TermData::Const(_) | TermData::Var(..) => true,
        TermData::App(Symbol::Named(operator), args) => match operator.as_str() {
            "+" | "-" | "*" => args.iter().all(|&arg| is_pure_linear_term(terms, arg)),
            _ => args.is_empty(),
        },
        _ => false,
    }
}

/// Whether `literal` (possibly negated) is a binary arithmetic comparison over
/// pure linear terms of a common sort, i.e. an admissible Farkas premise.
fn is_pure_linear_literal(terms: &TermStore, literal: TermId) -> bool {
    let atom = match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => literal,
    };
    let TermData::App(Symbol::Named(operator), args) = terms.get(atom) else {
        return false;
    };
    args.len() == 2
        && matches!(operator.as_str(), "=" | "<" | "<=" | ">" | ">=")
        && terms.sort(args[0]) == terms.sort(args[1])
        && is_pure_linear_term(terms, args[0])
        && is_pure_linear_term(terms, args[1])
}

/// Introduce `term` as an assumption of `candidate`, reusing the existing step
/// if this term was already assumed.
///
/// Assumes the caller only ever passes exact authored roots; nothing here
/// checks problem scope, so `validate_reachable_assumes_in_problem_scope` is
/// what ultimately licenses each assumption.
fn assume_exact(
    candidate: &mut Proof,
    assumptions: &mut Vec<(TermId, ProofId)>,
    term: TermId,
) -> ProofId {
    if let Some((_, id)) = assumptions.iter().find(|(existing, _)| *existing == term) {
        return *id;
    }
    let id = candidate.add_assume(term, None);
    assumptions.push((term, id));
    id
}

/// Derive `conclusion` from a subset of the authored arithmetic roots as a
/// checked Farkas theory lemma resolved against those roots, appending the
/// steps to `candidate` and returning the unit proof.
///
/// Assumes every entry of `arithmetic_roots` is an exact authored root that may
/// be assumed without proof. Returns `None` when the root set is outside the
/// search budget, when no subset yields a reconstructable certificate, or when
/// the resolution does not reduce the lemma to exactly `conclusion`. On the
/// `None` path `candidate` may already have been mutated; callers discard it.
fn derive_affine_literal(
    terms: &mut TermStore,
    candidate: &mut Proof,
    assumptions: &mut Vec<(TermId, ProofId)>,
    arithmetic_roots: &[TermId],
    conclusion: TermId,
) -> Option<ProofId> {
    if arithmetic_roots.is_empty() || arithmetic_roots.len() > MAX_ARITH_ROOTS {
        return None;
    }
    // Prefer smaller premise sets. Besides producing compact proofs,
    // this avoids zero-coefficient baggage that external la_generic
    // checkers disagree about.
    for cardinality in 1..=arithmetic_roots.len() {
        let limit = 1_u64.checked_shl(arithmetic_roots.len() as u32)?;
        for mask in 1_u64..limit {
            if mask.count_ones() as usize != cardinality {
                continue;
            }
            let selected: Vec<TermId> = arithmetic_roots
                .iter()
                .enumerate()
                .filter_map(|(index, &root)| ((mask & (1_u64 << index)) != 0).then_some(root))
                .collect();
            let mut clause: Vec<TermId> = selected
                .iter()
                .map(|&root| terms.mk_not_raw(root))
                .collect();
            clause.push(conclusion);
            let mut farkas = None;
            let mut inferred = TheoryLemmaKind::Generic;
            if !super::super::proof_farkas::try_lra_farkas_reconstruction(
                terms,
                &clause,
                &mut farkas,
                &mut inferred,
            ) {
                continue;
            }
            let farkas = farkas?;
            let mut current = candidate.add_step(ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: clause.clone(),
                farkas: Some(farkas),
                kind: TheoryLemmaKind::LraFarkas,
                lia: None,
            });
            let mut residual = clause;
            for root in selected {
                let negated = terms.mk_not_raw(root);
                let position = residual.iter().position(|&term| term == negated)?;
                let _ = residual.remove(position);
                let premise = assume_exact(candidate, assumptions, root);
                current = candidate.add_resolution(residual.clone(), root, current, premise);
            }
            if residual == [conclusion] {
                return Some(current);
            }
            return None;
        }
    }
    None
}

/// Establish `argument_equality` for one argument position whose two terms are
/// not syntactically identical: derive both `<=` directions by Farkas and glue
/// them with the `la_disequality` split.
///
/// Assumes `argument_equality` is `(= source_arg goal_arg)` and has already
/// been minted in `terms`. Returns `None` when either direction is not
/// derivable from the authored arithmetic roots, which is the caller's signal
/// to abandon this candidate entirely.
fn derive_argument_equality_by_farkas(
    terms: &mut TermStore,
    candidate: &mut Proof,
    assumptions: &mut Vec<(TermId, ProofId)>,
    arithmetic_roots: &[TermId],
    source_arg: TermId,
    goal_arg: TermId,
    argument_equality: TermId,
) -> Option<ProofId> {
    let forward = terms.mk_app(Symbol::named("<="), [source_arg, goal_arg], Sort::Bool);
    let reverse = terms.mk_app(Symbol::named("<="), [goal_arg, source_arg], Sort::Bool);
    let forward_unit =
        derive_affine_literal(terms, candidate, assumptions, arithmetic_roots, forward)?;
    let reverse_unit =
        derive_affine_literal(terms, candidate, assumptions, arithmetic_roots, reverse)?;
    let not_forward = terms.mk_not_raw(forward);
    let not_reverse = terms.mk_not_raw(reverse);
    let split = terms.mk_app(
        Symbol::named("or"),
        [argument_equality, not_forward, not_reverse],
        Sort::Bool,
    );
    let split_unit = candidate.add_rule_step(
        AletheRule::LaDisequality,
        vec![split],
        Vec::new(),
        Vec::new(),
    );
    let split_clause = candidate.add_rule_step(
        AletheRule::Or,
        vec![argument_equality, not_forward, not_reverse],
        vec![split_unit],
        Vec::new(),
    );
    let forward_resolved = candidate.add_resolution(
        vec![argument_equality, not_reverse],
        forward,
        split_clause,
        forward_unit,
    );
    Some(candidate.add_resolution(
        vec![argument_equality],
        reverse,
        forward_resolved,
        reverse_unit,
    ))
}

/// Build the pointwise argument equalities a congruence step over `source_args`
/// and `goal_args` needs, together with their unit proofs.
///
/// Assumes the two argument lists have equal length. Syntactically identical
/// positions are discharged by `eq_reflexive`; differing positions must be
/// entailed by the authored arithmetic roots. Returns `None` as soon as one
/// position is not derivable, leaving `candidate` partially built for the
/// caller to discard.
fn derive_argument_equalities(
    terms: &mut TermStore,
    candidate: &mut Proof,
    assumptions: &mut Vec<(TermId, ProofId)>,
    arithmetic_roots: &[TermId],
    source_args: &[TermId],
    goal_args: &[TermId],
) -> Option<ArgumentEqualities> {
    let mut equalities = Vec::with_capacity(source_args.len());
    let mut units = Vec::with_capacity(source_args.len());
    for (&source_arg, &goal_arg) in source_args.iter().zip(goal_args.iter()) {
        let argument_equality =
            terms.mk_app(Symbol::named("="), [source_arg, goal_arg], Sort::Bool);
        let unit = if source_arg == goal_arg {
            candidate.add_rule_step(
                AletheRule::EqReflexive,
                vec![argument_equality],
                Vec::new(),
                Vec::new(),
            )
        } else {
            derive_argument_equality_by_farkas(
                terms,
                candidate,
                assumptions,
                arithmetic_roots,
                source_arg,
                goal_arg,
                argument_equality,
            )?
        };
        equalities.push(argument_equality);
        units.push(unit);
    }
    Some(ArgumentEqualities { equalities, units })
}

/// Resolve an `eq_congruent` lemma against the argument-equality units to get a
/// unit proof of `(= source_app goal_app)`.
///
/// Assumes `arguments` was derived for exactly this application pair, so every
/// negated argument equality occurs in the congruence clause. Returns the
/// congruence equality together with its unit proof, or `None` when the
/// resolution does not reduce the clause to that single literal.
fn build_congruence_unit(
    terms: &mut TermStore,
    candidate: &mut Proof,
    arguments: &ArgumentEqualities,
    source_app: TermId,
    goal_app: TermId,
) -> Option<(TermId, ProofId)> {
    let congruence_equality = terms.mk_app(Symbol::named("="), [source_app, goal_app], Sort::Bool);
    let mut congruence_clause: Vec<TermId> = arguments
        .equalities
        .iter()
        .map(|&equality| terms.mk_not_raw(equality))
        .collect();
    congruence_clause.push(congruence_equality);
    let mut congruence_unit = candidate.add_rule_step(
        AletheRule::EqCongruent,
        congruence_clause.clone(),
        Vec::new(),
        Vec::new(),
    );
    let mut residual = congruence_clause;
    for (&argument_equality, &argument_unit) in
        arguments.equalities.iter().zip(arguments.units.iter())
    {
        let negated = terms.mk_not_raw(argument_equality);
        let position = residual.iter().position(|&term| term == negated)?;
        let _ = residual.remove(position);
        congruence_unit = candidate.add_resolution(
            residual.clone(),
            argument_equality,
            congruence_unit,
            argument_unit,
        );
    }
    if residual != [congruence_equality] {
        return None;
    }
    Some((congruence_equality, congruence_unit))
}

/// Chain the two authored application/value equalities -- and, when the two
/// applications differ, the congruence equality between them -- into a unit
/// proof of `value_equality`.
///
/// Assumes `congruence`, when present, is a proved unit of
/// `(= source_app goal_app)`, and that `value_equality` is the transitive
/// conclusion of the chain. Both roots are assumed into `candidate` here.
/// Returns `None` when the resolution does not reduce the `eq_transitive`
/// clause to exactly `value_equality`.
fn build_value_equality_chain(
    terms: &mut TermStore,
    candidate: &mut Proof,
    assumptions: &mut Vec<(TermId, ProofId)>,
    source_root: TermId,
    goal_root: TermId,
    congruence: Option<(TermId, ProofId)>,
    value_equality: TermId,
) -> Option<ProofId> {
    let source_assume = assume_exact(candidate, assumptions, source_root);
    let goal_assume = assume_exact(candidate, assumptions, goal_root);
    let mut chain_clause = vec![terms.mk_not_raw(source_root)];
    if let Some((congruence_equality, _)) = congruence {
        chain_clause.push(terms.mk_not_raw(congruence_equality));
    }
    chain_clause.push(terms.mk_not_raw(goal_root));
    chain_clause.push(value_equality);
    let mut value_unit = candidate.add_rule_step(
        AletheRule::EqTransitive,
        chain_clause.clone(),
        Vec::new(),
        Vec::new(),
    );
    let mut residual = chain_clause;
    for (pivot, unit) in std::iter::once((source_root, source_assume))
        .chain(congruence)
        .chain(std::iter::once((goal_root, goal_assume)))
    {
        let negated = terms.mk_not_raw(pivot);
        let position = residual.iter().position(|&term| term == negated)?;
        let _ = residual.remove(position);
        value_unit = candidate.add_resolution(residual.clone(), pivot, value_unit, unit);
    }
    if residual != [value_equality] {
        return None;
    }
    Some(value_unit)
}

impl Executor {
    /// Rebuild the exact mixed LIA/EUF value-conflict lane from authored
    /// premises.
    ///
    /// A common UFLIA refutation is lost when arithmetic preprocessing derives
    /// an argument equality before EUF closes a value conflict:
    ///
    /// `a + b = c, b = 0, f(a) = v, f(c) != v`.
    ///
    /// Reconstruct it as a checked composition: Farkas derives each needed
    /// argument equality, `eq_congruent` transports the application, and
    /// `eq_transitive` transports the known value. Only exact immutable roots
    /// are assumed, and the whole candidate is replayed strictly before use.
    pub(super) fn replace_with_exact_authored_affine_euf_refutation(&mut self, proof: &mut Proof) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return;
        }

        let arithmetic_roots: Vec<TermId> = authored
            .iter()
            .copied()
            .filter(|&root| is_pure_linear_literal(&self.ctx.terms, root))
            .collect();
        if arithmetic_roots.is_empty() || arithmetic_roots.len() > MAX_ARITH_ROOTS {
            return;
        }

        if let Some(candidate) =
            self.try_affine_euf_transported_value_lane(&authored, &arithmetic_roots)
        {
            *proof = candidate;
            return;
        }
        if let Some(candidate) = self.try_affine_euf_paired_value_lane(&authored, &arithmetic_roots)
        {
            *proof = candidate;
        }
    }

    /// Enumerate authored disequalities `f(goal_args) != v` against authored
    /// equalities `f(source_args) = v` and rebuild the first refutation that
    /// replays strictly.
    ///
    /// Assumes `arithmetic_roots` is the pure-linear subset of `authored`. Only
    /// genuine EUF applications are paired; a candidate that fails to build or
    /// fails strict replay simply moves the search on to the next pairing.
    fn try_affine_euf_transported_value_lane(
        &mut self,
        authored: &[TermId],
        arithmetic_roots: &[TermId],
    ) -> Option<Proof> {
        for &negative_root in authored {
            let TermData::Not(goal_equality) = self.ctx.terms.get(negative_root) else {
                continue;
            };
            let goal_equality = *goal_equality;
            let Some((goal_lhs, goal_rhs)) = decode_eq_local(&self.ctx.terms, goal_equality) else {
                continue;
            };
            for (goal_app, value) in [(goal_lhs, goal_rhs), (goal_rhs, goal_lhs)] {
                let TermData::App(goal_symbol, goal_args) = self.ctx.terms.get(goal_app).clone()
                else {
                    continue;
                };
                // This reconstruction is specifically for EUF transport.
                // Interpreted applications such as `count + 1` are not function
                // symbols to pair by congruence here; admitting them sends pure
                // incremental LIA proofs through an exponential subset search.
                if goal_args.is_empty()
                    || is_pure_linear_term(&self.ctx.terms, goal_app)
                    || ay_frontend::is_reserved_symbol(goal_symbol.name())
                {
                    continue;
                }
                for &value_root in authored {
                    if value_root == negative_root || arithmetic_roots.contains(&value_root) {
                        continue;
                    }
                    let Some((value_lhs, value_rhs)) = decode_eq_local(&self.ctx.terms, value_root)
                    else {
                        continue;
                    };
                    for (source_app, source_value) in
                        [(value_lhs, value_rhs), (value_rhs, value_lhs)]
                    {
                        if source_value != value {
                            continue;
                        }
                        let TermData::App(source_symbol, source_args) =
                            self.ctx.terms.get(source_app).clone()
                        else {
                            continue;
                        };
                        if source_symbol != goal_symbol
                            || source_args.len() != goal_args.len()
                            || source_args.is_empty()
                        {
                            continue;
                        }

                        let pairing = TransportedValuePairing {
                            negative_root,
                            goal_equality,
                            goal_app,
                            goal_args: goal_args.clone(),
                            value_root,
                            source_app,
                            source_args,
                        };
                        if let Some(candidate) = self.try_affine_euf_transported_value_refutation(
                            &pairing,
                            authored,
                            arithmetic_roots,
                        ) {
                            return Some(candidate);
                        }
                    }
                }
            }
        }
        None
    }

    /// Rebuild the refutation for one pairing: Farkas-derived argument
    /// equalities feed `eq_congruent`, `eq_transitive` transports the authored
    /// value onto the goal application, and the authored disequality closes the
    /// clause.
    ///
    /// Assumes the enumeration already checked that both applications share a
    /// symbol and a non-empty arity and that they carry the same value.
    /// Returns the candidate only when it derives the empty clause from
    /// authored assumptions and replays strictly; otherwise `None`, and the
    /// partially built candidate is dropped.
    fn try_affine_euf_transported_value_refutation(
        &mut self,
        pairing: &TransportedValuePairing,
        authored: &[TermId],
        arithmetic_roots: &[TermId],
    ) -> Option<Proof> {
        let mut candidate = Proof::new();
        let mut assumptions = Vec::new();
        let arguments = derive_argument_equalities(
            &mut self.ctx.terms,
            &mut candidate,
            &mut assumptions,
            arithmetic_roots,
            &pairing.source_args,
            &pairing.goal_args,
        )?;
        let (congruence_equality, congruence_unit) = build_congruence_unit(
            &mut self.ctx.terms,
            &mut candidate,
            &arguments,
            pairing.source_app,
            pairing.goal_app,
        )?;

        let not_congruence = self.ctx.terms.mk_not_raw(congruence_equality);
        let not_value_root = self.ctx.terms.mk_not_raw(pairing.value_root);
        let transitivity = candidate.add_rule_step(
            AletheRule::EqTransitive,
            vec![not_congruence, not_value_root, pairing.goal_equality],
            Vec::new(),
            Vec::new(),
        );
        let from_congruence = candidate.add_resolution(
            vec![not_value_root, pairing.goal_equality],
            congruence_equality,
            transitivity,
            congruence_unit,
        );
        let value_assume = assume_exact(&mut candidate, &mut assumptions, pairing.value_root);
        let goal_unit = candidate.add_resolution(
            vec![pairing.goal_equality],
            pairing.value_root,
            from_congruence,
            value_assume,
        );
        let negative_assume = assume_exact(&mut candidate, &mut assumptions, pairing.negative_root);
        candidate.add_resolution(
            Vec::new(),
            pairing.goal_equality,
            goal_unit,
            negative_assume,
        );

        if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, authored).is_ok()
            && Self::proof_derives_empty_clause(&candidate)
            && self.check_proof_strict_with_datatypes(&candidate).is_ok()
        {
            return Some(candidate);
        }
        None
    }

    /// Collect the authored `(= application value)` roots the paired-value lane
    /// can use, in both orientations.
    ///
    /// Interpreted, nullary, and reserved applications are skipped for the same
    /// reason as in the transported-value lane, and the value must be
    /// arithmetic and of the application's own sort for a Farkas disequality
    /// between two such values to mean anything.
    fn affine_euf_app_value_roots(&self, authored: &[TermId]) -> Vec<AppValueRoot> {
        let mut app_value_roots = Vec::new();
        for &root in authored {
            let Some((lhs, rhs)) = decode_eq_local(&self.ctx.terms, root) else {
                continue;
            };
            for (app, value) in [(lhs, rhs), (rhs, lhs)] {
                let TermData::App(symbol, args) = self.ctx.terms.get(app).clone() else {
                    continue;
                };
                if args.is_empty()
                    || is_pure_linear_term(&self.ctx.terms, app)
                    || ay_frontend::is_reserved_symbol(symbol.name())
                    || !matches!(self.ctx.terms.sort(value), Sort::Int | Sort::Real)
                    || self.ctx.terms.sort(app) != self.ctx.terms.sort(value)
                {
                    continue;
                }
                app_value_roots.push(AppValueRoot {
                    root,
                    app,
                    value,
                    symbol,
                    args,
                });
            }
        }
        app_value_roots
    }

    /// Enumerate unordered pairs of authored application/value roots and
    /// rebuild the first refutation that replays strictly.
    fn try_affine_euf_paired_value_lane(
        &mut self,
        authored: &[TermId],
        arithmetic_roots: &[TermId],
    ) -> Option<Proof> {
        // The same mixed-theory conflict can be authored without an explicit
        // UF disequality: `f(x) = v1`, `f(y) = v2`, arithmetic entails `x = y`,
        // and `v1 != v2` is itself an unconditional linear theorem (the smoke
        // corpus uses the distinct constants 10 and 20).  Compose that case
        // explicitly as argument equality -> congruence -> value transitivity
        // -> an independently reconstructed Farkas disequality.
        let app_value_roots = self.affine_euf_app_value_roots(authored);

        for source_index in 0..app_value_roots.len() {
            for goal_index in (source_index + 1)..app_value_roots.len() {
                let source = app_value_roots[source_index].clone();
                let goal = app_value_roots[goal_index].clone();
                if let Some(candidate) = self.try_affine_euf_paired_value_refutation(
                    &source,
                    &goal,
                    authored,
                    arithmetic_roots,
                ) {
                    return Some(candidate);
                }
            }
        }
        None
    }

    /// Rebuild the refutation for one application/value pair: congruence over
    /// the derived argument equalities, `eq_transitive` from the two authored
    /// value equalities, and a Farkas disequality between the two values.
    ///
    /// Assumes both entries came from `affine_euf_app_value_roots`; the pair is
    /// re-checked here for a shared symbol, a shared non-empty arity, and a
    /// shared value sort. Returns the candidate only when it derives the empty
    /// clause from authored assumptions and replays strictly.
    fn try_affine_euf_paired_value_refutation(
        &mut self,
        source: &AppValueRoot,
        goal: &AppValueRoot,
        authored: &[TermId],
        arithmetic_roots: &[TermId],
    ) -> Option<Proof> {
        if source.root == goal.root
            || source.symbol != goal.symbol
            || source.args.len() != goal.args.len()
            || source.args.is_empty()
            || self.ctx.terms.sort(source.value) != self.ctx.terms.sort(goal.value)
        {
            return None;
        }

        let (value_equality, value_disequality, value_farkas) =
            self.reconstruct_affine_euf_value_disequality(source.value, goal.value)?;

        let mut candidate = Proof::new();
        let mut assumptions = Vec::new();
        let arguments = derive_argument_equalities(
            &mut self.ctx.terms,
            &mut candidate,
            &mut assumptions,
            arithmetic_roots,
            &source.args,
            &goal.args,
        )?;

        let mut congruence = None;
        if source.app != goal.app {
            congruence = Some(build_congruence_unit(
                &mut self.ctx.terms,
                &mut candidate,
                &arguments,
                source.app,
                goal.app,
            )?);
        }

        let value_unit = build_value_equality_chain(
            &mut self.ctx.terms,
            &mut candidate,
            &mut assumptions,
            source.root,
            goal.root,
            congruence,
            value_equality,
        )?;

        let disequality_unit = candidate.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![value_disequality],
            farkas: Some(value_farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
        candidate.add_resolution(Vec::new(), value_equality, value_unit, disequality_unit);

        if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, authored).is_ok()
            && Self::proof_derives_empty_clause(&candidate)
            && self.check_proof_strict_with_datatypes(&candidate).is_ok()
        {
            return Some(candidate);
        }
        None
    }

    /// Mint `(= source_value goal_value)`, its negation, and a Farkas
    /// certificate for that negation.
    ///
    /// Assumes both values are arithmetic terms of the same sort. Returns the
    /// equality, the disequality, and the certificate, or `None` when no
    /// certificate is available at all.
    fn reconstruct_affine_euf_value_disequality(
        &mut self,
        source_value: TermId,
        goal_value: TermId,
    ) -> Option<(TermId, TermId, FarkasAnnotation)> {
        let value_equality =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [source_value, goal_value], Sort::Bool);
        let value_disequality = self.ctx.terms.mk_not_raw(value_equality);
        let mut value_farkas = None;
        let mut value_kind = TheoryLemmaKind::Generic;
        let reconstructed_value_disequality =
            super::super::proof_farkas::try_lra_farkas_reconstruction(
                &self.ctx.terms,
                &[value_disequality],
                &mut value_farkas,
                &mut value_kind,
            );
        if !reconstructed_value_disequality {
            // The LRA solver constant-folds a ground false equality
            // before it can return a conflict annotation.  The exact
            // one-row equality certificate is canonical; the strict
            // checker below still independently validates it before
            // this candidate can replace the original proof.
            value_farkas = Some(FarkasAnnotation::from_ints(&[1]));
        }
        let value_farkas = value_farkas?;
        Some((value_equality, value_disequality, value_farkas))
    }
}
