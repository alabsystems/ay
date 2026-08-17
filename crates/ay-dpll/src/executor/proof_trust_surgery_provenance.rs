// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared policy helpers for provenance-authenticated proof repair.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{Sort, Symbol, TermId};
use ay_frontend::command::Term as FrontendTerm;

use super::proof_surface_syntax::{
    format_frontend_term, parsed_term_is_binder_free, strip_frontend_annotations,
};
use super::Executor;

#[path = "proof_trust_surgery_original_index.rs"]
mod original_index;
pub(in crate::executor) use original_index::{prepare_rebuilt_premise_append, OriginalSourceIndex};
#[path = "proof_trust_surgery_planning_budget.rs"]
mod planning_budget;
#[cfg(test)]
pub(in crate::executor) use planning_budget::MAX_FARKAS_ATTEMPTS;
pub(in crate::executor) use planning_budget::{
    canonical_term_work, surgery_sources_are_bounded, SurgeryPlanningBudget,
};

/// Hard width bound for provenance-driven repair inputs.
pub(super) const MAX_PROVENANCE_REPAIR_TERMS: usize = 64;

pub(super) struct AuthenticatedProvenanceOr {
    pub(super) orig: TermId,
    pub(super) disjuncts: Vec<TermId>,
    pub(super) supports: Vec<TermId>,
    pub(super) authored_sources: Vec<TermId>,
}

pub(in crate::executor) use super::proof_trust_surgery_surface_audit::{
    retained_surface_plan_mix_is_safe, surface_source_is_bounded, surface_source_work,
    ProvenanceSurfaceAudit,
};

/// Require the authored connective's immediate operands to elaborate to the
/// canonical operands in exactly the order used by the proof rules.
///
/// This rejects surface rewrites such as nested/flattened `or` and
/// `(ite (not c) a b)`, whose canonical terms may be equivalent but whose
/// printed Alethe rule has a different positional shape.
pub(in crate::executor) fn immediate_surface_parts_match(
    ctx: &mut ay_frontend::Context,
    parsed: &FrontendTerm,
    expected_head: &str,
    canonical_parts: &[TermId],
) -> bool {
    if !surface_source_is_bounded(parsed) {
        return false;
    }
    let FrontendTerm::App(head, surface_parts) = strip_frontend_annotations(parsed) else {
        return false;
    };
    head == expected_head
        && surface_parts.len() == canonical_parts.len()
        && surface_parts
            .iter()
            .zip(canonical_parts)
            .all(|(surface, &canonical)| ctx.elaborate_surface_subterm(surface) == Some(canonical))
}

pub(super) fn source_set_is_exactly_authored(
    source_set: &[TermId],
    source_index: &OriginalSourceIndex,
) -> bool {
    !source_set.is_empty()
        && source_set.len() <= MAX_PROVENANCE_REPAIR_TERMS
        && source_set
            .iter()
            .all(|&source| source_index.contains(source))
}

fn atom_of(terms: &ay_core::TermStore, literal: TermId) -> TermId {
    let mut atom = literal;
    while let TermData::Not(inner) = terms.get(atom) {
        atom = *inner;
    }
    atom
}

pub(super) fn complement_of(terms: &mut ay_core::TermStore, literal: TermId) -> TermId {
    match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => terms.mk_not_raw(literal),
    }
}

pub(super) fn unique_atoms(terms: &ay_core::TermStore, literals: &[TermId]) -> bool {
    let mut atoms: Vec<TermId> = literals
        .iter()
        .map(|&literal| atom_of(terms, literal))
        .collect();
    atoms.sort_unstable();
    atoms.dedup();
    atoms.len() == literals.len()
}

/// Reject shapes where set-resolution can erase an additional literal before
/// the emitter's ordered bookkeeping reaches it.
pub(super) fn branch_resolution_shape_unambiguous(
    terms: &mut ay_core::TermStore,
    goal: TermId,
    guard: TermId,
    source: TermId,
    lifted: TermId,
    lemma: &[TermId],
) -> bool {
    let source_complement = complement_of(terms, source);
    let lifted_complement = complement_of(terms, lifted);
    if lemma.iter().filter(|&&term| term == lifted).count() != 1
        || lemma
            .iter()
            .filter(|&&term| term == source_complement)
            .count()
            != 1
        || !unique_atoms(terms, lemma)
        || !unique_atoms(terms, &[goal, guard, lifted_complement])
        || !unique_atoms(terms, &[guard, source])
    {
        return false;
    }
    let mut remaining = vec![goal, guard];
    remaining.extend(lemma.iter().copied().filter(|&term| term != lifted));
    unique_atoms(terms, &remaining)
}

pub(super) fn surface_is_direct_arithmetic_literal(
    ctx: &mut ay_frontend::Context,
    parsed: &FrontendTerm,
) -> bool {
    if !surface_source_is_bounded(parsed) {
        return false;
    }
    surface_is_direct_arithmetic_literal_prechecked(ctx, parsed)
}

pub(super) fn surface_is_direct_arithmetic_literal_prechecked(
    ctx: &mut ay_frontend::Context,
    parsed: &FrontendTerm,
) -> bool {
    if !parsed_term_is_binder_free(parsed) {
        return false;
    }
    if !ay_proof::printed_linear_arithmetic_literal_is_supported(&format_frontend_term(parsed)) {
        return false;
    }
    let mut current = strip_frontend_annotations(parsed);
    let mut negations = 0usize;
    while let FrontendTerm::App(op, args) = current {
        if op == "not" && args.len() == 1 {
            negations += 1;
            if negations > 1 {
                return false;
            }
            current = strip_frontend_annotations(&args[0]);
            continue;
        }
        if !matches!(op.as_str(), "=" | "<" | "<=" | ">" | ">=") || args.len() != 2 {
            return false;
        }
        let Some(operands) = args
            .iter()
            .map(|arg| ctx.elaborate_surface_subterm(arg))
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };
        if !operands
            .iter()
            .all(|&term| matches!(ctx.terms.sort(term), Sort::Int | Sort::Real))
        {
            return false;
        }
        let Some(canonical) = ctx.elaborate_surface_subterm(current) else {
            return false;
        };
        let mut atom = canonical;
        while let TermData::Not(inner) = ctx.terms.get(atom) {
            atom = *inner;
        }
        return matches!(
            ctx.terms.get(atom),
            TermData::App(Symbol::Named(canonical_op), canonical_args)
                if matches!(canonical_op.as_str(), "=" | "<" | "<=" | ">" | ">=")
                    && canonical_args.len() == 2
                    && canonical_args.iter().all(|&term| {
                        matches!(ctx.terms.sort(term), Sort::Int | Sort::Real)
                    })
        );
    }
    false
}

pub(super) fn surface_is_direct_equality(parsed: &FrontendTerm) -> bool {
    surface_source_is_bounded(parsed)
        && parsed_term_is_binder_free(parsed)
        && matches!(
            strip_frontend_annotations(parsed),
            FrontendTerm::App(op, args) if op == "=" && args.len() == 2
        )
}

pub(super) fn collect_surface_arithmetic_literals(
    ctx: &mut ay_frontend::Context,
    parsed: &FrontendTerm,
    out: &mut HashSet<TermId>,
) {
    let parsed = strip_frontend_annotations(parsed);
    if surface_is_direct_arithmetic_literal_prechecked(ctx, parsed) {
        if let Some(canonical) = ctx.elaborate_surface_subterm(parsed) {
            out.insert(canonical);
        }
    }
    let FrontendTerm::App(_, args) = parsed else {
        return;
    };
    for arg in args {
        collect_surface_arithmetic_literals(ctx, arg, out);
    }
}

pub(super) fn surface_arithmetic_or_matches(
    ctx: &mut ay_frontend::Context,
    parsed: &FrontendTerm,
    canonical_disjuncts: &[TermId],
) -> bool {
    immediate_surface_parts_match(ctx, parsed, "or", canonical_disjuncts)
        && match strip_frontend_annotations(parsed) {
            FrontendTerm::App(_, parts) => parts
                .iter()
                .all(|part| surface_is_direct_arithmetic_literal(ctx, part)),
            _ => false,
        }
}

pub(in crate::executor) fn surface_or_decomposition_matches(
    ctx: &mut ay_frontend::Context,
    parsed: &FrontendTerm,
    canonical_disjuncts: &[TermId],
) -> bool {
    if !surface_source_is_bounded(parsed) {
        return false;
    }
    match strip_frontend_annotations(parsed) {
        FrontendTerm::App(op, surface_disjuncts) if op == "or" => {
            if surface_disjuncts.len() != canonical_disjuncts.len()
                || surface_disjuncts
                    .iter()
                    .any(|term| !parsed_term_is_binder_free(term))
            {
                return false;
            }
            let Some(mut surface) = surface_disjuncts
                .iter()
                .map(|term| ctx.elaborate_surface_subterm(term))
                .collect::<Option<Vec<_>>>()
            else {
                return false;
            };
            let mut canonical = canonical_disjuncts.to_vec();
            surface.sort_unstable();
            canonical.sort_unstable();
            surface == canonical
        }
        FrontendTerm::App(not, args) if not == "not" && args.len() == 1 => {
            let FrontendTerm::App(and, conjuncts) = strip_frontend_annotations(&args[0]) else {
                return false;
            };
            and == "and"
                && conjuncts.len() == canonical_disjuncts.len()
                && conjuncts.iter().all(parsed_term_is_binder_free)
                && conjuncts
                    .iter()
                    .zip(canonical_disjuncts)
                    .all(|(surface, &canonical)| {
                        ctx.elaborate_surface_subterm(surface)
                            .map(|term| complement_of(&mut ctx.terms, term))
                            == Some(canonical)
                    })
        }
        _ => false,
    }
}

pub(in crate::executor) fn surface_arithmetic_ite_matches(
    ctx: &mut ay_frontend::Context,
    parsed: &FrontendTerm,
    canonical_parts: &[TermId; 3],
) -> bool {
    immediate_surface_parts_match(ctx, parsed, "ite", canonical_parts)
        && match strip_frontend_annotations(parsed) {
            FrontendTerm::App(_, parts) => {
                parsed_term_is_binder_free(&parts[0])
                    && surface_is_direct_arithmetic_literal(ctx, &parts[1])
                    && surface_is_direct_arithmetic_literal(ctx, &parts[2])
            }
            _ => false,
        }
}

/// External `la_generic` signing must be able to see the authored arithmetic
/// atom directly. In particular, a `let` anywhere in the printed row can
/// hide an equality orientation from the signer.
pub(super) fn retained_original_rows_are_signable(
    ctx: &mut ay_frontend::Context,
    retained: &[TermId],
    originals: &[(TermId, FrontendTerm)],
    source_index: &OriginalSourceIndex,
    planning: &mut SurgeryPlanningBudget,
) -> bool {
    retained.iter().all(|support| {
        source_index
            .get(originals, *support)
            .is_none_or(|(_, parsed)| {
                planning.retained_row_is_signable(ctx, *support, parsed) == Some(true)
            })
    })
}

impl Executor {
    pub(super) fn surface_equality_source_is_print_faithful(
        &mut self,
        canonical: TermId,
        parsed: &FrontendTerm,
    ) -> bool {
        if !surface_is_direct_equality(parsed) {
            return false;
        }
        let FrontendTerm::App(_, surface_sides) = strip_frontend_annotations(parsed) else {
            return false;
        };
        let TermData::App(Symbol::Named(op), canonical_sides) =
            self.ctx.terms.get(canonical).clone()
        else {
            return false;
        };
        if op != "=" || canonical_sides.len() != 2 {
            return false;
        }
        let (Some(left), Some(right)) = (
            self.raw_intern_surface(&surface_sides[0]),
            self.raw_intern_surface(&surface_sides[1]),
        ) else {
            return false;
        };
        (left == canonical_sides[0] && right == canonical_sides[1])
            || (left == canonical_sides[1] && right == canonical_sides[0])
    }

    pub(super) fn authenticate_provenance_or(
        &mut self,
        goal: TermId,
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<AuthenticatedProvenanceOr> {
        let TermData::App(Symbol::Named(goal_op), goal_disjuncts) =
            self.ctx.terms.get(goal).clone()
        else {
            return None;
        };
        if goal_op != "or"
            || !(2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&goal_disjuncts.len())
            || source_index.contains(goal)
        {
            return None;
        }
        let source_sets = self
            .proof_problem_assertion_provenance
            .as_ref()?
            .assertion_sources
            .get(&goal)?;
        let [source_set] = source_sets.as_slice() else {
            return None;
        };
        if !source_set_is_exactly_authored(source_set, source_index) {
            return None;
        }

        let mut candidates = Vec::new();
        for &source in source_set {
            let (_, parsed) = source_index.get(originals, source)?;
            if !planning.spend_surface(source, parsed) {
                return None;
            }
            let TermData::App(Symbol::Named(op), disjuncts) = self.ctx.terms.get(source).clone()
            else {
                continue;
            };
            if op == "or"
                && (2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&disjuncts.len())
                && surface_arithmetic_or_matches(&mut self.ctx, parsed, &disjuncts)
            {
                candidates.push((source, disjuncts));
            }
        }
        let mut candidates = candidates.into_iter();
        let (orig, disjuncts) = candidates.next()?;
        if candidates.next().is_some() || orig == goal || !unique_atoms(&self.ctx.terms, &disjuncts)
        {
            return None;
        }
        let supports = source_set
            .iter()
            .copied()
            .filter(|&source| source != orig)
            .collect();
        Some(AuthenticatedProvenanceOr {
            orig,
            disjuncts,
            supports,
            authored_sources: source_set.clone(),
        })
    }
}

#[cfg(test)]
mod tests {
    use ay_frontend::command::{Command, Constant, Sort as FrontendSort, Term as FrontendTerm};

    use super::Executor;

    fn declare_fixture_const(
        executor: &mut Executor,
        name: &str,
        sort: FrontendSort,
    ) -> ay_core::TermId {
        executor
            .ctx
            .process_command(&Command::DeclareConst(name.to_string(), sort))
            .expect("fixture declaration succeeds");
        executor
            .ctx
            .elaborate_surface_subterm(&FrontendTerm::Symbol(name.to_string()))
            .expect("declared fixture symbol elaborates")
    }

    #[test]
    fn substituted_equality_source_must_preserve_printed_operands() {
        let mut executor = Executor::new();
        let x = declare_fixture_const(
            &mut executor,
            "subst_surface_x",
            FrontendSort::Simple("Int".to_string()),
        );
        let y = declare_fixture_const(
            &mut executor,
            "subst_surface_y",
            FrontendSort::Simple("Int".to_string()),
        );
        let canonical = executor.ctx.terms.mk_eq(x, y);
        let exact_reversed = FrontendTerm::App(
            "=".to_string(),
            vec![
                FrontendTerm::Symbol("subst_surface_y".to_string()),
                FrontendTerm::Symbol("subst_surface_x".to_string()),
            ],
        );
        assert!(executor.surface_equality_source_is_print_faithful(canonical, &exact_reversed,));

        let normalized = FrontendTerm::App(
            "=".to_string(),
            vec![
                FrontendTerm::App(
                    "+".to_string(),
                    vec![
                        FrontendTerm::Symbol("subst_surface_x".to_string()),
                        FrontendTerm::Const(Constant::Numeral("0".to_string())),
                    ],
                ),
                FrontendTerm::Symbol("subst_surface_y".to_string()),
            ],
        );
        assert!(!executor.surface_equality_source_is_print_faithful(canonical, &normalized));
    }
}
