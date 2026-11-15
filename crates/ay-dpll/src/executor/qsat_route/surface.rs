// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The problem file's spelling on a QSAT replay proof.
//!
//! The replay proof is installed outside the ordinary assembly, whose input
//! syntax pass gives every authored root its source spelling before the
//! printer plans the checked authored-to-canonical bridges. The final
//! restoration pass (`restore_reachable_authored_assume_surface_overrides`)
//! re-spells only roots whose authored head the printer is known to confine,
//! and leaves the others to "an earlier pass" — which on this route never ran.
//! MEASURED on the route's branch: `(assert (not (and (not p) (not q))))`
//! shipped `(assume t0 (or p q))`, `(assert (=> p q))` shipped `(assume t0 (or
//! q (not p)))`, and pinned carcara rejected both at `t0`, where the legacy
//! route prints `t0.a` with its `and_neg`/`or_neg`/`equiv_*` bridge.
//!
//! The two passes here supply what that earlier pass would have:
//!
//! * every assumed authored root still printed canonically gets its source
//!   spelling, so the printer plans its bridge (or the evidence gate refuses
//!   the document it cannot plan);
//! * every negated-existential dual the replay minted (`qnt_neg_exists`) is
//!   spelled with the AUTHORED binder names. Elaboration alpha-renames the
//!   binder (`x` becomes `x_1`), and the resolution against the authored
//!   `assume` then faced two different printed pivots;
//! * every `forall` conjunct of an authored conjunction, which elaboration
//!   alpha-renames and normalizes (`(+ x1 (* 0 x2) (- 1))` becomes `(+ x1_1
//!   (- 1))`), is spelled as written, so its `and_pos` projection finds it in
//!   the authored root and its `forall_inst` instances are spelled from the
//!   same source body.
//!
//! Spelling grants no authority: the evidence gate reads the rendered
//! document, and every printed step is judged by the printer and by carcara.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{AletheRule, Proof, ProofStep, Sort, TermId, TermStore};
use ay_frontend::command::{Sort as FrontendSort, Term as FrontendTerm};

use super::super::proof_surface_syntax::{
    format_forall_instance_surface, format_frontend_term, strip_frontend_annotations,
    surface_override_map_is_bounded,
};
use super::super::Executor;

/// Authored rows this presentation pass reads.
const MAX_ROWS: usize = 4096;

impl Executor {
    /// Spell the installed replay proof over the problem file (module docs).
    pub(super) fn qsat_spell_replay_proof(&mut self, proof: &Proof) {
        if self.last_unsat_proof_reconstruction_suppressed || !self.ctx.retains_parsed_assertions()
        {
            return;
        }
        let Some(rows) = self
            .ctx
            .concrete_authored_assertion_terms_aligned_bounded(MAX_ROWS)
        else {
            return;
        };
        let mut overrides = self.last_proof_term_overrides.clone().unwrap_or_default();
        let mut changed = self.qsat_spell_assumed_roots(proof, &rows, &mut overrides);
        changed |= self.qsat_spell_nested_quantifiers(proof, &rows, &mut overrides);
        if changed && surface_override_map_is_bounded(&overrides) {
            self.last_proof_term_overrides = Some(overrides);
        }
    }

    /// Give each assumed authored root that has no spelling yet its one source
    /// spelling, where that differs from the canonical rendering.
    fn qsat_spell_assumed_roots(
        &self,
        proof: &Proof,
        rows: &[TermId],
        overrides: &mut HashMap<TermId, String>,
    ) -> bool {
        let assumed: HashSet<TermId> = proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Assume(term) => Some(*term),
                _ => None,
            })
            .collect();
        // `None`: two rows spell one root differently, so no spelling is chosen.
        let mut spellings: HashMap<TermId, Option<String>> = HashMap::default();
        for (&root, row) in rows.iter().zip(self.ctx.assertions_parsed()) {
            if !assumed.contains(&root) {
                continue;
            }
            let surface = format_frontend_term(strip_frontend_annotations(row));
            spellings
                .entry(root)
                .and_modify(|known| {
                    if known.as_deref() != Some(surface.as_str()) {
                        *known = None;
                    }
                })
                .or_insert(Some(surface));
        }
        let mut changed = false;
        for (root, surface) in spellings {
            let Some(surface) = surface else {
                continue;
            };
            if overrides.contains_key(&root)
                || ay_proof::render_term_canonical(&self.ctx.terms, root) == surface
            {
                continue;
            }
            overrides.insert(root, surface);
            changed = true;
        }
        changed
    }

    /// Spell each quantifier of `proof` that elaborated from an authored
    /// quantifier nested in a root: each `qnt_neg_exists` pair `(cl E F)`
    /// with the binder names of the authored `(not E)`, each `forall`
    /// conjunct of an authored conjunction with its source text, and each
    /// `forall_inst` over either with the matching instance spelling.
    fn qsat_spell_nested_quantifiers(
        &self,
        proof: &Proof,
        rows: &[TermId],
        overrides: &mut HashMap<TermId, String>,
    ) -> bool {
        let mut authored = AuthoredQuantifiers::default();
        for (&root, row) in rows.iter().zip(self.ctx.assertions_parsed()) {
            authored.collect(&self.ctx.terms, root, row);
        }
        if authored.exists.is_empty() && authored.foralls.is_empty() {
            return false;
        }
        // Universals whose `forall_inst` instances are spelled from source.
        let mut universals: HashMap<TermId, FrontendTerm> = HashMap::default();
        let mut changed = false;
        for (forall, parsed) in authored.foralls {
            if spell(overrides, forall, format_frontend_term(&parsed)) {
                universals.insert(forall, parsed);
                changed = true;
            }
        }
        for step in &proof.steps {
            let ProofStep::Step {
                rule: AletheRule::QntNegExists,
                clause,
                ..
            } = step
            else {
                continue;
            };
            let [exists, forall] = clause.as_slice() else {
                continue;
            };
            let Some(FrontendTerm::Exists(bindings, body)) = authored.exists.get(exists) else {
                continue;
            };
            let dual = FrontendTerm::Forall(
                bindings.clone(),
                Box::new(FrontendTerm::App("not".to_string(), vec![(**body).clone()])),
            );
            let exists_surface =
                format_frontend_term(&FrontendTerm::Exists(bindings.clone(), body.clone()));
            let dual_surface = format_frontend_term(&dual);
            if !spell(overrides, *exists, exists_surface)
                || !spell(overrides, *forall, dual_surface)
            {
                continue;
            }
            universals.insert(*forall, dual);
            changed = true;
        }
        for step in &proof.steps {
            let Some((parsed, instance, args)) =
                forall_instance_of(&self.ctx.terms, step, &universals)
            else {
                continue;
            };
            if let Some(surface) =
                format_forall_instance_surface(&self.ctx.terms, parsed, args, overrides)
            {
                changed |= spell(overrides, instance, surface);
            }
        }
        changed
    }
}

/// Authored quantifiers nested in the roots, keyed by the internal term each
/// elaborated to.
#[derive(Default)]
struct AuthoredQuantifiers {
    /// An `exists` under a negation (the source of a `qnt_neg_exists` dual).
    exists: HashMap<TermId, FrontendTerm>,
    /// A `forall` conjunct of a conjunction root (a root that IS a `forall`
    /// is spelled by the ordinary restoration pass).
    foralls: HashMap<TermId, FrontendTerm>,
}

impl AuthoredQuantifiers {
    fn collect(&mut self, terms: &TermStore, root: TermId, row: &FrontendTerm) {
        let before = self.exists.len();
        pair_negated_exists(terms, root, row, 0, &mut self.exists);
        if self.exists.len() == before {
            // Elaboration may reorder a clause's literals: one negated
            // existential on each side is still the same one.
            if let ([internal], [authored]) = (
                negated_exists_occurrences(terms, root).as_slice(),
                authored_negated_exists_occurrences(row).as_slice(),
            ) {
                if let (TermData::Exists(bindings, _, _), FrontendTerm::Exists(surface, _)) =
                    (terms.get(*internal), authored)
                {
                    if bindings.len() == surface.len() {
                        self.exists.insert(*internal, (*authored).clone());
                    }
                }
            }
        }
        let (mut internal, mut authored) = (Vec::new(), Vec::new());
        flatten_internal_and(terms, root, &mut internal);
        flatten_authored_and(row, &mut authored);
        if internal.len() < 2 {
            return;
        }
        // Elaboration may fold a ground conjunct away (`(<= (+ (* c 5) (* (-
        // 4) c)) c)` is `true`), so the `forall` leaves are paired in order,
        // only when both sides have the same number of them.
        internal.retain(|&conjunct| matches!(terms.get(conjunct), TermData::Forall(..)));
        authored.retain(|source| matches!(source, FrontendTerm::Forall(..)));
        if internal.len() != authored.len() {
            return;
        }
        let mut pairs = Vec::with_capacity(internal.len());
        for (&conjunct, &source) in internal.iter().zip(&authored) {
            let (TermData::Forall(bindings, _, _), FrontendTerm::Forall(surface, _)) =
                (terms.get(conjunct), source)
            else {
                return;
            };
            if bindings.len() != surface.len()
                || bindings
                    .iter()
                    .zip(surface)
                    .any(|((_, sort), (_, source_sort))| !same_sort_name(sort, source_sort))
            {
                return;
            }
            pairs.push((conjunct, source.clone()));
        }
        self.foralls.extend(pairs);
    }
}

/// Whether an internal binder sort is the authored one (compared by name:
/// the arithmetic and Boolean sorts this route admits).
fn same_sort_name(sort: &Sort, source: &FrontendSort) -> bool {
    let name = match sort {
        Sort::Bool => "Bool",
        Sort::Int => "Int",
        Sort::Real => "Real",
        _ => return false,
    };
    matches!(source, FrontendSort::Simple(source) if source.as_str() == name)
}

/// The `and`-leaves of an internal term, in order.
fn flatten_internal_and(terms: &TermStore, term: TermId, out: &mut Vec<TermId>) {
    match terms.get(term) {
        TermData::App(symbol, args) if symbol.name() == "and" => {
            for &arg in args {
                flatten_internal_and(terms, arg, out);
            }
        }
        _ => out.push(term),
    }
}

/// The `and`-leaves of an authored term, in order.
fn flatten_authored_and<'a>(row: &'a FrontendTerm, out: &mut Vec<&'a FrontendTerm>) {
    let row = strip_frontend_annotations(row);
    match row {
        FrontendTerm::App(name, operands) if name.as_str() == "and" => {
            for operand in operands {
                flatten_authored_and(operand, out);
            }
        }
        _ => out.push(row),
    }
}

/// Internal `exists` terms in negative position of `term`'s Boolean skeleton
/// (`and`/`or`/`not`); the search stops at the second.
fn negated_exists_occurrences(terms: &TermStore, term: TermId) -> Vec<TermId> {
    let mut found = Vec::new();
    let mut stack = vec![(term, false)];
    while let Some((t, negated)) = stack.pop() {
        match terms.get(t) {
            TermData::Exists(..) if negated => found.push(t),
            TermData::Not(inner) => stack.push((*inner, !negated)),
            TermData::App(symbol, args) if matches!(symbol.name(), "and" | "or") => {
                stack.extend(args.iter().map(|&a| (a, negated)));
            }
            _ => {}
        }
        if found.len() > 1 {
            break;
        }
    }
    found
}

/// Authored `exists` terms in negative position of `row`'s Boolean skeleton;
/// the search stops at the second.
fn authored_negated_exists_occurrences(row: &FrontendTerm) -> Vec<&FrontendTerm> {
    let mut found = Vec::new();
    let mut stack = vec![(row, false)];
    while let Some((t, negated)) = stack.pop() {
        let t = strip_frontend_annotations(t);
        match t {
            FrontendTerm::Exists(..) if negated => found.push(t),
            FrontendTerm::App(name, operands) if name.as_str() == "not" && operands.len() == 1 => {
                stack.push((&operands[0], !negated));
            }
            FrontendTerm::App(name, operands) if matches!(name.as_str(), "and" | "or") => {
                stack.extend(operands.iter().map(|o| (o, negated)));
            }
            _ => {}
        }
        if found.len() > 1 {
            break;
        }
    }
    found
}

/// Record `surface` for `term` unless another spelling is already there;
/// whether `term` now carries `surface`.
fn spell(overrides: &mut HashMap<TermId, String>, term: TermId, surface: String) -> bool {
    match overrides.get(&term) {
        Some(existing) => *existing == surface,
        None => {
            overrides.insert(term, surface);
            true
        }
    }
}

/// `(parsed dual, instance, binder values)` of a `forall_inst` step whose
/// quantifier is one of `duals`.
fn forall_instance_of<'a>(
    terms: &TermStore,
    step: &'a ProofStep,
    duals: &'a HashMap<TermId, FrontendTerm>,
) -> Option<(&'a FrontendTerm, TermId, &'a [TermId])> {
    let ProofStep::Step {
        rule: AletheRule::ForallInst,
        clause,
        args,
        ..
    } = step
    else {
        return None;
    };
    let [implication] = clause.as_slice() else {
        return None;
    };
    let TermData::App(Symbol::Named(name), disjuncts) = terms.get(*implication) else {
        return None;
    };
    let [negated, instance] = disjuncts.as_slice() else {
        return None;
    };
    let TermData::Not(quantifier) = terms.get(*negated) else {
        return None;
    };
    (name == "or")
        .then(|| duals.get(quantifier))
        .flatten()
        .map(|dual| (dual, *instance, args.as_slice()))
}

/// Pair each internal `exists` under a negation of `term` with the authored
/// `exists` it elaborated from, walking `term` and its source `row` in
/// lockstep through `and`/`or`/`not` of equal arity.
fn pair_negated_exists(
    terms: &TermStore,
    term: TermId,
    row: &FrontendTerm,
    depth: usize,
    out: &mut HashMap<TermId, FrontendTerm>,
) {
    const MAX_DEPTH: usize = 8;
    if depth > MAX_DEPTH {
        return;
    }
    let row = strip_frontend_annotations(row);
    match (terms.get(term), row) {
        (TermData::Not(inner), FrontendTerm::App(not, operands))
            if not.as_str() == "not" && operands.len() == 1 =>
        {
            let operand = strip_frontend_annotations(&operands[0]);
            match (terms.get(*inner), operand) {
                (TermData::Exists(bindings, _, _), FrontendTerm::Exists(surface, _))
                    if bindings.len() == surface.len() =>
                {
                    out.insert(*inner, operand.clone());
                }
                // `(not (and .. (exists ..) ..))`: each conjunct is a clause
                // literal `(not E)` of the replay.
                (TermData::App(symbol, args), FrontendTerm::App(name, operands))
                    if symbol.name() == "and" && name == "and" && args.len() == operands.len() =>
                {
                    for (&arg, operand) in args.iter().zip(operands) {
                        if let (
                            TermData::Exists(bindings, _, _),
                            FrontendTerm::Exists(surface, _),
                        ) = (terms.get(arg), strip_frontend_annotations(operand))
                        {
                            if bindings.len() == surface.len() {
                                out.insert(arg, strip_frontend_annotations(operand).clone());
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        // `(not (and A (exists ..)))` interned as its De Morgan `(or (not A)
        // (not E))`: the `or`'s negated literals pair with the `and` operands.
        (TermData::App(symbol, args), FrontendTerm::App(not, negated))
            if symbol.name() == "or" && not.as_str() == "not" && negated.len() == 1 =>
        {
            let FrontendTerm::App(and, operands) = strip_frontend_annotations(&negated[0]) else {
                return;
            };
            if and.as_str() != "and" || args.len() != operands.len() {
                return;
            }
            for (&arg, operand) in args.iter().zip(operands) {
                let operand = strip_frontend_annotations(operand);
                if let TermData::Not(inner) = terms.get(arg) {
                    if let (TermData::Exists(bindings, _, _), FrontendTerm::Exists(surface, _)) =
                        (terms.get(*inner), operand)
                    {
                        if bindings.len() == surface.len() {
                            out.insert(*inner, operand.clone());
                        }
                    }
                }
            }
        }
        (TermData::App(symbol, args), FrontendTerm::App(name, operands))
            if matches!(symbol.name(), "and" | "or")
                && symbol.name() == name
                && args.len() == operands.len() =>
        {
            for (&arg, operand) in args.iter().zip(operands) {
                pair_negated_exists(terms, arg, operand, depth + 1, out);
            }
        }
        _ => {}
    }
}
