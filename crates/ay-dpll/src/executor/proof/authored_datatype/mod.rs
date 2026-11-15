// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod transport;

#[derive(Clone)]
pub(super) struct OwnedLeaf {
    root: TermId,
    path: Vec<u32>,
    term: TermId,
}

pub(super) fn collect_leaves(
    terms: &TermStore,
    root: TermId,
    term: TermId,
    path: &mut Vec<u32>,
    out: &mut Vec<OwnedLeaf>,
) {
    if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
        if name == "and" {
            for (index, &child) in args.iter().enumerate() {
                path.push(index as u32);
                collect_leaves(terms, root, child, path, out);
                path.pop();
            }
            return;
        }
    }
    out.push(OwnedLeaf {
        root,
        path: path.clone(),
        term,
    });
}

pub(super) fn append_owned_leaf(
    terms: &mut TermStore,
    proof: &mut Proof,
    leaf: &OwnedLeaf,
) -> Option<ProofId> {
    let mut current = proof.add_assume(leaf.root, None);
    let mut current_term = leaf.root;
    for &position in &leaf.path {
        let TermData::App(Symbol::Named(name), args) = terms.get(current_term) else {
            return None;
        };
        if name != "and" {
            return None;
        }
        let child = *args.get(position as usize)?;
        let projection = proof.add_rule_step(
            AletheRule::AndPos(position),
            vec![terms.mk_not_raw(current_term), child],
            Vec::new(),
            vec![current_term],
        );
        current = proof.add_resolution(vec![child], current_term, projection, current);
        current_term = child;
    }
    (current_term == leaf.term).then_some(current)
}

fn tester_subject(terms: &TermStore, term: TermId) -> Option<TermId> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    (name.starts_with("is-") && args.len() == 1 && terms.sort(term) == &Sort::Bool)
        .then_some(args[0])
}

/// The constructor argument the declaration-backed registry says
/// `selector(constructor)` projects to, if registered.
pub(super) fn projected_field(
    terms: &TermStore,
    selector_decls: &[(String, Vec<String>)],
    selector: &str,
    constructor: TermId,
) -> Option<TermId> {
    let TermData::App(symbol @ Symbol::Named(_), args) = terms.get(constructor).clone() else {
        return None;
    };
    let (_, selectors) = selector_decls
        .iter()
        .find(|(name, _)| name.as_str() == symbol.name())?;
    let index = selectors.iter().position(|s| s.as_str() == selector)?;
    args.get(index).copied()
}

impl Executor {
    /// Whether any assume step's term tree mentions an elaboration-invented
    /// variable (frontend field variables are spelled with `!`, e.g.
    /// `x!f!case`). Bounded walk; oversized proofs answer false and keep
    /// the incumbent.
    fn proof_assumes_invented_field_var(&self, proof: &Proof) -> bool {
        const MAX_VISITED: usize = 64 * 1024;
        let mut visited = ay_core::kani_compat::DetHashSet::default();
        let mut stack: Vec<TermId> = proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Assume(term) => Some(*term),
                _ => None,
            })
            .collect();
        while let Some(term) = stack.pop() {
            if visited.len() >= MAX_VISITED {
                return false;
            }
            if !visited.insert(term) {
                continue;
            }
            if let TermData::Var(name, _) = self.ctx.terms.get(term) {
                if name.contains('!') {
                    return true;
                }
                continue;
            }
            stack.extend(self.ctx.terms.children(term));
        }
        false
    }

    /// Intern one parsed authored assertion for this planner when the shared
    /// raw intern declines it. The shared intern deliberately fails closed
    /// on record field reads (the ground-closure twin design depends on
    /// that), so this planner-local rebuild covers only the shapes it can
    /// transport: connective/equality skeletons whose leaves are datatype
    /// selector/constructor applications named by the declaration registry,
    /// rebuilt node-by-node with registry sorts. Any other head delegates
    /// back to the shared raw intern, preserving its authority decisions.
    fn intern_datatype_surface(&mut self, surface: &FrontendTerm) -> Option<TermId> {
        self.intern_datatype_surface_at(surface, 0)
    }

    fn intern_datatype_surface_at(
        &mut self,
        surface: &FrontendTerm,
        depth: usize,
    ) -> Option<TermId> {
        if depth > 64 {
            return None;
        }
        let stripped = crate::executor::proof_surface_syntax::strip_frontend_annotations(surface);
        match stripped {
            FrontendTerm::Symbol(_) | FrontendTerm::Const(_) => {
                self.ctx.elaborate_surface_subterm(stripped)
            }
            FrontendTerm::App(head, arguments) => {
                let member = self
                    .ctx
                    .exact_datatype_member_info(head)
                    .map(|info| (info.arg_sorts.clone(), info.sort.clone()));
                let skeleton = matches!(
                    head.as_str(),
                    "not" | "=" | "and" | "or" | "distinct" | "=>"
                );
                if member.is_none() && !skeleton {
                    return self.raw_intern_surface(surface);
                }
                if let Some((arg_sorts, _)) = &member {
                    if arg_sorts.len() != arguments.len() {
                        return None;
                    }
                }
                let raw_arguments = arguments
                    .iter()
                    .map(|argument| self.intern_datatype_surface_at(argument, depth + 1))
                    .collect::<Option<Vec<TermId>>>()?;
                // A selector name shared by two datatypes resolves by name
                // to the first datatype's field; synthesizing that identity
                // on the other datatype mints an ill-sorted application the
                // typed signature context later rejects, withholding a
                // verdict the incumbent proof had already earned. Fail
                // closed unless every argument sort matches the registry
                // identity the name actually resolves to.
                if let Some((arg_sorts, _)) = &member {
                    if raw_arguments
                        .iter()
                        .zip(arg_sorts.iter())
                        .any(|(arg, expected)| self.ctx.terms.sort(*arg) != expected)
                    {
                        return None;
                    }
                }
                if head.as_str() == "not" && raw_arguments.len() == 1 {
                    return Some(self.ctx.terms.mk_not_raw(raw_arguments[0]));
                }
                let sort = member.map_or(Sort::Bool, |(_, sort)| sort);
                Some(
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(head.as_str()), raw_arguments, sort),
                )
            }
            FrontendTerm::QualifiedApp(identifier, _, arguments) => {
                let name = identifier.as_symbol()?;
                let (arg_sorts, sort) = self
                    .ctx
                    .exact_datatype_member_info(name)
                    .map(|info| (info.arg_sorts.clone(), info.sort.clone()))?;
                if arg_sorts.len() != arguments.len() {
                    return None;
                }
                if arguments.is_empty() {
                    return self.ctx.elaborate_surface_subterm(stripped);
                }
                let raw_arguments = arguments
                    .iter()
                    .map(|argument| self.intern_datatype_surface_at(argument, depth + 1))
                    .collect::<Option<Vec<TermId>>>()?;
                if raw_arguments
                    .iter()
                    .zip(arg_sorts.iter())
                    .any(|(arg, expected)| self.ctx.terms.sort(*arg) != expected)
                {
                    return None;
                }
                Some(
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(name), raw_arguments, sort),
                )
            }
            // Every non-datatype node (indexed BV constants and operators,
            // binders, ...) keeps the shared raw intern's authority
            // decision, exactly like a non-skeleton `App` head above.
            _ => self.raw_intern_surface(surface),
        }
    }

    /// Rebuild an exact datatype projection/tester contradiction from public
    /// query roots, including native-API assertions that have no parsed
    /// SMT-LIB surface.
    ///
    /// The datatype solver can close `selector(C(args)) != arg_i` and
    /// `not (is-C (C(args)))` through an implicit datatype theorem, leaving a
    /// Generic proof leaf.  Reconstruct the theorem explicitly and accept it
    /// only through the strict checker's declaration-backed recognizer.  The
    /// contradictory premise must be an exact authored root; no live solver
    /// axiom or simplified surrogate is eligible.
    pub(super) fn replace_with_exact_authored_datatype_refutation(&mut self, proof: &mut Proof) {
        // Cheap shape gate first: this planner also runs in the cascade
        // prepass, where non-datatype problems must not pay for a scope
        // rebuild or a strict check.
        let datatype_decls = self.datatype_decls_for_strict_proof();
        let selector_decls = self.ctor_selector_decls_for_strict_proof();
        if datatype_decls.is_empty() && selector_decls.is_empty() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        // A proof can be native-strict complete yet assume elaborated
        // field terms with no authored surface (`x!f!case`); term-scope
        // validation passes on the elaborated provenance and the in-solve
        // render succeeds, but final certification cannot restore an
        // authored spelling for an invented field variable and withholds
        // the verdict. Such a proof still needs rebuilding on raw
        // authored roots. The `!` in an assume's variable name only
        // decides whether to attempt the (strictly checked) rebuild.
        if !self.proof_assumes_invented_field_var(proof)
            && self.check_proof_strict_with_datatypes(proof).is_ok()
            && ay_proof::validate_reachable_assumes_in_problem_scope(proof, &authored).is_ok()
        {
            return;
        }

        for &root in &authored {
            let (theorem, pivot) = match self.ctx.terms.get(root) {
                TermData::Not(inner) => (*inner, *inner),
                _ => (self.ctx.terms.mk_not_raw(root), root),
            };
            let kind = if !selector_decls.is_empty()
                && ay_proof::recognize_datatype_selector_project(
                    &self.ctx.terms,
                    &[theorem],
                    &selector_decls,
                ) {
                TheoryLemmaKind::DatatypeSelectorProject
            } else if !datatype_decls.is_empty()
                && ay_proof::recognize_datatype_tester_eval(
                    &self.ctx.terms,
                    &[theorem],
                    &datatype_decls,
                )
            {
                TheoryLemmaKind::DatatypeTesterEval
            } else {
                continue;
            };

            let mut candidate = Proof::new();
            let premise = candidate.add_assume(root, None);
            let lemma = candidate.add_theory_lemma_with_kind("datatype", vec![theorem], kind);
            candidate.add_resolution(Vec::new(), pivot, premise, lemma);
            if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok()
                && Self::proof_derives_empty_clause(&candidate)
                && self.check_proof_strict_with_datatypes(&candidate).is_ok()
            {
                *proof = candidate;
                return;
            }
        }

        let mut leaves = Vec::new();
        for &root in &authored {
            collect_leaves(&self.ctx.terms, root, root, &mut Vec::new(), &mut leaves);
        }
        // The provenance scope can be post-elaboration (field variables
        // like `x!f!case` in place of constructor forms), which seeds no
        // constructor shape below. Also collect leaves from the authored
        // assertions re-interned RAW, admitted only when the export scope
        // already contains them — the same raw-root source the BV
        // bit-blast repair uses; this pass reads the scope, never widens it.
        let mut candidate_scope = authored.clone();
        let mut synthesized_roots: Vec<TermId> = Vec::new();
        {
            let export_scope = self.proof_export_scope_assertions();
            let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
            for assertion in &parsed {
                let raw_root = self.raw_intern_surface(assertion);
                // A root folded to a Boolean constant (or its negation)
                // seeds no constructor shape; fall through to synthesized.
                let raw_folded = raw_root.is_some_and(|root| {
                    matches!(self.ctx.terms.get(root), TermData::Const(_))
                        || matches!(
                            self.ctx.terms.get(root),
                            TermData::Not(inner)
                                if matches!(self.ctx.terms.get(*inner), TermData::Const(_))
                        )
                });
                if let Some(root) = raw_root {
                    if export_scope.contains(&root) && !candidate_scope.contains(&root) {
                        candidate_scope.push(root);
                        collect_leaves(&self.ctx.terms, root, root, &mut Vec::new(), &mut leaves);
                    }
                }
                if raw_root.is_none() || raw_folded {
                    if let Some(root) = self.intern_datatype_surface(assertion) {
                        // Selector-bearing roots the shared raw intern declines
                        // by design; see `intern_datatype_surface`. Registered
                        // as raw originals only if a candidate installs.
                        if !candidate_scope.contains(&root) {
                            candidate_scope.push(root);
                            synthesized_roots.push(root);
                            collect_leaves(
                                &self.ctx.terms,
                                root,
                                root,
                                &mut Vec::new(),
                                &mut leaves,
                            );
                        }
                    }
                }
            }
        }
        // Two positive tester premises over one opaque value contradict the
        // declaration-backed mutual-exclusion theorem.
        if !datatype_decls.is_empty() {
            for (left_index, left) in leaves.iter().enumerate() {
                let Some(left_subject) = tester_subject(&self.ctx.terms, left.term) else {
                    continue;
                };
                for right in leaves.iter().skip(left_index + 1) {
                    if tester_subject(&self.ctx.terms, right.term) != Some(left_subject) {
                        continue;
                    }
                    let not_left = self.ctx.terms.mk_not_raw(left.term);
                    let not_right = self.ctx.terms.mk_not_raw(right.term);
                    let theorem = vec![not_left, not_right];
                    if !ay_proof::recognize_datatype_tester_eval_with_selectors(
                        &self.ctx.terms,
                        &theorem,
                        &datatype_decls,
                        &selector_decls,
                    ) {
                        continue;
                    }
                    let mut candidate = Proof::new();
                    let Some(left_unit) =
                        append_owned_leaf(&mut self.ctx.terms, &mut candidate, left)
                    else {
                        continue;
                    };
                    let Some(right_unit) =
                        append_owned_leaf(&mut self.ctx.terms, &mut candidate, right)
                    else {
                        continue;
                    };
                    let lemma = candidate.add_theory_lemma_with_kind(
                        "datatype",
                        theorem,
                        TheoryLemmaKind::DatatypeTesterEval,
                    );
                    let residual =
                        candidate.add_resolution(vec![not_right], left.term, lemma, left_unit);
                    candidate.add_resolution(Vec::new(), right.term, residual, right_unit);
                    if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored)
                        .is_ok()
                        && Self::proof_derives_empty_clause(&candidate)
                        && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                    {
                        *proof = candidate;
                        return;
                    }
                }
            }

            // A negative tester plus disequality from its nullary sibling
            // contradicts exact two-constructor exhaustiveness.
            for tester_leaf in &leaves {
                let TermData::Not(tester) = self.ctx.terms.get(tester_leaf.term) else {
                    continue;
                };
                if tester_subject(&self.ctx.terms, *tester).is_none() {
                    continue;
                }
                let tester = *tester;
                for equality_leaf in &leaves {
                    let TermData::Not(equality) = self.ctx.terms.get(equality_leaf.term) else {
                        continue;
                    };
                    if decode_eq_local(&self.ctx.terms, *equality).is_none() {
                        continue;
                    }
                    let equality = *equality;
                    let theorem = vec![tester, equality];
                    if !ay_proof::recognize_datatype_tester_eval_with_selectors(
                        &self.ctx.terms,
                        &theorem,
                        &datatype_decls,
                        &selector_decls,
                    ) {
                        continue;
                    }
                    let mut candidate = Proof::new();
                    let Some(tester_unit) =
                        append_owned_leaf(&mut self.ctx.terms, &mut candidate, tester_leaf)
                    else {
                        continue;
                    };
                    let Some(equality_unit) =
                        append_owned_leaf(&mut self.ctx.terms, &mut candidate, equality_leaf)
                    else {
                        continue;
                    };
                    let lemma = candidate.add_theory_lemma_with_kind(
                        "datatype",
                        theorem,
                        TheoryLemmaKind::DatatypeTesterEval,
                    );
                    let residual =
                        candidate.add_resolution(vec![equality], tester, lemma, tester_unit);
                    candidate.add_resolution(Vec::new(), equality, residual, equality_unit);
                    if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored)
                        .is_ok()
                        && Self::proof_derives_empty_clause(&candidate)
                        && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                    {
                        *proof = candidate;
                        return;
                    }
                }
            }
        }

        // Transport an authored constructor equality through a selector, apply
        // the declaration-backed selector projection theorem, and close the
        // authored selector disequality.
        //
        // Synthesized roots must be registered as raw originals BEFORE the
        // candidate strict check: the checker admits an assume only from
        // the legit assume set those registries feed. Registration is
        // transactional — restored below unless a candidate installs — the
        // same save/restore other authored repairs use. A synthesized root
        // is, by construction, the raw form of a parsed authored assertion,
        // so this asserts no provenance the shared raw intern would not
        // have asserted had it admitted the shape.
        let saved_rebuild_originals = self.last_proof_rebuild_originals.clone();
        let saved_raw_originals = self.last_proof_raw_original_assertions.clone();
        for root in &synthesized_roots {
            if !self.last_proof_rebuild_originals.contains(root) {
                self.last_proof_rebuild_originals.push(*root);
            }
            if !self.last_proof_raw_original_assertions.contains(root) {
                self.last_proof_raw_original_assertions.push(*root);
            }
        }
        if self.try_authored_selector_transport(proof, &candidate_scope, &leaves, &selector_decls) {
            return;
        }
        // No candidate installed: withdraw the transactional registration.
        self.last_proof_rebuild_originals = saved_rebuild_originals;
        self.last_proof_raw_original_assertions = saved_raw_originals;
    }
}
