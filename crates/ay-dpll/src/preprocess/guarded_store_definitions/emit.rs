// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{AletheRule, TheoryLemmaKind};

use super::{shape::Path, *};

struct Builder<'a, 'p> {
    terms: &'a mut TermStore,
    proof: Proof,
    progress: Progress<'p>,
}

pub(super) fn build(
    terms: &mut TermStore,
    request: GuardedStoreRequest,
    paths: [Path; 2],
    cover_path: Path,
    replacement: TermId,
    definition: TermId,
    progress: Progress<'_>,
) -> Option<(Proof, ProofId)> {
    let mut builder = Builder {
        terms,
        proof: Proof::new(),
        progress,
    };
    let g = request.cases[0].guard;
    let not_g = builder.terms.mk_not_raw(g);
    let cover = builder.cover(request, &cover_path)?;
    let then_branch =
        builder.branch(request.cases[0], &paths[0], not_g, replacement, definition)?;
    let else_branch = builder.branch(request.cases[1], &paths[1], g, replacement, definition)?;
    // !g => h follows from the source cover, without asserting XOR.
    let else_covered = builder.resolve(vec![g, definition], else_branch, cover);
    let conclusion = builder.resolve(vec![definition], then_branch, else_covered);
    Some((builder.proof, conclusion))
}

impl Builder<'_, '_> {
    fn resolve(&mut self, clause: Vec<TermId>, left: ProofId, right: ProofId) -> ProofId {
        // The existing argument-free rule checks the exact set resolvent;
        // repeated guards are contracted, never treated as exclusive.
        self.proof.add_rule_step(
            AletheRule::ThResolution,
            clause,
            vec![left, right],
            Vec::new(),
        )
    }

    fn assume_source(&mut self, source: TermId, guard: Option<TermId>, body: TermId) -> ProofId {
        let source_id = self.proof.add_assume(source, None);
        match guard {
            Some(guard) => {
                let not_guard = self.terms.mk_not_raw(guard);
                self.proof.add_rule_step(
                    AletheRule::Or,
                    vec![not_guard, body],
                    vec![source_id],
                    Vec::new(),
                )
            }
            None => source_id,
        }
    }

    fn project(
        &mut self,
        path: &Path,
        mut current: ProofId,
        guard: Option<TermId>,
    ) -> Option<ProofId> {
        for &(parent, position, child) in &path.edges {
            if !(self.progress)(4, 2048) {
                return None;
            }
            let not_parent = self.terms.mk_not_raw(parent);
            let projection = self.proof.add_rule_step(
                AletheRule::AndPos(position),
                vec![not_parent, child],
                Vec::new(),
                vec![parent],
            );
            let clause = match guard {
                Some(guard) => vec![self.terms.mk_not_raw(guard), child],
                None => vec![child],
            };
            current = self.resolve(clause, current, projection);
        }
        Some(current)
    }

    fn cover(&mut self, request: GuardedStoreRequest, path: &Path) -> Option<ProofId> {
        let mut current = self.assume_source(request.cover_source, request.activation, path.body);
        if let Some(activation) = request.activation {
            // This assumption MUST itself be an original root (or its exact
            // conjunct); the final source-bound checker authenticates it.
            let activated = self.proof.add_assume(activation, None);
            current = self.resolve(vec![path.body], current, activated);
        }
        let projected = self.project(path, current, None)?;
        Some(self.proof.add_rule_step(
            AletheRule::Or,
            request.cases.iter().map(|case| case.guard).collect(),
            vec![projected],
            Vec::new(),
        ))
    }

    fn branch(
        &mut self,
        case: GuardedStoreCase,
        path: &Path,
        selected_guard: TermId,
        replacement: TermId,
        definition: TermId,
    ) -> Option<ProofId> {
        let source = self.assume_source(case.source, Some(case.guard), path.body);
        let source = self.project(path, source, Some(case.guard))?;
        let TermData::App(_, replacement_args) = self.terms.get(replacement) else {
            return None;
        };
        let selected_value = replacement_args[2];
        let TermData::App(_, store_args) = self.terms.get(case.store) else {
            return None;
        };
        let branch_value = store_args[2];
        let value_eq = raw_eq(self.terms, selected_value, branch_value);
        let projection = self.proof.add_theory_lemma_with_kind(
            "ite",
            vec![selected_guard, value_eq],
            TheoryLemmaKind::IteBranchProjection,
        );
        let array_eq = raw_eq(self.terms, replacement, case.store);
        let not_value_eq = self.terms.mk_not_raw(value_eq);
        let congruence = self.proof.add_theory_lemma_with_kind(
            "euf",
            vec![not_value_eq, array_eq],
            TheoryLemmaKind::EufCongruent,
        );
        let transported = self.resolve(vec![selected_guard, array_eq], projection, congruence);
        let not_source_eq = self.terms.mk_not_raw(path.target);
        let not_array_eq = self.terms.mk_not_raw(array_eq);
        let transitive = self.proof.add_theory_lemma_with_kind(
            "euf",
            vec![not_source_eq, not_array_eq, definition],
            TheoryLemmaKind::EufTransitive,
        );
        let not_guard = self.terms.mk_not_raw(case.guard);
        let source_transport = self.resolve(
            vec![not_guard, not_array_eq, definition],
            source,
            transitive,
        );
        let mut clause = vec![not_guard, definition];
        if selected_guard != not_guard {
            clause.push(selected_guard);
        }
        Some(self.resolve(clause, source_transport, transported))
    }
}
