// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The limb certificate: one bit-blast lemma for the facts, then the chain.

use super::super::frontier::samples_agree;
use crate::executor::Executor;
use ay_core::{Proof, ProofId, Sort, Symbol, TermId, TheoryLemmaKind};

/// How one node of the chain follows from the one before it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Step {
    /// The node is the previous one with facts rewritten (congruence).
    Rewrite,
    /// The PREVIOUS node is this one with facts rewritten (congruence).
    RewriteBack,
    /// The node is the previous one's ring normal form (`poly_simp`).
    Ring,
}

/// One proved link of the chain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Link {
    /// `(= original rewritten)` by congruence over the facts.
    Congruent(TermId, TermId),
    /// `(= left right)` by the ring lane.
    Ring(TermId, TermId),
}

impl Executor {
    /// The facts as one checked bit-blast lemma, then the chain from
    /// `start` through each `(step, node)` to the last node, with identical
    /// neighbours merged and any loop cut: congruence over the facts, ring
    /// steps between sums, and one transitivity to `(= start last)`.
    pub(super) fn prove_limb_chain(
        &mut self,
        candidate: &mut Proof,
        facts: &[(TermId, TermId)],
        start: TermId,
        path: &[(Step, TermId)],
    ) -> Option<ProofId> {
        if !facts
            .iter()
            .all(|&(left, right)| samples_agree(&self.ctx.terms, left, right))
        {
            decline("a fact disagrees on a sampled assignment");
            return None;
        }
        let goal_end = path.last()?.1;
        let links = limb_path(start, path);
        // Ring links first: they are cheap, and a refused one declines
        // before the bit-blast lemma is paid for.
        for (index, link) in links.iter().enumerate() {
            if let Link::Ring(left, right) = *link {
                // Printable as `poly_simp` AND admitted by the strict arm.
                let equality = self.limb_equality(left, right);
                let clause = [equality];
                if !ay_proof::recognize_arith_poly_simp(&self.ctx.terms, &clause)
                    || !ay_proof::recognize_arith_clause_tautology(&self.ctx.terms, &clause)
                {
                    decline(&format!("ring link {index} of {} is refused", links.len()));
                    return None;
                }
            }
        }
        let equalities: Vec<TermId> = facts
            .iter()
            .map(|&(left, right)| self.limb_equality(left, right))
            .collect();
        let lemma = match equalities.as_slice() {
            [single] => *single,
            _ => self
                .ctx
                .terms
                .mk_app(Symbol::named("and"), equalities.clone(), Sort::Bool),
        };
        if !self.recognize_bv_bitblast_until_stopped(&[lemma]) {
            decline("the bit-blast recognizer refused the facts lemma");
            return None;
        }
        let before = candidate.steps.len();
        let goal = self.limb_equality(start, goal_end);
        let proved = self.limb_links(candidate, lemma, &equalities, facts, &links, goal);
        if proved.is_none() {
            decline("the congruence/transitivity links did not close");
            candidate.steps.truncate(before);
        }
        proved
    }

    pub(super) fn limb_equality(&mut self, left: TermId, right: TermId) -> TermId {
        self.ctx
            .terms
            .mk_app(Symbol::named("="), [left, right], Sort::Bool)
    }

    fn limb_links(
        &mut self,
        candidate: &mut Proof,
        lemma: TermId,
        equalities: &[TermId],
        facts: &[(TermId, TermId)],
        links: &[Link],
        goal: TermId,
    ) -> Option<ProofId> {
        let units = self.project_frontier_lemma(candidate, lemma, equalities)?;
        let proved: Vec<_> = facts.iter().copied().zip(units).collect();
        let mut steps: Vec<(TermId, ProofId)> = Vec::with_capacity(links.len());
        for link in links {
            steps.push(match *link {
                Link::Congruent(original, rewritten) => {
                    let (step, equality) =
                        self.derive_frontier_congruence(candidate, original, rewritten, &proved)?;
                    (equality, step)
                }
                Link::Ring(left, right) => {
                    let equality = self.limb_equality(left, right);
                    let step = candidate.add_theory_lemma_with_kind(
                        "bv",
                        vec![equality],
                        TheoryLemmaKind::ArithClauseTautology,
                    );
                    (equality, step)
                }
            });
        }
        if let [(equality, step)] = steps.as_slice() {
            return (*equality == goal).then_some(*step);
        }
        if steps.is_empty() {
            return None;
        }
        // (cl (not e_1) .. (not e_n) (= start end)); the validator and the
        // consumer's `eq_transitive` both orient each premise themselves.
        let mut clause: Vec<TermId> = steps
            .iter()
            .map(|&(equality, _)| self.ctx.terms.mk_not_raw(equality))
            .collect();
        clause.push(goal);
        let mut current = candidate.add_theory_lemma_with_kind(
            "euf",
            clause.clone(),
            TheoryLemmaKind::EufTransitive,
        );
        let mut remaining = clause;
        for (equality, support) in steps {
            let negated = self.ctx.terms.mk_not_raw(equality);
            let position = remaining.iter().position(|&literal| literal == negated)?;
            let _ = remaining.remove(position);
            current = candidate.add_resolution(remaining.clone(), equality, current, support);
        }
        (remaining == [goal]).then_some(current)
    }
}

/// The links of the chain between distinct neighbours, with any loop cut so
/// that every link lies on one simple path (the transitivity schema refuses a
/// redundant premise).
fn limb_path(start: TermId, path: &[(Step, TermId)]) -> Vec<Link> {
    let mut nodes = vec![start];
    let mut links: Vec<Link> = Vec::new();
    for &(step, to) in path {
        let from = *nodes.last().unwrap_or(&start);
        if from == to {
            continue;
        }
        if let Some(seen) = nodes.iter().position(|&node| node == to) {
            // `to` is already on the path: drop the loop back to it.
            nodes.truncate(seen + 1);
            links.truncate(seen);
            continue;
        }
        nodes.push(to);
        links.push(match step {
            Step::Rewrite => Link::Congruent(from, to),
            Step::RewriteBack => Link::Congruent(to, from),
            Step::Ring => Link::Ring(from, to),
        });
    }
    links
}

/// `--probe-cert-reject` names why the limb certificate declined.
pub(super) fn decline(reason: &str) {
    crate::executor::unsat_cert::probe_cert_reject(|| {
        format!("bv-limb-identity: DECLINE {reason}")
    });
}

#[cfg(test)]
mod tests {
    use super::{limb_path, Link, Step};
    use ay_core::{Sort, TermStore};

    #[test]
    fn the_chain_merges_neighbours_and_cuts_loops() {
        let mut terms = TermStore::new();
        let [a, b, c, d, e] =
            ["a", "b", "c", "d", "e"].map(|name| terms.mk_var(name, Sort::bitvec(8)));
        let full = limb_path(
            a,
            &[
                (Step::Rewrite, b),
                (Step::Ring, c),
                (Step::Ring, e),
                (Step::RewriteBack, a),
            ],
        );
        assert!(full.is_empty(), "a path back to its start proves nothing");
        let path = limb_path(
            a,
            &[
                (Step::Rewrite, b),
                (Step::Ring, b),
                (Step::Rewrite, c),
                (Step::Ring, d),
                (Step::Ring, e),
                (Step::RewriteBack, d),
            ],
        );
        assert_eq!(
            path,
            vec![
                Link::Congruent(a, b),
                Link::Congruent(b, c),
                Link::Ring(c, d),
            ],
            "b = b merges, and the loop d -> e -> d is cut"
        );
        let back = limb_path(a, &[(Step::Ring, b), (Step::RewriteBack, c)]);
        assert_eq!(back, vec![Link::Ring(a, b), Link::Congruent(c, b)]);
    }
}
