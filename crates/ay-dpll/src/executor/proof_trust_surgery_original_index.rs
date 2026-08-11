// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One bounded, unique canonical lookup index for authored proof sources.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::TermId;
use ay_frontend::command::Term as FrontendTerm;

const MAX_INDEXED_ORIGINALS: usize = 100_000;

/// Prepare the first-seen novel authored premises without mutating executor
/// state. The caller can commit the returned append after every fallible proof
/// and surface-map check has succeeded.
pub(in crate::executor) fn prepare_rebuilt_premise_append(
    existing: &mut Vec<TermId>,
    candidates: &[TermId],
) -> Option<Vec<TermId>> {
    if existing.len() > MAX_INDEXED_ORIGINALS || candidates.len() > MAX_INDEXED_ORIGINALS {
        return None;
    }
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    for premise in existing.iter().copied() {
        // The original-rebuild wrapper records both the elaborated authored
        // root and its recursively raw-interned spelling. Print-faithful Apps
        // intentionally produce the same TermId in both slots. Preserve that
        // already-established scope order, but treat it as one membership
        // entry while deciding which newly rebuilt premises need appending.
        seen.insert(premise);
    }
    let mut append = Vec::new();
    for &premise in candidates {
        if seen.insert(premise) {
            if seen.len() > MAX_INDEXED_ORIGINALS {
                return None;
            }
            append.push(premise);
        }
    }
    existing.try_reserve(append.len()).ok()?;
    Some(append)
}

pub(in crate::executor) struct OriginalSourceIndex {
    indices: HashMap<TermId, Option<usize>>,
    valid: bool,
}

impl OriginalSourceIndex {
    pub(in crate::executor) fn new(originals: &[(TermId, FrontendTerm)]) -> Self {
        if originals.len() > MAX_INDEXED_ORIGINALS {
            return Self {
                indices: HashMap::default(),
                valid: false,
            };
        }
        let mut indices = HashMap::default();
        for (index, (canonical, _)) in originals.iter().enumerate() {
            if indices.insert(*canonical, Some(index)).is_some() {
                indices.insert(*canonical, None);
            }
        }
        Self {
            indices,
            valid: true,
        }
    }

    pub(in crate::executor) fn is_valid(&self) -> bool {
        self.valid
    }

    pub(in crate::executor) fn contains(&self, canonical: TermId) -> bool {
        self.indices.get(&canonical).is_some_and(Option::is_some)
    }

    pub(in crate::executor) fn is_ambiguous(&self, canonical: TermId) -> bool {
        self.indices.get(&canonical).is_some_and(Option::is_none)
    }

    pub(in crate::executor) fn get<'a>(
        &self,
        originals: &'a [(TermId, FrontendTerm)],
        canonical: TermId,
    ) -> Option<(usize, &'a FrontendTerm)> {
        let index = self.indices.get(&canonical).copied().flatten()?;
        let (source, parsed) = originals.get(index)?;
        (*source == canonical).then_some((index, parsed))
    }
}

#[cfg(test)]
mod tests {
    use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
    use ay_core::{Proof, TermId};
    use ay_frontend::command::Term as FrontendTerm;
    use ay_frontend::parse;

    use super::{prepare_rebuilt_premise_append, OriginalSourceIndex, MAX_INDEXED_ORIGINALS};
    use crate::executor::Executor;

    #[test]
    fn index_rejects_duplicates_and_over_cap_sources() {
        let parsed = FrontendTerm::Symbol("indexed_source".to_string());
        let duplicate = vec![(TermId(1), parsed.clone()), (TermId(1), parsed.clone())];
        let index = OriginalSourceIndex::new(&duplicate);
        assert!(index.is_valid());
        assert!(index.is_ambiguous(TermId(1)));
        assert!(index.get(&duplicate, TermId(1)).is_none());

        let over_cap = vec![(TermId(2), parsed); MAX_INDEXED_ORIGINALS + 1];
        assert!(!OriginalSourceIndex::new(&over_cap).is_valid());
    }

    #[test]
    fn over_cap_sources_force_rebuild_and_decline_without_mutation() {
        let mut executor = Executor::new();
        let term = executor.ctx.terms.mk_bool(true);
        let parsed = FrontendTerm::Symbol("over_cap_source".to_string());
        let originals = vec![(term, parsed); MAX_INDEXED_ORIGINALS + 1];
        let mut proof = Proof::new();
        proof.add_assume(term, None);
        let before_steps = format!("{:?}", proof.steps);
        let mut overrides = HashMap::default();
        overrides.insert(term, "over_cap_source".to_string());
        executor.last_proof_term_overrides = Some(overrides.clone());

        assert!(executor.reachable_normalized_assume(&proof, &originals));
        assert!(!executor.try_rebuild_with_trust_surgery(&mut proof, &originals));
        assert_eq!(format!("{:?}", proof.steps), before_steps);
        assert_eq!(executor.last_proof_term_overrides, Some(overrides));
    }

    #[test]
    fn rebuilt_premise_append_is_ordered_bounded_and_transactional() {
        let mut existing = vec![TermId(1), TermId(1), TermId(2)];
        let candidates = vec![TermId(2), TermId(3), TermId(3), TermId(4)];
        assert_eq!(
            prepare_rebuilt_premise_append(&mut existing, &candidates),
            Some(vec![TermId(3), TermId(4)])
        );
        assert_eq!(existing, [TermId(1), TermId(1), TermId(2)]);

        let mut full: Vec<TermId> = (0..MAX_INDEXED_ORIGINALS as u32).map(TermId).collect();
        let before = full.clone();
        assert!(prepare_rebuilt_premise_append(&mut full, &[TermId(u32::MAX)]).is_none());
        assert_eq!(full, before, "declining preparation must not mutate scope");
    }

    #[test]
    fn production_rebuild_tolerates_print_faithful_app_duplicates() {
        let script = r#"
            (set-option :produce-proofs true)
            (set-logic QF_LIA)
            (declare-const A Int)
            (declare-const B Int)
            (declare-const C Int)
            (declare-const D Int)
            (declare-const E Int)
            (declare-const F Int)
            (declare-const G Int)
            (declare-const H Int)
            (declare-const I Int)
            (declare-const J Int)
            (assert (ite (= J 1) (= I (+ E F)) (= I E)))
            (assert (= H (+ C F)))
            (assert (= G (+ B 1)))
            (assert (= F (+ A 1)))
            (assert (= E (+ D G)))
            ; These already-canonical Apps raw-intern to their own TermIds.
            (assert (<= 0 D))
            (assert (<= 0 A))
            (assert (<= 0 B))
            (assert (<= 0 C))
            (assert (< I 0))
            (check-sat)
        "#;
        let commands = parse(script).expect("valid wrapper fixture");
        let mut executor = Executor::new();
        assert_eq!(
            executor.execute_all(&commands).expect("solver executes"),
            vec!["unsat"]
        );

        let mut seen = HashSet::default();
        assert!(
            executor
                .last_proof_rebuild_originals
                .iter()
                .copied()
                .any(|term| !seen.insert(term)),
            "the production wrapper must exercise canonical/raw duplicate scope entries"
        );
        let proof = executor.last_proof().expect("UNSAT publishes a proof");
        let quality = ay_proof::check_proof_strict(proof, &executor.ctx.terms)
            .expect("wrapper rebuild must remain strict");
        assert_eq!(quality.trust_count, 0);
        assert!(ay_proof::terminal_trust_report(proof).is_trust_free());
        assert!(
            proof.steps.iter().any(|step| matches!(
                step,
                ay_core::ProofStep::Step {
                    rule: ay_core::AletheRule::Ite1 | ay_core::AletheRule::Ite2,
                    ..
                }
            )),
            "fixture must pass through the trust-surgery ITE repair"
        );
    }
}
