// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One run of the authored equality closure, shared by the plain member and
//! the instance-seeded member (`ground_instances`): authored leaves (step 1),
//! seeds and goals (step 2), the congruence universe (step 3) and bounded
//! saturation with closers and the shared commit gate (step 4).

use super::*;

impl Executor {
    /// Steps 3 and 4 of the closure: build the congruence universe, then
    /// alternate closers and bounded saturation rounds, committing the first
    /// candidate that passes the scope, empty-clause and strict gates (and,
    /// for `wire_clean_only`, the publication wire-gap screen).
    pub(super) fn close_authored_equalities(
        &mut self,
        proof: &mut Proof,
        authored: &[TermId],
        seeds: AuthoredClosureSeeds<'_>,
        mut derived: Vec<AuthoredDerivedEq>,
    ) {
        let AuthoredClosureSeeds {
            leaves,
            goals,
            instance_roots,
            constant_endpoints,
            wire_clean_only,
        } = seeds;
        // 3. The congruence universe: every subterm of the authored roots and
        //    of the checked instance equalities. A congruence step may only
        //    conclude about applications the PROBLEM already mentions, which
        //    keeps the search finite and the rebuilt proof free of invented
        //    terms.
        let mut universe: Vec<TermId> = Vec::new();
        for &root in authored.iter().chain(instance_roots) {
            collect_authored_subterms(&self.ctx.terms, root, &mut universe, MAX_UNIVERSE);
        }
        if universe.len() > MAX_UNIVERSE {
            return;
        }

        // 4. Bounded saturation, then close. Closers are tried on the seeds and
        //    after every round, so the smallest refutation wins.
        for _ in 0..=MAX_ROUNDS {
            let mut candidate =
                self.build_authored_equality_closure_candidate(leaves, &derived, goals);
            if candidate.is_none() && constant_endpoints {
                candidate = self.build_constant_endpoint_candidate(leaves, &derived);
            }
            if let Some(candidate) = candidate {
                if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, authored)
                    .is_ok()
                    && Self::proof_derives_empty_clause(&candidate)
                    && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                    && (!wire_clean_only || !self.proof_has_known_wire_gap(&candidate))
                {
                    *proof = candidate;
                    return;
                }
            }
            if derived.len() >= MAX_DERIVED {
                return;
            }
            if !self.saturate_authored_equalities(&mut derived, &universe, MAX_DERIVED) {
                return;
            }
        }
    }
}

/// Step 1 of the closure: conjunction leaves of the authored roots, each with
/// the `and`-path that reaches it. A leaf is derivable from its root by
/// `and_pos` projections alone, so nothing outside the authored scope enters.
pub(super) fn authored_closure_leaves(
    terms: &TermStore,
    authored: &[TermId],
) -> Option<Vec<AuthoredLeaf>> {
    if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
        return None;
    }
    let mut leaves: Vec<AuthoredLeaf> = Vec::new();
    for &root in authored {
        collect_authored_conjunction_leaves(
            terms,
            root,
            root,
            &mut Vec::new(),
            &mut leaves,
            MAX_LEAVES,
        );
    }
    (leaves.len() <= MAX_LEAVES).then_some(leaves)
}

/// The read-only inputs one closure run shares with its closers.
pub(super) struct AuthoredClosureSeeds<'a> {
    pub(super) leaves: &'a [AuthoredLeaf],
    pub(super) goals: &'a [AuthoredEqGoal],
    /// Instance equalities whose subterms join the congruence universe.
    pub(super) instance_roots: &'a [TermId],
    /// Whether a derived equality between two distinct constants closes.
    pub(super) constant_endpoints: bool,
    /// Whether a candidate the publication wire-gap screen
    /// (`proof_has_known_wire_gap`) flags is declined rather than committed.
    pub(super) wire_clean_only: bool,
}

impl<'a> AuthoredClosureSeeds<'a> {
    /// The plain member's run: no instance roots, no constant-endpoint closer,
    /// and its historical commit gate.
    pub(super) fn plain(leaves: &'a [AuthoredLeaf], goals: &'a [AuthoredEqGoal]) -> Self {
        Self {
            leaves,
            goals,
            instance_roots: &[],
            constant_endpoints: false,
            wire_clean_only: false,
        }
    }
}

/// Step 2 of the closure.
pub(super) fn authored_closure_seeds(
    terms: &TermStore,
    leaves: &[AuthoredLeaf],
) -> (Vec<AuthoredDerivedEq>, Vec<AuthoredEqGoal>) {
    // 2. Seed the derived-equality set with the leaves that ARE equalities,
    //    and collect the leaves that are DISEQUALITIES as closing targets.
    let mut derived: Vec<AuthoredDerivedEq> = Vec::new();
    let mut goals: Vec<AuthoredEqGoal> = Vec::new();
    for (index, leaf) in leaves.iter().enumerate() {
        if let Some((a, b)) = decode_eq_local(terms, leaf.term) {
            if a != b {
                push_authored_derived_eq(
                    &mut derived,
                    AuthoredDerivedEq {
                        eq: leaf.term,
                        a,
                        b,
                        derivation: AuthoredEqDerivation::Leaf(index),
                    },
                );
            }
            continue;
        }
        if let TermData::Not(inner) = terms.get(leaf.term) {
            let inner = *inner;
            if decode_eq_local(terms, inner).is_some() {
                goals.push(AuthoredEqGoal::Disequality {
                    equality: inner,
                    leaf: index,
                });
                continue;
            }
        }
        // A common WP postcondition shape is
        // `(or (not (= a x)) (not (= b y)))`: refuting it requires BOTH
        // equalities. Keep this narrowly structural and bounded. The
        // eventual `or` and resolution steps are checked independently;
        // a malformed or incomplete candidate cannot pass the final
        // strict commit gate.
        if let TermData::App(Symbol::Named(name), args) = terms.get(leaf.term) {
            const MAX_DISEQUALITY_DISJUNCTS: usize = 8;
            if name == "or" && (2..=MAX_DISEQUALITY_DISJUNCTS).contains(&args.len()) {
                let mut equalities = Vec::with_capacity(args.len());
                for &disjunct in args {
                    let TermData::Not(inner) = terms.get(disjunct) else {
                        equalities.clear();
                        break;
                    };
                    let inner = *inner;
                    if decode_eq_local(terms, inner).is_none() || equalities.contains(&inner) {
                        equalities.clear();
                        break;
                    }
                    equalities.push(inner);
                }
                if !equalities.is_empty() {
                    goals.push(AuthoredEqGoal::DisequalityDisjunction {
                        equalities,
                        leaf: index,
                    });
                }
            }
        }
    }
    (derived, goals)
}
