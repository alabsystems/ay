// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cheap problem identity for process-wide caches keyed by problem content
//! (condense sharing, OR-split sharing, the failed-replay memo): a shallow
//! shape hash to pre-filter, then full structural equality.

use std::hash::{Hash, Hasher};

use super::ChcProblem;
use crate::{ClauseHead, HornClause};

/// Hash the shape of `clauses` (counts, predicate ids, arities, metadata);
/// [`clauses_identical`] is the authoritative check.
pub(super) fn hash_clause_shapes(clauses: &[HornClause], h: &mut impl Hasher) {
    clauses.len().hash(h);
    for clause in clauses {
        for (pid, args) in &clause.body.predicates {
            pid.hash(h);
            args.len().hash(h);
        }
        clause.body.constraint.is_some().hash(h);
        match &clause.head {
            ClauseHead::Predicate(pid, args) => {
                1u8.hash(h);
                pid.hash(h);
                args.len().hash(h);
            }
            ClauseHead::False => 0u8.hash(h),
        }
        clause.action_id.hash(h);
        clause.source_query_ordinal.hash(h);
    }
}

/// Full structural equality of two clause lists: every field a transform
/// reads or carries into its output. `ChcExpr::eq` short-circuits on shared
/// `Arc` children, so comparing clones never walks constraint trees.
pub(super) fn clauses_identical(a: &[HornClause], b: &[HornClause]) -> bool {
    a.len() == b.len()
        && a.iter().zip(b).all(|(c, d)| {
            c.action_id == d.action_id
                && c.source_query_ordinal == d.source_query_ordinal
                && c.body.predicates == d.body.predicates
                && c.body.constraint == d.body.constraint
                && match (&c.head, &d.head) {
                    (ClauseHead::False, ClauseHead::False) => true,
                    (ClauseHead::Predicate(pi, pa), ClauseHead::Predicate(qi, qa)) => {
                        pi == qi && pa == qa
                    }
                    _ => false,
                }
        })
}

impl ChcProblem {
    /// Cheap pre-filter fingerprint. Deliberately shallow (counts, names,
    /// arities): the authoritative check is [`Self::structurally_equal`].
    pub(crate) fn shallow_fingerprint(&self) -> u64 {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.predicates().len().hash(&mut h);
        for pred in self.predicates() {
            pred.name.hash(&mut h);
            pred.arg_sorts.hash(&mut h);
        }
        hash_clause_shapes(self.clauses(), &mut h);
        self.is_fixedpoint_format().hash(&mut h);
        h.finish()
    }

    /// Full structural equality between two problems (authoritative cache
    /// check).
    pub(crate) fn structurally_equal(&self, other: &Self) -> bool {
        self.predicates().len() == other.predicates().len()
            && self.is_fixedpoint_format() == other.is_fixedpoint_format()
            && self.has_query_evidence() == other.has_query_evidence()
            && self.action_names() == other.action_names()
            && self.datatype_defs() == other.datatype_defs()
            && self
                .predicates()
                .iter()
                .zip(other.predicates())
                .all(|(p, q)| p.name == q.name && p.arg_sorts == q.arg_sorts)
            && clauses_identical(self.clauses(), other.clauses())
    }
}
