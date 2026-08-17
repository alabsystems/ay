// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source-bound semantic authentication for a bounded Bool/Int/BV fragment.
//!
//! This checker is deliberately independent of AY's production BV/LIA bridge.
//! It consumes the exact live source roots, interprets SMT-LIB operations
//! directly, and either proves an immediate range/residue contradiction or
//! exhausts every value in a finite source-derived domain.  No production
//! theory lemma, translated AUFLIA assertion, model, or solver verdict is an
//! input to the decision.

use std::collections::{HashMap, HashSet};

use ay_core::{
    term::TermStoreSnapshotStamp, time::Instant, Constant, Sort, Symbol, TermData, TermId,
    TermStore,
};
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};

#[path = "bv_lia_query_eval.rs"]
mod application_evaluation;
#[path = "bv_lia_query_guarded.rs"]
mod guarded_range;
#[path = "bv_lia_query_int.rs"]
mod integer_evaluation;
#[path = "bv_lia_query_pins.rs"]
mod pins;
#[path = "bv_lia_query_sort.rs"]
mod sort_validation;
#[path = "bv_lia_query_tautology.rs"]
mod tautology;

pub(crate) use tautology::validate_bv_lia_tautology;

/// Maximum number of exact source roots admitted by the bounded BV/LIA lane.
///
/// Real model-checker-consumer obligations measured 271–406 roots. Refusing them discards a
/// computed UNSAT; 1024 covers that range while the independent interpreter's
/// node, work, memory, and caller-deadline limits remain the real backstops.
pub const MAX_BV_LIA_QUERY_ROOTS: usize = 1024;
/// Maximum deterministic interpreter work charged for one BV/LIA tautology.
pub const MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA: u64 = 100_000_000;
/// Conservative private-allocation envelope for one BV/LIA tautology.
///
/// This covers the shared 8 MiB owned-BigInt payload plus all independently
/// bounded 100k-node maps, sets, vectors, class/dimension records, evaluation
/// memo entries, traversal scratch, and depth-bounded temporary BigInts.
pub const MAX_BV_LIA_TAUTOLOGY_BYTES_PER_LEMMA: usize = 128 * 1024 * 1024;
const MAX_TERM_NODES: usize = 100_000;
const MAX_TERM_DEPTH: usize = 256;
const MAX_ENUMERATED_ASSIGNMENTS: u64 = 1 << 16;
const MAX_PROPAGATION_ROUNDS: usize = 512;
const MAX_WORK: u64 = MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA;
// Bound exact integer evaluation so multiplication cannot consume unmetered memory.
const MAX_INTEGER_BITS: u64 = 1 << 16;
// Bound retained BigInts independently of logical work so repeated source
// constants cannot accumulate before we decline.
const MAX_LIVE_INTEGER_LIMBS: u64 = 1 << 20;

/// Opaque evidence that one exact ordered Bool/Int/BV query is UNSAT.
#[derive(Debug)]
pub struct AuthenticatedBvLiaUnsatQuery {
    term_snapshot: TermStoreSnapshotStamp,
    roots: Box<[TermId]>,
}

impl AuthenticatedBvLiaUnsatQuery {
    /// Whether this evidence still denotes the same immutable term snapshot
    /// and exact ordered source roots.
    #[must_use]
    pub fn is_current_for(&self, terms: &TermStore, roots: &[TermId]) -> bool {
        self.term_snapshot == terms.snapshot_stamp() && self.roots.as_ref() == roots
    }

    /// Whether the immutable term snapshot authenticated by this evidence is
    /// still current.  A caller may use this after sealing the exact roots in a
    /// separate affine query-scope token.
    #[must_use]
    pub fn term_snapshot_is_current(&self, terms: &TermStore) -> bool {
        self.term_snapshot == terms.snapshot_stamp()
    }
}

/// Fail-closed reason why a source Bool/Int/BV query could not be
/// authenticated as UNSAT.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum BvLiaUnsatAuthenticationError {
    /// The empty conjunction is satisfiable.
    #[error("the BV/LIA query has no roots")]
    EmptyQuery,
    /// The source query exceeds the bounded root count.
    #[error("the BV/LIA query has {actual} roots, above the limit {limit}")]
    TooManyRoots {
        /// Maximum accepted roots.
        limit: usize,
        /// Roots supplied by the caller.
        actual: usize,
    },
    /// A supplied root does not name a live term.
    #[error("query root {root} is outside the live term store")]
    InvalidRoot {
        /// The first invalid source root.
        root: TermId,
    },
    /// The exact query has a satisfying assignment.
    #[error("the independently interpreted BV/LIA query is satisfiable")]
    Satisfiable,
    /// The source query is outside the finite checked fragment.
    #[error("query is outside the checked BV/LIA fragment: {reason}")]
    UnsupportedFragment {
        /// Stable source-fragment diagnostic.
        reason: String,
    },
    /// A deterministic work bound or caller deadline was exhausted.
    #[error("BV/LIA semantic authentication exhausted {resource}")]
    ResourceLimit {
        /// Exhausted bounded resource.
        resource: &'static str,
    },
}

impl BvLiaUnsatAuthenticationError {
    /// Whether another independently checked theory-specific lane may be tried
    /// because this checker does not implement the source fragment.
    #[must_use]
    pub fn is_unsupported_fragment(&self) -> bool {
        matches!(self, Self::UnsupportedFragment { .. })
    }

    /// Whether this error means "this lane cannot answer", as opposed to "the
    /// claimed refutation is wrong".
    ///
    /// This lane is an ADDITIONAL independent authenticator, not a gate: it runs
    /// only after the Alethe presentation has already failed, and its job is to
    /// rescue a correct refutation the presentation could not express. So
    /// exhausting its OWN bounded budget must decline the lane and let the
    /// remaining routes try, exactly as an unsupported fragment does.
    ///
    /// Treating a budget exhaustion as a rejection instead vetoed the whole
    /// certification, including the deferred-trust discharge that would have run
    /// next. Measured on QF_DT `vlsat3_b83`: 156_823 roots against this lane's
    /// then-256-root cap produced "independent source-level BV/LIA check rejected
    /// query", and a correct `unsat` published as `unknown`.
    ///
    /// `Satisfiable` is deliberately NOT here. That is this lane succeeding at
    /// its real job — it independently found the query satisfiable, which
    /// contradicts the claimed refutation and must stay a hard rejection.
    pub fn is_capability_decline(&self) -> bool {
        matches!(
            self,
            Self::UnsupportedFragment { .. }
                | Self::TooManyRoots { .. }
                | Self::ResourceLimit { .. }
        )
    }
}

/// Authenticate the conjunction of exact source `roots` as UNSAT in the
/// bounded Bool/Int/BV fragment.
///
/// `caller_deadline` is an external fail-closed stop only.  Acceptance is
/// bounded primarily by deterministic node, assignment, propagation, and work
/// counts, so machine load cannot widen the admitted fragment.
pub fn authenticate_bv_lia_unsat_query(
    terms: &TermStore,
    roots: &[TermId],
    caller_deadline: Option<Instant>,
) -> Result<AuthenticatedBvLiaUnsatQuery, BvLiaUnsatAuthenticationError> {
    if roots.is_empty() {
        return Err(BvLiaUnsatAuthenticationError::EmptyQuery);
    }
    if roots.len() > MAX_BV_LIA_QUERY_ROOTS {
        return Err(BvLiaUnsatAuthenticationError::TooManyRoots {
            limit: MAX_BV_LIA_QUERY_ROOTS,
            actual: roots.len(),
        });
    }
    if let Some(&root) = roots.iter().find(|root| root.index() >= terms.len()) {
        return Err(BvLiaUnsatAuthenticationError::InvalidRoot { root });
    }

    let term_snapshot = terms.snapshot_stamp();
    let mut checker = QueryChecker::new(terms, caller_deadline);
    match checker.decide(roots)? {
        QueryDecision::Unsat => Ok(AuthenticatedBvLiaUnsatQuery {
            term_snapshot,
            roots: roots.into(),
        }),
        QueryDecision::Sat => Err(BvLiaUnsatAuthenticationError::Satisfiable),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Bool(bool),
    Int(BigInt),
    BitVec { value: u64, width: u32 },
}

#[derive(Default)]
struct Environment {
    bools: HashMap<TermId, bool>,
    ints: HashMap<TermId, BigInt>,
    int_limbs: u64,
    bvs: HashMap<TermId, (u64, u32)>,
}

impl Environment {
    fn clear_ints(&mut self) {
        self.ints.clear();
        self.int_limbs = 0;
    }
}

struct CollectedVariables {
    ints: Vec<TermId>,
    bools: Vec<TermId>,
    bitvecs: Vec<(TermId, u32)>,
}

#[derive(Debug)]
enum Dimension {
    Bool(TermId),
    BitVec {
        term: TermId,
        width: u32,
    },
    IntClass {
        members: Vec<TermId>,
        lower: BigInt,
        count: u64,
    },
}

impl Dimension {
    fn count(&self) -> u64 {
        match self {
            Self::Bool(_) => 2,
            Self::BitVec { width, .. } => 1_u64 << width,
            Self::IntClass { count, .. } => *count,
        }
    }
}

#[derive(Clone, Debug, Default)]
struct ClassBounds {
    lower: Option<BigInt>,
    upper: Option<BigInt>,
}

struct IntClasses {
    class_of: HashMap<TermId, usize>,
    members: Vec<Vec<TermId>>,
    bounds: Vec<ClassBounds>,
}

impl IntClasses {
    fn members_for(&self, term: TermId) -> Option<&[TermId]> {
        self.class_of
            .get(&term)
            .map(|&class| self.members[class].as_slice())
    }

    fn semantic_key(&self, term: TermId) -> Option<usize> {
        self.class_of.get(&term).copied()
    }
}

enum QueryDecision {
    Sat,
    Unsat,
}

struct Meter {
    work: u64,
    deadline: Option<Instant>,
}

impl Meter {
    fn charge(&mut self, amount: u64) -> Result<(), BvLiaUnsatAuthenticationError> {
        let previous_work = self.work;
        self.work =
            self.work
                .checked_add(amount)
                .ok_or(BvLiaUnsatAuthenticationError::ResourceLimit {
                    resource: "work accounting",
                })?;
        if self.work > MAX_WORK {
            return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "deterministic work budget",
            });
        }
        // Bulk limb charges need not land exactly on a sampling boundary.
        // Compare buckets so crossing one or many boundaries always samples.
        if (previous_work >> 14) != (self.work >> 14)
            && self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "caller deadline",
            });
        }
        Ok(())
    }

    fn check_entry(&mut self) -> Result<(), BvLiaUnsatAuthenticationError> {
        if self
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "caller deadline",
            });
        }
        self.charge(1)
    }
}

struct QueryChecker<'a> {
    terms: &'a TermStore,
    meter: Meter,
    retained_int_limbs: u64,
}

impl<'a> QueryChecker<'a> {
    fn new(terms: &'a TermStore, deadline: Option<Instant>) -> Self {
        Self {
            terms,
            meter: Meter { work: 0, deadline },
            retained_int_limbs: 0,
        }
    }

    fn assign_dimension(
        &mut self,
        dimension: &Dimension,
        digit: u64,
        env: &mut Environment,
    ) -> Result<(), BvLiaUnsatAuthenticationError> {
        match dimension {
            Dimension::Bool(term) => {
                self.meter.charge(1)?;
                env.bools.insert(*term, digit != 0);
            }
            Dimension::BitVec { term, width } => {
                self.meter.charge(1)?;
                env.bvs.insert(*term, (digit & bv_mask(*width), *width));
            }
            Dimension::IntClass { members, lower, .. } => {
                let value = self.add_bounded_ints(lower, &BigInt::from(digit))?;
                if self.assign_int_members(members, &value, env)? == EnforceOutcome::Conflict {
                    return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                        reason: "overlapping integer dimensions assign conflicting values"
                            .to_string(),
                    });
                }
            }
        }
        Ok(())
    }

    fn assign_int_members(
        &mut self,
        members: &[TermId],
        value: &BigInt,
        env: &mut Environment,
    ) -> Result<EnforceOutcome, BvLiaUnsatAuthenticationError> {
        self.ensure_integer_magnitude(value)?;
        // This is deliberately two-phase. Charge and validate every existing
        // member plus the complete clone payload before reserving or inserting,
        // so conflict/deadline/storage failures leave the reusable env exact.
        let member_count = u64::try_from(members.len()).map_err(|_| {
            BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "integer assignment accounting",
            }
        })?;
        self.meter.charge(member_count.max(1))?;

        let value_limbs = integer_evaluation::integer_limb_units(value);
        let mut missing_members = HashSet::new();
        missing_members.try_reserve(members.len()).map_err(|_| {
            BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "integer assignment preflight allocation",
            }
        })?;
        for &member in members {
            if let Some(existing) = env.ints.get(&member) {
                let comparison_work =
                    value_limbs.max(integer_evaluation::integer_limb_units(existing));
                self.meter.charge(comparison_work)?;
                if existing != value {
                    return Ok(EnforceOutcome::Conflict);
                }
            } else {
                missing_members.insert(member);
            }
        }

        let missing_u64 = u64::try_from(missing_members.len()).map_err(|_| {
            BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "integer assignment accounting",
            }
        })?;
        let added_limbs = value_limbs.checked_mul(missing_u64).ok_or(
            BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "integer storage accounting",
            },
        )?;
        self.meter.charge(added_limbs.max(1))?;
        let new_live_limbs = env.int_limbs.checked_add(added_limbs).ok_or(
            BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "integer storage accounting",
            },
        )?;
        let total_live_limbs = self.retained_int_limbs.checked_add(new_live_limbs).ok_or(
            BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "integer storage accounting",
            },
        )?;
        if total_live_limbs > MAX_LIVE_INTEGER_LIMBS {
            return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "live integer storage",
            });
        }
        env.ints.try_reserve(missing_members.len()).map_err(|_| {
            BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "integer environment allocation",
            }
        })?;
        for member in missing_members {
            env.ints.insert(member, value.clone());
        }
        env.int_limbs = new_live_limbs;
        Ok(if missing_u64 == 0 {
            EnforceOutcome::Stable
        } else {
            EnforceOutcome::Changed
        })
    }

    fn decide(&mut self, roots: &[TermId]) -> Result<QueryDecision, BvLiaUnsatAuthenticationError> {
        self.meter.check_entry()?;
        self.validate_fragment_sorting(roots)?;
        let assertions = self.flatten_assertions(roots)?;
        if assertions
            .iter()
            .any(|&assertion| self.terms.sort(assertion) != &Sort::Bool)
        {
            return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                reason: "a flattened source assertion is not Boolean".to_string(),
            });
        }
        let variables = self.collect_variables(roots)?;
        let classes = self.build_int_classes(&variables.ints, &assertions)?;

        let pinned_bitvectors = self.collect_pinned_bitvectors(&assertions)?;
        if pinned_bitvectors.contradictory {
            return Ok(QueryDecision::Unsat);
        }

        if self.has_structural_contradiction(&assertions, &classes)? {
            return Ok(QueryDecision::Unsat);
        }

        // Propagate exact authored definitions before sizing the finite search.
        // A wide BV variable pinned by `(= x #x9c40)` has one possible value,
        // not 2^16 possibilities; counting it as free made this checker decline
        // simple source contradictions after hitting its enumeration cap. The
        // same fail-closed propagator used for every enumerated assignment is
        // sound on the exact `bv2nat` seed: it assigns only forced equalities or
        // unit connectives, and leaves every ambiguous term unknown. Seeding
        // first also propagates aliases of a variable fixed by `bv2nat`.
        self.meter
            .charge(u64::try_from(pinned_bitvectors.values.len()).unwrap_or(u64::MAX))?;
        let mut base_env = Environment {
            bvs: pinned_bitvectors.values,
            ..Environment::default()
        };
        match self.assignment_satisfies(&assertions, &classes, &mut base_env)? {
            AssignmentOutcome::Model => return Ok(QueryDecision::Sat),
            AssignmentOutcome::Refuted => return Ok(QueryDecision::Unsat),
            AssignmentOutcome::Unknown => {}
        }

        let dimensions =
            self.build_dimensions(&classes, &variables.bools, &variables.bitvecs, &base_env)?;
        let total = dimensions.iter().try_fold(1_u64, |total, dimension| {
            total
                .checked_mul(dimension.count())
                .filter(|count| *count <= MAX_ENUMERATED_ASSIGNMENTS)
                .ok_or(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                    reason: format!("finite assignment space exceeds {MAX_ENUMERATED_ASSIGNMENTS}"),
                })
        })?;

        let mut env = base_env;
        for ordinal in 0..total {
            self.meter.charge(1)?;
            // Propagation may assign otherwise-unbounded Int variables. Those
            // assignments belong only to this ordinal. Forced base Bool/Int
            // values are re-derived from the same authored assertions after
            // clearing. Every non-base Bool is a dimension, and every non-base
            // BV is a dimension overwritten below, so the retained BV map is
            // an exact immutable seed rather than leaked ordinal state.
            env.bools.clear();
            env.clear_ints();
            let mut remaining = ordinal;
            for dimension in &dimensions {
                let count = dimension.count();
                self.assign_dimension(dimension, remaining % count, &mut env)?;
                remaining /= count;
            }
            match self.assignment_satisfies(&assertions, &classes, &mut env)? {
                AssignmentOutcome::Model => return Ok(QueryDecision::Sat),
                AssignmentOutcome::Refuted => {}
                AssignmentOutcome::Unknown => {
                    return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                        reason: "an unbounded variable or unsupported operation remains after finite propagation"
                            .to_string(),
                    });
                }
            }
        }
        Ok(QueryDecision::Unsat)
    }

    fn validate_fragment_sorting(
        &mut self,
        roots: &[TermId],
    ) -> Result<(), BvLiaUnsatAuthenticationError> {
        let mut seen = HashSet::new();
        let mut reachable_edges = 0usize;
        let mut stack: Vec<(TermId, usize)> = roots.iter().copied().map(|root| (root, 1)).collect();
        while let Some((term, depth)) = stack.pop() {
            self.meter.charge(1)?;
            if depth > MAX_TERM_DEPTH {
                return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                    resource: "sort-validation depth",
                });
            }
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_TERM_NODES {
                return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                    resource: "sort-validation term nodes",
                });
            }
            if self.terms.entry_stamp(term).is_none() {
                return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                    reason: "a source term contains a dangling term reference".to_string(),
                });
            }
            let child_count = match self.terms.get(term) {
                TermData::Const(_) | TermData::Var(..) => 0,
                TermData::App(_, args) => args.len(),
                TermData::Let(bindings, _) => bindings.len().saturating_add(1),
                TermData::Not(_) => 1,
                TermData::Ite(..) => 3,
                TermData::Forall(..) | TermData::Exists(..) => 1,
                _ => {
                    return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                        reason: "an unsupported term occurs in the source query".to_string(),
                    });
                }
            };
            reachable_edges = reachable_edges.checked_add(child_count).ok_or(
                BvLiaUnsatAuthenticationError::ResourceLimit {
                    resource: "sort-validation term edges",
                },
            )?;
            if reachable_edges > MAX_TERM_NODES {
                return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                    resource: "sort-validation term edges",
                });
            }
            self.meter
                .charge(u64::try_from(child_count).unwrap_or(u64::MAX))?;
            let children = self.terms.children(term);
            if children
                .iter()
                .any(|&child| self.terms.entry_stamp(child).is_none())
            {
                return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                    reason: "a source term contains a dangling term reference".to_string(),
                });
            }
            if !sort_validation::node_is_well_sorted(self.terms, term) {
                return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                    reason: "an ill-sorted or unsupported term occurs in the source query"
                        .to_string(),
                });
            }
            stack.extend(children.into_iter().map(|child| (child, depth + 1)));
        }
        Ok(())
    }

    fn flatten_assertions(
        &mut self,
        roots: &[TermId],
    ) -> Result<Vec<TermId>, BvLiaUnsatAuthenticationError> {
        let mut out = Vec::new();
        let mut active_ands = HashSet::new();
        let mut stack: Vec<(TermId, bool)> = roots
            .iter()
            .rev()
            .copied()
            .map(|term| (term, false))
            .collect();
        while let Some((term, exiting)) = stack.pop() {
            self.meter.charge(1)?;
            if exiting {
                active_ands.remove(&term);
                continue;
            }
            if self.terms.sort(term) != &Sort::Bool {
                return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                    reason: "a source assertion or Boolean connective is not Boolean".to_string(),
                });
            }
            if out.len() + stack.len() > MAX_TERM_NODES {
                return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                    resource: "flattened assertion nodes",
                });
            }
            match self.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "and" => {
                    if !active_ands.insert(term) {
                        return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                            reason: "the source query contains a cyclic conjunction".to_string(),
                        });
                    }
                    stack.push((term, true));
                    stack.extend(args.iter().rev().copied().map(|arg| (arg, false)));
                }
                _ => out.push(term),
            }
        }
        Ok(out)
    }

    fn collect_variables(
        &mut self,
        roots: &[TermId],
    ) -> Result<CollectedVariables, BvLiaUnsatAuthenticationError> {
        let mut seen = HashSet::new();
        let mut stack: Vec<(TermId, usize)> = roots.iter().copied().map(|root| (root, 1)).collect();
        let mut ints = Vec::new();
        let mut bools = Vec::new();
        let mut bvs = Vec::new();
        while let Some((term, depth)) = stack.pop() {
            self.meter.charge(1)?;
            if depth > MAX_TERM_DEPTH {
                return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                    resource: "term depth",
                });
            }
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_TERM_NODES {
                return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                    resource: "term DAG nodes",
                });
            }
            if matches!(self.terms.get(term), TermData::Var(..)) {
                match self.terms.sort(term) {
                    Sort::Bool => bools.push(term),
                    Sort::Int => ints.push(term),
                    Sort::BitVec(width) if width.width > 0 && width.width <= 64 => {
                        bvs.push((term, width.width));
                    }
                    sort => {
                        return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                            reason: format!("unsupported variable sort {sort:?}"),
                        });
                    }
                }
            }
            let next_depth = depth + 1;
            match self.terms.get(term) {
                TermData::App(_, args) => {
                    stack.extend(args.iter().copied().map(|arg| (arg, next_depth)));
                }
                TermData::Not(inner) => stack.push((*inner, next_depth)),
                TermData::Ite(condition, then_term, else_term) => {
                    stack.push((*condition, next_depth));
                    stack.push((*then_term, next_depth));
                    stack.push((*else_term, next_depth));
                }
                TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => {
                    return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                        reason: "let/quantifier terms are outside the bounded BV/LIA fragment"
                            .to_string(),
                    });
                }
                TermData::Const(_) | TermData::Var(..) => {}
                _ => {
                    return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                        reason: "unsupported source term form".to_string(),
                    });
                }
            }
        }
        ints.sort_unstable();
        bools.sort_unstable();
        bvs.sort_unstable_by_key(|(term, _)| *term);
        Ok(CollectedVariables {
            ints,
            bools,
            bitvecs: bvs,
        })
    }

    fn build_int_classes(
        &mut self,
        vars: &[TermId],
        assertions: &[TermId],
    ) -> Result<IntClasses, BvLiaUnsatAuthenticationError> {
        let index: HashMap<TermId, usize> = vars
            .iter()
            .enumerate()
            .map(|(index, &term)| (term, index))
            .collect();
        let mut parent: Vec<usize> = (0..vars.len()).collect();

        fn find(parent: &mut [usize], mut index: usize) -> usize {
            let mut root = index;
            while parent[root] != root {
                root = parent[root];
            }
            while parent[index] != index {
                let next = parent[index];
                parent[index] = root;
                index = next;
            }
            root
        }
        fn union(parent: &mut [usize], left: usize, right: usize) {
            let left = find(parent, left);
            let right = find(parent, right);
            if left != right {
                parent[right] = left;
            }
        }

        for &assertion in assertions {
            self.meter.charge(1)?;
            let Some((name, args)) = named_app(self.terms, assertion) else {
                continue;
            };
            if name == "=" && args.len() == 2 {
                if let (Some(&left), Some(&right)) = (index.get(&args[0]), index.get(&args[1])) {
                    union(&mut parent, left, right);
                }
            }
        }

        let mut root_to_class = HashMap::new();
        let mut class_of = HashMap::new();
        let mut members: Vec<Vec<TermId>> = Vec::new();
        for (var_index, &term) in vars.iter().enumerate() {
            let root = find(&mut parent, var_index);
            let next = root_to_class.len();
            let class = *root_to_class.entry(root).or_insert(next);
            if class == members.len() {
                members.push(Vec::new());
            }
            members[class].push(term);
            class_of.insert(term, class);
        }
        let mut classes = IntClasses {
            class_of,
            bounds: vec![ClassBounds::default(); members.len()],
            members,
        };

        let retained_before_bounds = self.retained_int_limbs;
        for &assertion in assertions {
            if let Err(error) = self.record_int_bound(assertion, &mut classes) {
                self.retained_int_limbs = retained_before_bounds;
                return Err(error);
            }
        }
        Ok(classes)
    }

    fn record_int_bound(
        &mut self,
        assertion: TermId,
        classes: &mut IntClasses,
    ) -> Result<(), BvLiaUnsatAuthenticationError> {
        self.meter.charge(1)?;
        let Some((mut name, args)) = named_app(self.terms, assertion) else {
            return Ok(());
        };
        if args.len() != 2 {
            return Ok(());
        }

        if name == "=" {
            if let Some((var, value)) = var_const_pair(self.terms, args) {
                if let Some(&class) = classes.class_of.get(&var) {
                    self.tighten_lower_bound_from_ref(&mut classes.bounds[class], value)?;
                    self.tighten_upper_bound_from_ref(&mut classes.bounds[class], value)?;
                }
            }
            return Ok(());
        }

        if !matches!(name, "<" | "<=" | ">" | ">=") {
            return Ok(());
        }
        let (var, constant, variable_on_left) = if is_int_var(self.terms, args[0]) {
            let Some(value) = int_constant(self.terms, args[1]) else {
                return Ok(());
            };
            (args[0], value, true)
        } else if is_int_var(self.terms, args[1]) {
            let Some(value) = int_constant(self.terms, args[0]) else {
                return Ok(());
            };
            (args[1], value, false)
        } else {
            return Ok(());
        };
        let Some(&class) = classes.class_of.get(&var) else {
            return Ok(());
        };
        if !variable_on_left {
            name = match name {
                "<" => ">",
                "<=" => ">=",
                ">" => "<",
                ">=" => "<=",
                _ => unreachable!(),
            };
        }
        match name {
            "<" => {
                let bound = self.subtract_bounded_ints(constant, &BigInt::one())?;
                self.tighten_upper_bound(&mut classes.bounds[class], bound)?;
            }
            "<=" => {
                self.tighten_upper_bound_from_ref(&mut classes.bounds[class], constant)?;
            }
            ">" => {
                let bound = self.add_bounded_ints(constant, &BigInt::one())?;
                self.tighten_lower_bound(&mut classes.bounds[class], bound)?;
            }
            ">=" => {
                self.tighten_lower_bound_from_ref(&mut classes.bounds[class], constant)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn tighten_lower_bound_from_ref(
        &mut self,
        bounds: &mut ClassBounds,
        value: &BigInt,
    ) -> Result<(), BvLiaUnsatAuthenticationError> {
        if let Some(existing) = &bounds.lower {
            self.charge_integer_comparison(existing, value)?;
            if existing >= value {
                return Ok(());
            }
        }
        let retained = self.preflight_retained_integer(bounds.lower.as_ref(), value, 0)?;
        self.meter
            .charge(integer_evaluation::integer_limb_units(value))?;
        bounds.lower = Some(value.clone());
        self.retained_int_limbs = retained;
        Ok(())
    }

    fn tighten_upper_bound_from_ref(
        &mut self,
        bounds: &mut ClassBounds,
        value: &BigInt,
    ) -> Result<(), BvLiaUnsatAuthenticationError> {
        if let Some(existing) = &bounds.upper {
            self.charge_integer_comparison(existing, value)?;
            if existing <= value {
                return Ok(());
            }
        }
        let retained = self.preflight_retained_integer(bounds.upper.as_ref(), value, 0)?;
        self.meter
            .charge(integer_evaluation::integer_limb_units(value))?;
        bounds.upper = Some(value.clone());
        self.retained_int_limbs = retained;
        Ok(())
    }

    fn tighten_lower_bound(
        &mut self,
        bounds: &mut ClassBounds,
        value: BigInt,
    ) -> Result<(), BvLiaUnsatAuthenticationError> {
        if let Some(existing) = &bounds.lower {
            self.charge_integer_comparison(existing, &value)?;
            if existing >= &value {
                return Ok(());
            }
        }
        let retained = self.preflight_retained_integer(bounds.lower.as_ref(), &value, 0)?;
        bounds.lower = Some(value);
        self.retained_int_limbs = retained;
        Ok(())
    }

    fn tighten_upper_bound(
        &mut self,
        bounds: &mut ClassBounds,
        value: BigInt,
    ) -> Result<(), BvLiaUnsatAuthenticationError> {
        if let Some(existing) = &bounds.upper {
            self.charge_integer_comparison(existing, &value)?;
            if existing <= &value {
                return Ok(());
            }
        }
        let retained = self.preflight_retained_integer(bounds.upper.as_ref(), &value, 0)?;
        bounds.upper = Some(value);
        self.retained_int_limbs = retained;
        Ok(())
    }

    fn has_structural_contradiction(
        &mut self,
        assertions: &[TermId],
        classes: &IntClasses,
    ) -> Result<bool, BvLiaUnsatAuthenticationError> {
        for bounds in &classes.bounds {
            let Some((lower, upper)) = bounds.lower.as_ref().zip(bounds.upper.as_ref()) else {
                continue;
            };
            self.charge_integer_comparison(lower, upper)?;
            if lower > upper {
                return Ok(true);
            }
        }
        for &assertion in assertions {
            self.meter.charge(1)?;
            if self.interval_proves_false(assertion)?
                || self.residue_identity_proves_false(assertion, classes)?
            {
                return Ok(true);
            }
        }
        self.has_guarded_bv2nat_range_contradiction(assertions)
    }

    fn interval_proves_false(
        &mut self,
        assertion: TermId,
    ) -> Result<bool, BvLiaUnsatAuthenticationError> {
        let (term, desired) = match self.terms.get(assertion) {
            TermData::Not(inner) => (*inner, false),
            _ => (assertion, true),
        };
        let Some((name, args)) = named_app(self.terms, term) else {
            return Ok(false);
        };
        if args.len() != 2 || !matches!(name, "<" | "<=" | ">" | ">=" | "=") {
            return Ok(false);
        }
        let Some((left_low, left_high)) = self.int_interval(args[0], 0)? else {
            return Ok(false);
        };
        let Some((right_low, right_high)) = self.int_interval(args[1], 0)? else {
            return Ok(false);
        };
        for (left, right) in [
            (&left_low, &right_high),
            (&left_high, &right_low),
            (&right_high, &left_low),
            (&left_low, &left_high),
            (&left_low, &right_low),
            (&right_low, &right_high),
        ] {
            self.charge_integer_comparison(left, right)?;
        }
        let always_false = match name {
            "<" => left_low >= right_high,
            "<=" => left_low > right_high,
            ">" => left_high <= right_low,
            ">=" => left_high < right_low,
            "=" => left_high < right_low || right_high < left_low,
            _ => false,
        };
        let always_true = match name {
            "<" => left_high < right_low,
            "<=" => left_high <= right_low,
            ">" => left_low > right_high,
            ">=" => left_low >= right_high,
            "=" => left_low == left_high && left_low == right_low && right_low == right_high,
            _ => false,
        };
        Ok(if desired { always_false } else { always_true })
    }

    fn int_interval(
        &mut self,
        term: TermId,
        depth: usize,
    ) -> Result<Option<(BigInt, BigInt)>, BvLiaUnsatAuthenticationError> {
        if depth > MAX_TERM_DEPTH {
            return Ok(None);
        }
        match self.terms.get(term) {
            TermData::Const(Constant::Int(value)) => {
                let copy_work = integer_evaluation::integer_limb_units(value)
                    .checked_mul(2)
                    .ok_or(BvLiaUnsatAuthenticationError::ResourceLimit {
                        resource: "integer interval accounting",
                    })?;
                self.ensure_integer_magnitude(value)?;
                self.meter.charge(copy_work)?;
                Ok(Some((value.clone(), value.clone())))
            }
            TermData::App(Symbol::Named(name), args) if name == "bv2nat" && args.len() == 1 => {
                let Sort::BitVec(width) = self.terms.sort(args[0]) else {
                    return Ok(None);
                };
                if width.width == 0 || width.width > 64 {
                    return Ok(None);
                }
                self.meter.charge(1)?;
                Ok(Some((
                    BigInt::zero(),
                    (BigInt::one() << width.width) - BigInt::one(),
                )))
            }
            _ => Ok(None),
        }
    }

    fn residue_identity_proves_false(
        &mut self,
        assertion: TermId,
        classes: &IntClasses,
    ) -> Result<bool, BvLiaUnsatAuthenticationError> {
        let (term, desired) = match self.terms.get(assertion) {
            TermData::Not(inner) => (*inner, false),
            _ => (assertion, true),
        };
        let Some((name, args)) = named_app(self.terms, term) else {
            return Ok(false);
        };
        if args.len() != 2 || !matches!(name, "<" | "<=" | ">" | ">=" | "=") {
            return Ok(false);
        }
        let left = self.semantic_int_key(args[0], classes)?;
        let right = self.semantic_int_key(args[1], classes)?;
        let Some((left, right)) = left.zip(right) else {
            return Ok(false);
        };
        if left != right {
            return Ok(false);
        }
        let value = matches!(name, "<=" | ">=" | "=");
        Ok(value != desired)
    }

    fn semantic_int_key(
        &mut self,
        term: TermId,
        classes: &IntClasses,
    ) -> Result<Option<usize>, BvLiaUnsatAuthenticationError> {
        if let Some(class) = classes.semantic_key(term) {
            return Ok(Some(class));
        }
        let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
            return Ok(None);
        };
        if name != "bv2nat" || args.len() != 1 {
            return Ok(None);
        }
        let TermData::App(Symbol::Indexed(name, indices), int_args) = self.terms.get(args[0])
        else {
            return Ok(None);
        };
        if name != "int2bv" || indices.len() != 1 || int_args.len() != 1 {
            return Ok(None);
        }
        if indices[0] == 0 || indices[0] > 64 {
            return Ok(None);
        }
        let Some(class) = classes.semantic_key(int_args[0]) else {
            return Ok(None);
        };
        let bounds = &classes.bounds[class];
        let Some((lower, upper)) = bounds.lower.as_ref().zip(bounds.upper.as_ref()) else {
            return Ok(None);
        };
        let comparison_work = integer_evaluation::integer_limb_units(lower)
            .checked_add(integer_evaluation::integer_limb_units(upper))
            .ok_or(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "integer comparison accounting",
            })?;
        self.meter.charge(comparison_work)?;
        let max = (BigInt::one() << indices[0]) - BigInt::one();
        Ok((lower >= &BigInt::zero() && upper <= &max).then_some(class))
    }

    fn build_dimensions(
        &mut self,
        classes: &IntClasses,
        bool_vars: &[TermId],
        bv_vars: &[(TermId, u32)],
        base_env: &Environment,
    ) -> Result<Vec<Dimension>, BvLiaUnsatAuthenticationError> {
        let retained_before_dimensions = self.retained_int_limbs;
        let result = self.build_dimensions_inner(classes, bool_vars, bv_vars, base_env);
        if result.is_err() {
            self.retained_int_limbs = retained_before_dimensions;
        }
        result
    }

    fn build_dimensions_inner(
        &mut self,
        classes: &IntClasses,
        bool_vars: &[TermId],
        bv_vars: &[(TermId, u32)],
        base_env: &Environment,
    ) -> Result<Vec<Dimension>, BvLiaUnsatAuthenticationError> {
        let mut dimensions = Vec::new();
        for (class, members) in classes.members.iter().enumerate() {
            if members
                .first()
                .is_some_and(|member| base_env.ints.contains_key(member))
            {
                continue;
            }
            let (Some(lower), Some(upper)) = (
                classes.bounds[class].lower.as_ref(),
                classes.bounds[class].upper.as_ref(),
            ) else {
                continue;
            };
            self.charge_integer_comparison(lower, upper)?;
            if upper < lower {
                continue;
            }
            let span = self.subtract_bounded_ints(upper, lower)?;
            let count = self
                .add_bounded_ints(&span, &BigInt::one())?
                .to_u64()
                .ok_or_else(|| BvLiaUnsatAuthenticationError::UnsupportedFragment {
                    reason: "integer domain does not fit the finite enumeration counter"
                        .to_string(),
                })?;
            if count > MAX_ENUMERATED_ASSIGNMENTS {
                return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                    reason: format!(
                        "integer domain has {count} values, above {MAX_ENUMERATED_ASSIGNMENTS}"
                    ),
                });
            }
            self.meter
                .charge(u64::try_from(members.len()).unwrap_or(u64::MAX))?;
            let lower = self.clone_retained_int(lower, base_env.int_limbs)?;
            dimensions.push(Dimension::IntClass {
                members: members.clone(),
                lower,
                count,
            });
        }
        dimensions.extend(
            bool_vars
                .iter()
                .copied()
                .filter(|term| !base_env.bools.contains_key(term))
                .map(Dimension::Bool),
        );
        for &(term, width) in bv_vars {
            if base_env.bvs.contains_key(&term) {
                continue;
            }
            if width >= 64 {
                return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                    reason: "a free 64-bit BV variable exceeds finite enumeration".to_string(),
                });
            }
            dimensions.push(Dimension::BitVec { term, width });
        }
        Ok(dimensions)
    }

    fn assignment_satisfies(
        &mut self,
        assertions: &[TermId],
        classes: &IntClasses,
        env: &mut Environment,
    ) -> Result<AssignmentOutcome, BvLiaUnsatAuthenticationError> {
        for _ in 0..MAX_PROPAGATION_ROUNDS {
            self.meter.charge(1)?;
            let mut changed = false;
            let mut memo = HashMap::new();
            for &assertion in assertions {
                match self.enforce_bool(assertion, true, env, classes, &mut memo, 0)? {
                    EnforceOutcome::Stable => {}
                    EnforceOutcome::Changed => {
                        changed = true;
                        memo.clear();
                    }
                    EnforceOutcome::Conflict => return Ok(AssignmentOutcome::Refuted),
                }
            }
            if !changed {
                let mut unknown = false;
                let mut memo = HashMap::new();
                for &assertion in assertions {
                    match self.eval_bool(assertion, env, &mut memo, 0)? {
                        Some(true) => {}
                        Some(false) => return Ok(AssignmentOutcome::Refuted),
                        None => unknown = true,
                    }
                }
                return Ok(if unknown {
                    AssignmentOutcome::Unknown
                } else {
                    AssignmentOutcome::Model
                });
            }
        }
        Err(BvLiaUnsatAuthenticationError::ResourceLimit {
            resource: "definition propagation rounds",
        })
    }

    fn enforce_bool(
        &mut self,
        term: TermId,
        desired: bool,
        env: &mut Environment,
        classes: &IntClasses,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<EnforceOutcome, BvLiaUnsatAuthenticationError> {
        self.meter.charge(1)?;
        if depth > MAX_TERM_DEPTH {
            return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "propagation depth",
            });
        }
        if self.terms.sort(term) != &Sort::Bool {
            return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                reason: "a term used as a Boolean assertion is not Boolean".to_string(),
            });
        }
        if let Some(value) = self.eval_bool(term, env, memo, depth + 1)? {
            return Ok(if value == desired {
                EnforceOutcome::Stable
            } else {
                EnforceOutcome::Conflict
            });
        }

        match self.terms.get(term) {
            TermData::Not(inner) => {
                self.enforce_bool(*inner, !desired, env, classes, memo, depth + 1)
            }
            TermData::App(Symbol::Named(name), args) if name == "and" => {
                self.enforce_connective(args, desired, false, env, classes, memo, depth + 1)
            }
            TermData::App(Symbol::Named(name), args) if name == "or" => {
                self.enforce_connective(args, desired, true, env, classes, memo, depth + 1)
            }
            TermData::App(Symbol::Named(name), args)
                if matches!(name.as_str(), "=>" | "implies") && args.len() == 2 =>
            {
                if desired {
                    let left = self.eval_bool(args[0], env, memo, depth + 1)?;
                    let right = self.eval_bool(args[1], env, memo, depth + 1)?;
                    match (left, right) {
                        (Some(false), _) | (_, Some(true)) => Ok(EnforceOutcome::Stable),
                        (Some(true), None) => {
                            self.enforce_bool(args[1], true, env, classes, memo, depth + 1)
                        }
                        (None, Some(false)) => {
                            self.enforce_bool(args[0], false, env, classes, memo, depth + 1)
                        }
                        (Some(true), Some(false)) => Ok(EnforceOutcome::Conflict),
                        _ => Ok(EnforceOutcome::Stable),
                    }
                } else {
                    let left = self.enforce_bool(args[0], true, env, classes, memo, depth + 1)?;
                    let right = self.enforce_bool(args[1], false, env, classes, memo, depth + 1)?;
                    Ok(left.combine(right))
                }
            }
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                if desired {
                    self.enforce_equality(args[0], args[1], env, classes, memo, depth + 1)
                } else {
                    Ok(EnforceOutcome::Stable)
                }
            }
            TermData::Ite(condition, then_term, else_term) => {
                match self.eval_bool(*condition, env, memo, depth + 1)? {
                    Some(true) => {
                        self.enforce_bool(*then_term, desired, env, classes, memo, depth + 1)
                    }
                    Some(false) => {
                        self.enforce_bool(*else_term, desired, env, classes, memo, depth + 1)
                    }
                    None => Ok(EnforceOutcome::Stable),
                }
            }
            TermData::Var(..) if *self.terms.sort(term) == Sort::Bool => {
                assign_plain(&mut env.bools, term, desired)
            }
            _ => Ok(EnforceOutcome::Stable),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn enforce_connective(
        &mut self,
        args: &[TermId],
        desired: bool,
        is_or: bool,
        env: &mut Environment,
        classes: &IntClasses,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<EnforceOutcome, BvLiaUnsatAuthenticationError> {
        let force_every = desired != is_or;
        if force_every {
            let mut outcome = EnforceOutcome::Stable;
            for &arg in args {
                outcome = outcome.combine(self.enforce_bool(
                    arg,
                    desired,
                    env,
                    classes,
                    memo,
                    depth + 1,
                )?);
                if outcome == EnforceOutcome::Conflict {
                    break;
                }
            }
            return Ok(outcome);
        }

        let satisfying = desired;
        let mut unknown = None;
        let mut unknown_count = 0;
        for &arg in args {
            match self.eval_bool(arg, env, memo, depth + 1)? {
                Some(value) if value == satisfying => return Ok(EnforceOutcome::Stable),
                Some(_) => {}
                None => {
                    unknown = Some(arg);
                    unknown_count += 1;
                }
            }
        }
        match (unknown_count, unknown) {
            (0, _) => Ok(EnforceOutcome::Conflict),
            (1, Some(arg)) => self.enforce_bool(arg, desired, env, classes, memo, depth + 1),
            _ => Ok(EnforceOutcome::Stable),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn enforce_equality(
        &mut self,
        left: TermId,
        right: TermId,
        env: &mut Environment,
        classes: &IntClasses,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<EnforceOutcome, BvLiaUnsatAuthenticationError> {
        let left_value = self.eval_value(left, env, memo, depth + 1)?;
        let right_value = self.eval_value(right, env, memo, depth + 1)?;
        match (left_value, right_value) {
            (Some(left), Some(right)) => Ok(if self.values_equal(&left, &right)? {
                EnforceOutcome::Stable
            } else {
                EnforceOutcome::Conflict
            }),
            (None, Some(value)) if matches!(self.terms.get(left), TermData::Var(..)) => {
                self.assign_value(left, value, env, classes)
            }
            (Some(value), None) if matches!(self.terms.get(right), TermData::Var(..)) => {
                self.assign_value(right, value, env, classes)
            }
            _ => Ok(EnforceOutcome::Stable),
        }
    }

    fn assign_value(
        &mut self,
        term: TermId,
        value: Value,
        env: &mut Environment,
        classes: &IntClasses,
    ) -> Result<EnforceOutcome, BvLiaUnsatAuthenticationError> {
        let sort_matches = match (self.terms.sort(term), &value) {
            (Sort::Bool, Value::Bool(_)) | (Sort::Int, Value::Int(_)) => true,
            (Sort::BitVec(expected), Value::BitVec { width, .. }) => expected.width == *width,
            _ => false,
        };
        if !sort_matches {
            return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                reason: "an equality assigns a value of the wrong sort".to_string(),
            });
        }
        let assigned = match value {
            Value::Bool(value) => assign_plain(&mut env.bools, term, value),
            Value::Int(value) => match classes.members_for(term) {
                Some(members) => self.assign_int_members(members, &value, env),
                None => Ok(EnforceOutcome::Conflict),
            },
            Value::BitVec { value, width } => assign_plain(&mut env.bvs, term, (value, width)),
        }?;
        Ok(assigned)
    }

    fn eval_bool(
        &mut self,
        term: TermId,
        env: &Environment,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<Option<bool>, BvLiaUnsatAuthenticationError> {
        Ok(match self.eval_value(term, env, memo, depth)? {
            Some(Value::Bool(value)) => Some(value),
            _ => None,
        })
    }

    fn eval_value(
        &mut self,
        term: TermId,
        env: &Environment,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<Option<Value>, BvLiaUnsatAuthenticationError> {
        self.meter.charge(1)?;
        if depth > MAX_TERM_DEPTH {
            return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "evaluation depth",
            });
        }
        // Integer values own their BigInt payload. Never retain them in the
        // per-round DAG memo: repeated use is limb-metered instead, while the
        // cheap fixed-size Bool/BV values still benefit from memoization.
        if let Some(value @ (Value::Bool(_) | Value::BitVec { .. })) = memo.get(&term) {
            return Ok(Some(value.clone()));
        }
        let value = match self.terms.get(term) {
            TermData::Const(Constant::Bool(value)) => Some(Value::Bool(*value)),
            TermData::Const(Constant::Int(value)) => {
                Some(Value::Int(self.clone_bounded_int(value)?))
            }
            TermData::Const(Constant::BitVec { value, width }) => (*width > 0 && *width <= 64)
                .then(|| value.to_u64())
                .flatten()
                .map(|value| Value::BitVec {
                    value: value & bv_mask(*width),
                    width: *width,
                }),
            TermData::Var(..) => match self.terms.sort(term) {
                Sort::Bool => env.bools.get(&term).copied().map(Value::Bool),
                Sort::Int => match env.ints.get(&term) {
                    Some(value) => Some(Value::Int(self.clone_bounded_int(value)?)),
                    None => None,
                },
                Sort::BitVec(width) => {
                    env.bvs
                        .get(&term)
                        .copied()
                        .and_then(|(value, stored_width)| {
                            (stored_width == width.width).then_some(Value::BitVec {
                                value,
                                width: stored_width,
                            })
                        })
                }
                _ => None,
            },
            TermData::Not(inner) => self
                .eval_bool(*inner, env, memo, depth + 1)?
                .map(|value| Value::Bool(!value)),
            TermData::Ite(condition, then_term, else_term) => {
                match self.eval_bool(*condition, env, memo, depth + 1)? {
                    Some(true) => self.eval_value(*then_term, env, memo, depth + 1)?,
                    Some(false) => self.eval_value(*else_term, env, memo, depth + 1)?,
                    None => None,
                }
            }
            TermData::App(symbol, args) => match self.terms.sort(term) {
                Sort::Bool => self.eval_bool_app(symbol, args, env, memo, depth + 1)?,
                Sort::Int => self.eval_int_app(symbol, args, env, memo, depth + 1)?,
                Sort::BitVec(width) if width.width > 0 && width.width <= 64 => {
                    self.eval_bv_app(symbol, args, width.width, env, memo, depth + 1)?
                }
                _ => None,
            },
            _ => None,
        };
        if let Some(value @ (Value::Bool(_) | Value::BitVec { .. })) = &value {
            memo.insert(term, value.clone());
        }
        Ok(value)
    }

    fn eval_int(
        &mut self,
        term: TermId,
        env: &Environment,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<Option<BigInt>, BvLiaUnsatAuthenticationError> {
        Ok(match self.eval_value(term, env, memo, depth)? {
            Some(Value::Int(value)) => Some(value),
            _ => None,
        })
    }

    fn eval_bv(
        &mut self,
        term: TermId,
        env: &Environment,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<Option<(u64, u32)>, BvLiaUnsatAuthenticationError> {
        Ok(match self.eval_value(term, env, memo, depth)? {
            Some(Value::BitVec { value, width }) => Some((value, width)),
            _ => None,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EnforceOutcome {
    Stable,
    Changed,
    Conflict,
}

impl EnforceOutcome {
    fn combine(self, other: Self) -> Self {
        match (self, other) {
            (Self::Conflict, _) | (_, Self::Conflict) => Self::Conflict,
            (Self::Changed, _) | (_, Self::Changed) => Self::Changed,
            _ => Self::Stable,
        }
    }
}

enum AssignmentOutcome {
    Model,
    Refuted,
    Unknown,
}

fn assign_plain<T: Clone + PartialEq>(
    map: &mut HashMap<TermId, T>,
    term: TermId,
    value: T,
) -> Result<EnforceOutcome, BvLiaUnsatAuthenticationError> {
    Ok(match map.get(&term) {
        Some(existing) if existing != &value => EnforceOutcome::Conflict,
        Some(_) => EnforceOutcome::Stable,
        None => {
            map.insert(term, value);
            EnforceOutcome::Changed
        }
    })
}

fn named_app(terms: &TermStore, term: TermId) -> Option<(&str, &[TermId])> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => Some((name.as_str(), args.as_slice())),
        _ => None,
    }
}

fn is_int_var(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::Var(..)) && *terms.sort(term) == Sort::Int
}

fn int_constant(terms: &TermStore, term: TermId) -> Option<&BigInt> {
    match terms.get(term) {
        TermData::Const(Constant::Int(value)) => Some(value),
        _ => None,
    }
}

fn var_const_pair<'a>(terms: &'a TermStore, args: &[TermId]) -> Option<(TermId, &'a BigInt)> {
    if is_int_var(terms, args[0]) {
        int_constant(terms, args[1]).map(|value| (args[0], value))
    } else if is_int_var(terms, args[1]) {
        int_constant(terms, args[0]).map(|value| (args[1], value))
    } else {
        None
    }
}

fn bv_mask(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1_u64 << width) - 1
    }
}

fn signed_bv(value: u64, width: u32) -> i128 {
    let value = value & bv_mask(width);
    if ((value >> (width - 1)) & 1) == 0 {
        i128::from(value)
    } else {
        i128::from(value) - (1_i128 << width)
    }
}

fn arithmetic_shift_right(value: u64, amount: u64, width: u32) -> u64 {
    let mask = bv_mask(width);
    let negative = ((value >> (width - 1)) & 1) != 0;
    if amount >= u64::from(width) {
        return if negative { mask } else { 0 };
    }
    if amount == 0 {
        return value & mask;
    }
    let logical = value >> amount;
    if negative {
        logical | (mask ^ (mask >> amount))
    } else {
        logical
    }
}

#[cfg(test)]
#[path = "bv_lia_query_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "bv_lia_query_resource_tests.rs"]
mod resource_tests;
