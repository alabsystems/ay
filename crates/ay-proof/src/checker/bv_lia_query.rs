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
use num_traits::{One, Signed, ToPrimitive, Zero};

const MAX_QUERY_ROOTS: usize = 256;
const MAX_TERM_NODES: usize = 100_000;
const MAX_TERM_DEPTH: usize = 256;
const MAX_ENUMERATED_ASSIGNMENTS: u64 = 1 << 16;
const MAX_PROPAGATION_ROUNDS: usize = 512;
const MAX_WORK: u64 = 100_000_000;

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
    /// 256-root cap produced "independent source-level BV/LIA check rejected
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
    if roots.len() > MAX_QUERY_ROOTS {
        return Err(BvLiaUnsatAuthenticationError::TooManyRoots {
            limit: MAX_QUERY_ROOTS,
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
    bvs: HashMap<TermId, (u64, u32)>,
}

struct CollectedVariables {
    ints: Vec<TermId>,
    bools: Vec<TermId>,
    bitvecs: Vec<(TermId, u32)>,
}

#[derive(Clone)]
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

    fn assign(&self, digit: u64, env: &mut Environment) {
        match self {
            Self::Bool(term) => {
                env.bools.insert(*term, digit != 0);
            }
            Self::BitVec { term, width } => {
                env.bvs.insert(*term, (digit & bv_mask(*width), *width));
            }
            Self::IntClass { members, lower, .. } => {
                let value = lower + BigInt::from(digit);
                for &member in members {
                    env.ints.insert(member, value.clone());
                }
            }
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
    fn assign(&self, term: TermId, value: BigInt, env: &mut Environment) -> Result<bool, ()> {
        let Some(&class) = self.class_of.get(&term) else {
            return Err(());
        };
        let mut changed = false;
        for &member in &self.members[class] {
            match env.ints.get(&member) {
                Some(existing) if existing != &value => return Err(()),
                Some(_) => {}
                None => {
                    env.ints.insert(member, value.clone());
                    changed = true;
                }
            }
        }
        Ok(changed)
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
        if (self.work & 0x3fff) == 0
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
}

impl<'a> QueryChecker<'a> {
    fn new(terms: &'a TermStore, deadline: Option<Instant>) -> Self {
        Self {
            terms,
            meter: Meter { work: 0, deadline },
        }
    }

    fn decide(&mut self, roots: &[TermId]) -> Result<QueryDecision, BvLiaUnsatAuthenticationError> {
        self.meter.check_entry()?;
        let assertions = self.flatten_assertions(roots)?;
        let variables = self.collect_variables(roots)?;
        let classes = self.build_int_classes(&variables.ints, &assertions)?;

        if self.has_structural_contradiction(&assertions, &classes)? {
            return Ok(QueryDecision::Unsat);
        }

        let dimensions = self.build_dimensions(&classes, &variables.bools, &variables.bitvecs)?;
        let total = dimensions.iter().try_fold(1_u64, |total, dimension| {
            total
                .checked_mul(dimension.count())
                .filter(|count| *count <= MAX_ENUMERATED_ASSIGNMENTS)
                .ok_or(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                    reason: format!("finite assignment space exceeds {MAX_ENUMERATED_ASSIGNMENTS}"),
                })
        })?;

        for ordinal in 0..total {
            self.meter.charge(1)?;
            let mut env = Environment::default();
            let mut remaining = ordinal;
            for dimension in &dimensions {
                let count = dimension.count();
                dimension.assign(remaining % count, &mut env);
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

    fn flatten_assertions(
        &mut self,
        roots: &[TermId],
    ) -> Result<Vec<TermId>, BvLiaUnsatAuthenticationError> {
        let mut out = Vec::new();
        let mut stack: Vec<TermId> = roots.iter().rev().copied().collect();
        while let Some(term) = stack.pop() {
            self.meter.charge(1)?;
            if out.len() + stack.len() > MAX_TERM_NODES {
                return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                    resource: "flattened assertion nodes",
                });
            }
            match self.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "and" => {
                    stack.extend(args.iter().rev().copied());
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

        for &assertion in assertions {
            self.record_int_bound(assertion, &mut classes)?;
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
                    tighten_lower(&mut classes.bounds[class], value.clone());
                    tighten_upper(&mut classes.bounds[class], value);
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
            "<" => tighten_upper(&mut classes.bounds[class], constant - BigInt::one()),
            "<=" => tighten_upper(&mut classes.bounds[class], constant),
            ">" => tighten_lower(&mut classes.bounds[class], constant + BigInt::one()),
            ">=" => tighten_lower(&mut classes.bounds[class], constant),
            _ => {}
        }
        Ok(())
    }

    fn has_structural_contradiction(
        &mut self,
        assertions: &[TermId],
        classes: &IntClasses,
    ) -> Result<bool, BvLiaUnsatAuthenticationError> {
        for bounds in &classes.bounds {
            if matches!((&bounds.lower, &bounds.upper), (Some(lower), Some(upper)) if lower > upper)
            {
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
        Ok(false)
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
        let Some((left_low, left_high)) = int_interval(self.terms, args[0], 0) else {
            return Ok(false);
        };
        let Some((right_low, right_high)) = int_interval(self.terms, args[1], 0) else {
            return Ok(false);
        };
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
        let left = semantic_int_key(self.terms, args[0], classes);
        let right = semantic_int_key(self.terms, args[1], classes);
        let Some((left, right)) = left.zip(right) else {
            return Ok(false);
        };
        if left != right {
            return Ok(false);
        }
        let value = matches!(name, "<=" | ">=" | "=");
        Ok(value != desired)
    }

    fn build_dimensions(
        &mut self,
        classes: &IntClasses,
        bool_vars: &[TermId],
        bv_vars: &[(TermId, u32)],
    ) -> Result<Vec<Dimension>, BvLiaUnsatAuthenticationError> {
        let mut dimensions = Vec::new();
        for (class, members) in classes.members.iter().enumerate() {
            let (Some(lower), Some(upper)) = (
                classes.bounds[class].lower.as_ref(),
                classes.bounds[class].upper.as_ref(),
            ) else {
                continue;
            };
            if upper < lower {
                continue;
            }
            let count = (upper - lower + BigInt::one()).to_u64().ok_or_else(|| {
                BvLiaUnsatAuthenticationError::UnsupportedFragment {
                    reason: "integer domain does not fit the finite enumeration counter"
                        .to_string(),
                }
            })?;
            if count > MAX_ENUMERATED_ASSIGNMENTS {
                return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                    reason: format!(
                        "integer domain has {count} values, above {MAX_ENUMERATED_ASSIGNMENTS}"
                    ),
                });
            }
            dimensions.push(Dimension::IntClass {
                members: members.clone(),
                lower: lower.clone(),
                count,
            });
        }
        dimensions.extend(bool_vars.iter().copied().map(Dimension::Bool));
        for &(term, width) in bv_vars {
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
            (Some(left), Some(right)) => Ok(if left == right {
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
        &self,
        term: TermId,
        value: Value,
        env: &mut Environment,
        classes: &IntClasses,
    ) -> Result<EnforceOutcome, BvLiaUnsatAuthenticationError> {
        let assigned = match value {
            Value::Bool(value) => assign_plain(&mut env.bools, term, value),
            Value::Int(value) => match classes.assign(term, value, env) {
                Ok(true) => Ok(EnforceOutcome::Changed),
                Ok(false) => Ok(EnforceOutcome::Stable),
                Err(()) => Ok(EnforceOutcome::Conflict),
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
        if let Some(value) = memo.get(&term) {
            return Ok(Some(value.clone()));
        }
        let value = match self.terms.get(term) {
            TermData::Const(Constant::Bool(value)) => Some(Value::Bool(*value)),
            TermData::Const(Constant::Int(value)) => Some(Value::Int(value.clone())),
            TermData::Const(Constant::BitVec { value, width }) => (*width > 0 && *width <= 64)
                .then(|| value.to_u64())
                .flatten()
                .map(|value| Value::BitVec {
                    value: value & bv_mask(*width),
                    width: *width,
                }),
            TermData::Var(..) => match self.terms.sort(term) {
                Sort::Bool => env.bools.get(&term).copied().map(Value::Bool),
                Sort::Int => env.ints.get(&term).cloned().map(Value::Int),
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
        if let Some(value) = &value {
            memo.insert(term, value.clone());
        }
        Ok(value)
    }

    fn eval_bool_app(
        &mut self,
        symbol: &Symbol,
        args: &[TermId],
        env: &Environment,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<Option<Value>, BvLiaUnsatAuthenticationError> {
        let name = symbol.name();
        let bool_value = match name {
            "and" => {
                let mut unknown = false;
                for &arg in args {
                    match self.eval_bool(arg, env, memo, depth + 1)? {
                        Some(false) => return Ok(Some(Value::Bool(false))),
                        Some(true) => {}
                        None => unknown = true,
                    }
                }
                (!unknown).then_some(true)
            }
            "or" => {
                let mut unknown = false;
                for &arg in args {
                    match self.eval_bool(arg, env, memo, depth + 1)? {
                        Some(true) => return Ok(Some(Value::Bool(true))),
                        Some(false) => {}
                        None => unknown = true,
                    }
                }
                (!unknown).then_some(false)
            }
            "not" if args.len() == 1 => self
                .eval_bool(args[0], env, memo, depth + 1)?
                .map(|value| !value),
            "=>" | "implies" if args.len() == 2 => {
                match (
                    self.eval_bool(args[0], env, memo, depth + 1)?,
                    self.eval_bool(args[1], env, memo, depth + 1)?,
                ) {
                    (Some(false), _) | (_, Some(true)) => Some(true),
                    (Some(true), Some(false)) => Some(false),
                    _ => None,
                }
            }
            "xor" if args.len() == 2 => self
                .eval_bool(args[0], env, memo, depth + 1)?
                .zip(self.eval_bool(args[1], env, memo, depth + 1)?)
                .map(|(left, right)| left ^ right),
            "=" if args.len() == 2 => self
                .eval_value(args[0], env, memo, depth + 1)?
                .zip(self.eval_value(args[1], env, memo, depth + 1)?)
                .map(|(left, right)| left == right),
            "distinct" if args.len() == 2 => self
                .eval_value(args[0], env, memo, depth + 1)?
                .zip(self.eval_value(args[1], env, memo, depth + 1)?)
                .map(|(left, right)| left != right),
            "<" | "<=" | ">" | ">=" if args.len() == 2 => self
                .eval_int(args[0], env, memo, depth + 1)?
                .zip(self.eval_int(args[1], env, memo, depth + 1)?)
                .map(|(left, right)| match name {
                    "<" => left < right,
                    "<=" => left <= right,
                    ">" => left > right,
                    ">=" => left >= right,
                    _ => unreachable!(),
                }),
            "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
                if args.len() == 2 =>
            {
                self.eval_bv(args[0], env, memo, depth + 1)?
                    .zip(self.eval_bv(args[1], env, memo, depth + 1)?)
                    .and_then(|((left, left_width), (right, right_width))| {
                        (left_width == right_width).then(|| match name {
                            "bvult" => left < right,
                            "bvule" => left <= right,
                            "bvugt" => left > right,
                            "bvuge" => left >= right,
                            "bvslt" => signed_bv(left, left_width) < signed_bv(right, right_width),
                            "bvsle" => signed_bv(left, left_width) <= signed_bv(right, right_width),
                            "bvsgt" => signed_bv(left, left_width) > signed_bv(right, right_width),
                            "bvsge" => signed_bv(left, left_width) >= signed_bv(right, right_width),
                            _ => unreachable!(),
                        })
                    })
            }
            _ => None,
        };
        Ok(bool_value.map(Value::Bool))
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

    fn eval_int_app(
        &mut self,
        symbol: &Symbol,
        args: &[TermId],
        env: &Environment,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<Option<Value>, BvLiaUnsatAuthenticationError> {
        let name = symbol.name();
        let value = match name {
            "+" => {
                let mut value = BigInt::zero();
                for &arg in args {
                    let Some(arg) = self.eval_int(arg, env, memo, depth + 1)? else {
                        return Ok(None);
                    };
                    value += arg;
                }
                Some(value)
            }
            "-" => match args {
                [] => None,
                [arg] => self
                    .eval_int(*arg, env, memo, depth + 1)?
                    .map(|value| -value),
                [first, rest @ ..] => {
                    let Some(mut value) = self.eval_int(*first, env, memo, depth + 1)? else {
                        return Ok(None);
                    };
                    for &arg in rest {
                        let Some(arg) = self.eval_int(arg, env, memo, depth + 1)? else {
                            return Ok(None);
                        };
                        value -= arg;
                    }
                    Some(value)
                }
            },
            "*" => {
                let mut value = BigInt::one();
                for &arg in args {
                    let Some(arg) = self.eval_int(arg, env, memo, depth + 1)? else {
                        return Ok(None);
                    };
                    value *= arg;
                }
                Some(value)
            }
            "mod" if args.len() == 2 => {
                let dividend = self.eval_int(args[0], env, memo, depth + 1)?;
                let divisor = self.eval_int(args[1], env, memo, depth + 1)?;
                match (dividend, divisor) {
                    (Some(dividend), Some(divisor)) if divisor.is_positive() => {
                        let mut residue = dividend % &divisor;
                        if residue.is_negative() {
                            residue += divisor;
                        }
                        Some(residue)
                    }
                    _ => None,
                }
            }
            "abs" if args.len() == 1 => self
                .eval_int(args[0], env, memo, depth + 1)?
                .map(|value| value.abs()),
            "bv2nat" if args.len() == 1 => self
                .eval_bv(args[0], env, memo, depth + 1)?
                .map(|(value, _)| BigInt::from(value)),
            _ => None,
        };
        Ok(value.map(Value::Int))
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

    #[allow(clippy::too_many_arguments)]
    fn eval_bv_app(
        &mut self,
        symbol: &Symbol,
        args: &[TermId],
        expected_width: u32,
        env: &Environment,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<Option<Value>, BvLiaUnsatAuthenticationError> {
        if let Symbol::Indexed(name, indices) = symbol {
            if name == "int2bv" && indices.as_slice() == [expected_width] && args.len() == 1 {
                let value = self.eval_int(args[0], env, memo, depth + 1)?;
                return Ok(value
                    .as_ref()
                    .and_then(|value| bigint_residue_u64(value, expected_width))
                    .map(|value| Value::BitVec {
                        value,
                        width: expected_width,
                    }));
            }
            if args.len() == 1 {
                let Some((value, width)) = self.eval_bv(args[0], env, memo, depth + 1)? else {
                    return Ok(None);
                };
                let result = match (name.as_str(), indices.as_slice()) {
                    ("extract", [high, low]) if high >= low && *high < width => {
                        Some((value >> low, high - low + 1))
                    }
                    ("zero_extend", [added])
                        if width.checked_add(*added) == Some(expected_width) =>
                    {
                        Some((value, expected_width))
                    }
                    ("sign_extend", [added])
                        if width.checked_add(*added) == Some(expected_width) =>
                    {
                        let signed = signed_bv(value, width);
                        Some((
                            (signed as u128 & u128::from(bv_mask(expected_width))) as u64,
                            expected_width,
                        ))
                    }
                    _ => None,
                };
                return Ok(result.map(|(value, width)| Value::BitVec {
                    value: value & bv_mask(width),
                    width,
                }));
            }
            return Ok(None);
        }

        let name = symbol.name();
        if matches!(name, "bvnot" | "bvneg") && args.len() == 1 {
            let value = self.eval_bv(args[0], env, memo, depth + 1)?;
            return Ok(value.map(|(value, width)| Value::BitVec {
                value: if name == "bvnot" {
                    !value & bv_mask(width)
                } else {
                    0_u64.wrapping_sub(value) & bv_mask(width)
                },
                width,
            }));
        }
        if args.len() != 2 {
            return Ok(None);
        }
        let Some((left, left_width)) = self.eval_bv(args[0], env, memo, depth + 1)? else {
            return Ok(None);
        };
        let Some((right, right_width)) = self.eval_bv(args[1], env, memo, depth + 1)? else {
            return Ok(None);
        };
        if name == "concat" {
            let Some(width) = left_width.checked_add(right_width) else {
                return Ok(None);
            };
            if width != expected_width || width > 64 {
                return Ok(None);
            }
            let value = if right_width == 64 {
                right
            } else {
                (left << right_width) | right
            };
            return Ok(Some(Value::BitVec {
                value: value & bv_mask(width),
                width,
            }));
        }
        if left_width != right_width || left_width != expected_width {
            return Ok(None);
        }
        let width = left_width;
        let mask = bv_mask(width);
        let value = match name {
            "bvadd" => left.wrapping_add(right) & mask,
            "bvsub" => left.wrapping_sub(right) & mask,
            "bvmul" => left.wrapping_mul(right) & mask,
            "bvand" => left & right,
            "bvor" => left | right,
            "bvxor" => left ^ right,
            "bvnand" => !(left & right) & mask,
            "bvnor" => !(left | right) & mask,
            "bvxnor" => !(left ^ right) & mask,
            "bvshl" => {
                if right >= u64::from(width) {
                    0
                } else {
                    left.wrapping_shl(right as u32) & mask
                }
            }
            "bvlshr" => {
                if right >= u64::from(width) {
                    0
                } else {
                    left >> right
                }
            }
            "bvashr" => arithmetic_shift_right(left, right, width),
            _ => return Ok(None),
        };
        Ok(Some(Value::BitVec { value, width }))
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

fn int_constant(terms: &TermStore, term: TermId) -> Option<BigInt> {
    match terms.get(term) {
        TermData::Const(Constant::Int(value)) => Some(value.clone()),
        _ => None,
    }
}

fn var_const_pair(terms: &TermStore, args: &[TermId]) -> Option<(TermId, BigInt)> {
    if is_int_var(terms, args[0]) {
        int_constant(terms, args[1]).map(|value| (args[0], value))
    } else if is_int_var(terms, args[1]) {
        int_constant(terms, args[0]).map(|value| (args[1], value))
    } else {
        None
    }
}

fn tighten_lower(bounds: &mut ClassBounds, value: BigInt) {
    if bounds
        .lower
        .as_ref()
        .is_none_or(|existing| existing < &value)
    {
        bounds.lower = Some(value);
    }
}

fn tighten_upper(bounds: &mut ClassBounds, value: BigInt) {
    if bounds
        .upper
        .as_ref()
        .is_none_or(|existing| existing > &value)
    {
        bounds.upper = Some(value);
    }
}

fn int_interval(terms: &TermStore, term: TermId, depth: usize) -> Option<(BigInt, BigInt)> {
    if depth > MAX_TERM_DEPTH {
        return None;
    }
    match terms.get(term) {
        TermData::Const(Constant::Int(value)) => Some((value.clone(), value.clone())),
        TermData::App(Symbol::Named(name), args) if name == "bv2nat" && args.len() == 1 => {
            let Sort::BitVec(width) = terms.sort(args[0]) else {
                return None;
            };
            if width.width == 0 || width.width > 64 {
                return None;
            }
            Some((
                BigInt::zero(),
                (BigInt::one() << width.width) - BigInt::one(),
            ))
        }
        _ => None,
    }
}

fn semantic_int_key(terms: &TermStore, term: TermId, classes: &IntClasses) -> Option<usize> {
    if let Some(class) = classes.semantic_key(term) {
        return Some(class);
    }
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if name != "bv2nat" || args.len() != 1 {
        return None;
    }
    let TermData::App(Symbol::Indexed(name, indices), int_args) = terms.get(args[0]) else {
        return None;
    };
    if name != "int2bv" || indices.len() != 1 || int_args.len() != 1 {
        return None;
    }
    if indices[0] == 0 || indices[0] > 64 {
        return None;
    }
    let class = classes.semantic_key(int_args[0])?;
    let bounds = &classes.bounds[class];
    let lower = bounds.lower.as_ref()?;
    let upper = bounds.upper.as_ref()?;
    let max = (BigInt::one() << indices[0]) - BigInt::one();
    (lower >= &BigInt::zero() && upper <= &max).then_some(class)
}

fn bv_mask(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1_u64 << width) - 1
    }
}

fn bigint_residue_u64(value: &BigInt, width: u32) -> Option<u64> {
    if width == 0 || width > 64 {
        return None;
    }
    let modulus = BigInt::one() << width;
    let mut residue = value % &modulus;
    if residue.is_negative() {
        residue += modulus;
    }
    residue.to_u64().map(|value| value & bv_mask(width))
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
mod tests {
    use ay_core::{Sort, Symbol, TermStore};
    use num_bigint::BigInt;

    use super::{authenticate_bv_lia_unsat_query, BvLiaUnsatAuthenticationError};

    #[test]
    fn bounded_bv_to_nat_query_authenticates_and_rejects_sat_near_miss() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("bridge_x", Sort::bitvec(4));
        let nat = terms.mk_bv2nat(x);
        let five = terms.mk_int(5.into());
        let three_bv = terms.mk_bitvec(BigInt::from(3_u8), 4);
        let above_five = terms.mk_gt(nat, five);
        let below_three = terms.mk_bvult(x, three_bv);
        let roots = [above_five, below_three];
        let evidence = authenticate_bv_lia_unsat_query(&terms, &roots, None)
            .expect("finite BV enumeration proves the bridge contradiction");
        assert!(evidence.is_current_for(&terms, &roots));

        let ten_bv = terms.mk_bitvec(BigInt::from(10_u8), 4);
        let below_ten = terms.mk_bvult(x, ten_bv);
        let sat_roots = [above_five, below_ten];
        let error = authenticate_bv_lia_unsat_query(&terms, &sat_roots, None)
            .expect_err("x=6 witnesses the near-miss query");
        assert!(matches!(error, BvLiaUnsatAuthenticationError::Satisfiable));
    }

    #[test]
    fn universal_bv2nat_range_rejects_unbounded_source_violation() {
        let mut terms = TermStore::new();
        let source = terms.mk_var("bridge_e", Sort::Int);
        let bv = terms.mk_int2bv(8, source);
        let nat = terms.mk_bv2nat(bv);
        let max = terms.mk_int(255.into());
        let impossible = terms.mk_gt(nat, max);
        authenticate_bv_lia_unsat_query(&terms, &[impossible], None)
            .expect("bv2nat is universally bounded by its width");
    }

    #[test]
    fn in_range_int2bv_residue_identity_is_symbolically_checked() {
        let mut terms = TermStore::new();
        let source = terms.mk_var("bridge_source", Sort::Int);
        let zero = terms.mk_int(0.into());
        let modulus = terms.mk_int((1_i64 << 32).into());
        let nonnegative = terms.mk_ge(source, zero);
        let below_modulus = terms.mk_lt(source, modulus);
        let bv = terms.mk_int2bv(32, source);
        let nat = terms.mk_bv2nat(bv);
        let impossible = terms.mk_gt(nat, source);
        authenticate_bv_lia_unsat_query(&terms, &[nonnegative, below_modulus, impossible], None)
            .expect("in-range int2bv/bv2nat is the identity");
    }

    #[test]
    fn evidence_retires_after_term_snapshot_change() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("bridge_stale_x", Sort::bitvec(2));
        let zero = terms.mk_bitvec(BigInt::from(0_u8), 2);
        let lt_zero = terms.mk_app(Symbol::named("bvult"), [x, zero], Sort::Bool);
        let evidence = authenticate_bv_lia_unsat_query(&terms, &[lt_zero], None)
            .expect("unsigned value cannot be below zero");
        let _late = terms.mk_var("bridge_stale_late", Sort::Bool);
        assert!(!evidence.term_snapshot_is_current(&terms));
    }

    #[test]
    fn malformed_or_oversized_bv_widths_fail_closed() {
        let mut terms = TermStore::new();
        let zero_width = terms.mk_bitvec(BigInt::from(0_u8), 0);
        let signed_lt = terms.mk_app(Symbol::named("bvslt"), [zero_width, zero_width], Sort::Bool);
        let zero_error = authenticate_bv_lia_unsat_query(&terms, &[signed_lt], None)
            .expect_err("zero-width signed arithmetic is outside the checked fragment");
        assert!(matches!(
            zero_error,
            BvLiaUnsatAuthenticationError::UnsupportedFragment { .. }
        ));

        let source = terms.mk_var("bridge_huge_width_source", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0_u8));
        let one = terms.mk_int(BigInt::from(1_u8));
        let lower = terms.mk_ge(source, zero);
        let upper = terms.mk_le(source, one);
        let huge_bv = terms.mk_int2bv(u32::MAX, source);
        let huge_nat = terms.mk_bv2nat(huge_bv);
        let impossible = terms.mk_gt(huge_nat, source);
        let huge_error = authenticate_bv_lia_unsat_query(&terms, &[lower, upper, impossible], None)
            .expect_err("oversized int2bv width must not allocate or certify");
        assert!(matches!(
            huge_error,
            BvLiaUnsatAuthenticationError::UnsupportedFragment { .. }
        ));
    }

    #[test]
    fn long_integer_equality_chain_uses_bounded_stack() {
        const VARIABLES: usize = 20_000;

        let mut terms = TermStore::new();
        let vars: Vec<_> = (0..VARIABLES)
            .map(|index| terms.mk_var(format!("bridge_chain_{index}"), Sort::Int))
            .collect();
        let mut conjuncts = Vec::with_capacity(VARIABLES + 1);
        // This orientation deliberately creates the deepest tree for the
        // union policy before the final class walk compresses it.
        for index in 1..VARIABLES {
            conjuncts.push(terms.mk_eq(vars[index], vars[index - 1]));
        }
        let zero = terms.mk_int(BigInt::from(0_u8));
        let one = terms.mk_int(BigInt::from(1_u8));
        conjuncts.push(terms.mk_eq(vars[0], zero));
        conjuncts.push(terms.mk_eq(vars[VARIABLES - 1], one));
        let root = terms.mk_app(Symbol::named("and"), conjuncts, Sort::Bool);

        authenticate_bv_lia_unsat_query(&terms, &[root], None)
            .expect("the long equality chain is contradictory without recursive find");
    }
}
