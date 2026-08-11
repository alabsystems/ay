// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A small, solver-independent checker for projection-model certificates.
//!
//! Candidate generation is deliberately outside this module and is not trusted.
//! This checker accepts only a single direct universal implication for which
//! total argument projections turn the conclusion into a consequence of
//! acyclic binder equalities in the premise. It never calls a solver and never
//! uses `TermStore`'s simplifying constructors.

use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
#[cfg(test)]
use num_bigint::BigInt;
use num_bigint::Sign;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;

/// Maximum traversal depth accepted by the projection proof kernel.
const MAX_PROJECTION_DEPTH: usize = 4096;

/// Maximum number of normalization visits accepted by the proof kernel.
const MAX_PROJECTION_STEPS: usize = 10_000_000;

/// One untrusted proposal for a total UF projection.
///
/// The proposed interpretation is
/// `symbol(p_0, ..., p_n) = p_projected_parameter`. All fields are public so an
/// untrusted producer can construct candidates. Acceptance independently checks
/// the complete signature, every occurrence, and the selected parameter sort.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectionUfCandidate {
    /// The exact core symbol being defined.
    pub symbol: Symbol,
    /// The complete declared parameter signature, in application order.
    pub parameter_sorts: Vec<Sort>,
    /// The declared result sort.
    pub result_sort: Sort,
    /// The formal parameter returned by this total projection.
    pub projected_parameter: usize,
}

/// Untrusted input to the projection implication checker.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectionImplicationCandidate {
    /// One proposed total projection for every UF occurring in the assertion.
    pub definitions: Vec<ProjectionUfCandidate>,
    /// The untrusted choice of the implication's consequent.
    ///
    /// The checker independently requires this to be the direct consequent or
    /// exactly one top-level operand of the frontend's flattened OR clause.
    pub conclusion: TermId,
}

/// A checked UF projection stored inside [`CheckedProjectionImplication`].
///
/// Its fields are private: only the checker can construct a checked definition.
#[derive(Debug)]
pub struct CheckedProjectionUf {
    symbol: Symbol,
    parameter_sorts: Vec<Sort>,
    result_sort: Sort,
    projected_parameter: usize,
    binder_permutation: Vec<usize>,
}

impl CheckedProjectionUf {
    /// The exact core symbol interpreted by this definition.
    #[must_use]
    pub fn symbol(&self) -> &Symbol {
        &self.symbol
    }

    /// The checked formal-parameter sorts, in application order.
    #[must_use]
    pub fn parameter_sorts(&self) -> &[Sort] {
        &self.parameter_sorts
    }

    /// The checked result sort.
    #[must_use]
    pub fn result_sort(&self) -> &Sort {
        &self.result_sort
    }

    /// The formal parameter returned by the total projection.
    #[must_use]
    pub fn projected_parameter(&self) -> usize {
        self.projected_parameter
    }

    /// The universal-binder index supplied at each formal parameter position.
    #[must_use]
    pub fn binder_permutation(&self) -> &[usize] {
        &self.binder_permutation
    }
}

/// Opaque evidence that the projection implication checker accepted its
/// semantic projection obligation.
///
/// The type intentionally does not implement `Clone`, and all fields are
/// private. A caller can inspect the exact checked root and total definitions,
/// but cannot mint evidence from a raw solver result or candidate.
///
/// This value is deliberately not standalone SAT authority. `TermStore`
/// currently erases declaration kind into named symbols, so a future steering
/// path must also consume positive, scope-bound evidence that every selected
/// symbol is a live ordinary UF declaration rather than a built-in, definition,
/// datatype member, overload, adopted macro, or internal symbol.
#[derive(Debug)]
pub struct CheckedProjectionImplication {
    assertions: Vec<TermId>,
    checked_term_count: usize,
    frozen_terms: Vec<FrozenTerm>,
    definitions: Vec<CheckedProjectionUf>,
}

#[derive(Debug)]
struct FrozenTerm {
    id: TermId,
    data: TermData,
    sort: Sort,
}

impl CheckedProjectionImplication {
    /// The sole original assertion checked by this certificate.
    pub fn assertion(&self) -> TermId {
        self.assertions[0]
    }

    /// The exact original root vector bound to this certificate.
    pub fn assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// The `TermStore` length at the instant this certificate was checked.
    ///
    /// This is lifecycle metadata, not a digest. A verdict-authority layer must
    /// additionally bind the certificate to its frozen snapshot and scope epoch.
    #[must_use]
    pub fn checked_term_count(&self) -> usize {
        self.checked_term_count
    }

    /// The total UF projections independently checked for the assertion.
    #[must_use]
    pub fn definitions(&self) -> &[CheckedProjectionUf] {
        &self.definitions
    }

    /// Whether the supplied roots and every reachable term still exactly match
    /// the immutable snapshot accepted by the checker.
    ///
    /// This catches term-suffix rollback/reuse in addition to root-vector
    /// changes. The SAT authority layer must also compare its scope epoch.
    #[must_use]
    pub fn matches_snapshot(&self, terms: &TermStore, assertions: &[TermId]) -> bool {
        assertions == self.assertions
            && self.frozen_terms.iter().all(|frozen| {
                frozen.id.index() < terms.len()
                    && terms.get(frozen.id) == &frozen.data
                    && terms.sort(frozen.id) == &frozen.sort
            })
    }
}

/// A typed, fail-closed reason why a projection candidate was rejected.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProjectionCertificateRejection {
    /// The checker requires exactly one assertion.
    AssertionCount {
        /// Number of assertions supplied.
        found: usize,
    },
    /// A term identifier was outside the supplied store.
    InvalidTermId {
        /// Invalid identifier.
        term: TermId,
    },
    /// The sole root was not a direct positive universal quantifier.
    RootNotDirectForall,
    /// The universal quantifier had no binders.
    EmptyBinderList,
    /// A quantifier carried a user trigger.
    NonEmptyTriggers,
    /// A binder or body term used a sort outside Bool/fixed-width-BV.
    UnsupportedSort {
        /// Term carrying the unsupported sort, when one exists.
        term: Option<TermId>,
        /// Unsupported sort.
        sort: Box<Sort>,
    },
    /// Two binder declarations used the same visible name.
    DuplicateBinderName {
        /// Repeated name.
        name: String,
    },
    /// No body variable represented one declared binder.
    MissingBinderOccurrence {
        /// Binder name.
        name: String,
    },
    /// More than one core variable identity represented one binder name/sort.
    AmbiguousBinderIdentity {
        /// Binder name.
        name: String,
    },
    /// A binder occurrence had the declared name but a different sort.
    BinderSortMismatch {
        /// Binder name.
        name: String,
        /// Declared binder sort.
        declared: Box<Sort>,
        /// Sort found on the occurrence.
        found: Box<Sort>,
    },
    /// A nested quantifier, existential, let, or unknown core node was found.
    UnsupportedNode {
        /// Offending term.
        term: TermId,
        /// Stable diagnostic category.
        kind: &'static str,
    },
    /// The body was neither a direct implication nor its exact accepted OR form.
    BodyNotImplication,
    /// The proposed conclusion was not exactly one accepted top-level operand.
    ConclusionNotTopLevelOperand {
        /// Untrusted proposed conclusion.
        conclusion: TermId,
    },
    /// The candidate proposed no UF projection.
    NoDefinitions,
    /// A projection attempted to define a built-in or indexed symbol.
    UnsupportedDefinitionSymbol {
        /// Offending symbol.
        symbol: Symbol,
    },
    /// Two candidate entries attempted to define one symbol.
    DuplicateDefinition {
        /// Duplicated symbol.
        symbol: Symbol,
    },
    /// A proposed declaration did not have one parameter per binder.
    DefinitionArityMismatch {
        /// Offending symbol.
        symbol: Symbol,
        /// Expected arity.
        expected: usize,
        /// Proposed arity.
        found: usize,
    },
    /// A proposed projection index was outside the signature.
    ProjectionOutOfRange {
        /// Offending symbol.
        symbol: Symbol,
        /// Proposed parameter index.
        projected_parameter: usize,
        /// Signature arity.
        arity: usize,
    },
    /// The selected parameter sort differed from the UF result sort.
    ProjectionSortMismatch {
        /// Offending symbol.
        symbol: Symbol,
        /// Selected parameter sort.
        parameter_sort: Box<Sort>,
        /// UF result sort.
        result_sort: Box<Sort>,
    },
    /// A term's recorded sort or a built-in signature was malformed.
    IllSortedTerm {
        /// Offending term.
        term: TermId,
    },
    /// An application was neither a supported built-in nor a selected UF.
    UnsupportedApplication {
        /// Offending term.
        term: TermId,
        /// Unrecognized symbol.
        symbol: Symbol,
    },
    /// A selected UF occurrence did not match its declared signature.
    ApplicationSignatureMismatch {
        /// Offending term.
        term: TermId,
        /// Selected symbol.
        symbol: Symbol,
    },
    /// A selected UF application did not contain each binder exactly once as a
    /// bare argument.
    ApplicationNotBinderPermutation {
        /// Offending term.
        term: TermId,
        /// Selected symbol.
        symbol: Symbol,
    },
    /// One selected symbol appeared with two different binder permutations.
    InconsistentApplicationPermutation {
        /// Offending term.
        term: TermId,
        /// Selected symbol.
        symbol: Symbol,
    },
    /// A proposed definition never occurred in the assertion.
    UnusedDefinition {
        /// Unused symbol.
        symbol: Symbol,
    },
    /// A premise conjunct was not an orientable binary binder equality.
    PremiseNotBinderEquality {
        /// Offending premise conjunct.
        term: TermId,
    },
    /// Two premise equalities attempted to rewrite the same binder.
    DuplicatePremiseDefinition {
        /// Repeatedly defined binder term.
        binder: TermId,
    },
    /// Premise binder definitions contained a dependency cycle.
    CyclicPremiseDefinitions,
    /// The independent normalizer left a residual conclusion instead of true.
    ConclusionDidNotNormalizeTrue,
    /// A checker-owned index or work stack violated an invariant established by
    /// earlier validation.
    ///
    /// This is fail-closed and indicates an implementation defect, not an input
    /// resource limit.
    InternalInvariant {
        /// Stable diagnostic category.
        kind: &'static str,
    },
    /// A recursion or work bound was reached.
    ResourceLimit,
    /// The caller's solve deadline, interrupt, or memory envelope fired.
    ///
    /// This is distinct from the deterministic checker work bound so the
    /// authority layer can preserve the caller's precise `unknown` reason.
    Stopped,
}

impl fmt::Display for ProjectionCertificateRejection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "projection certificate rejected: {self:?}")
    }
}

impl Error for ProjectionCertificateRejection {}

/// Independently check a total-projection implication candidate.
///
/// Acceptance proves the one supported universal assertion has a model formed
/// by interpreting every selected *free-function application* as its checked
/// total argument projection. Candidate generation, symbol spellings, and
/// solver state are not authority. Because the current core term graph does not
/// carry declaration kind, callers must combine this semantic result with an
/// independently checked source/declaration binding before it may steer SAT.
pub fn check_projection_implication(
    terms: &TermStore,
    assertions: &[TermId],
    candidate: &ProjectionImplicationCandidate,
) -> Result<CheckedProjectionImplication, ProjectionCertificateRejection> {
    check_projection_implication_with_stop(terms, assertions, candidate, || false)
}

/// Independently check a projection implication under a cooperative stop
/// source supplied by the solve authority layer.
///
/// The callback is polled throughout every potentially long traversal.  A
/// stop can only reject the candidate; it can never turn a rejected or partial
/// check into evidence.
pub fn check_projection_implication_with_stop(
    terms: &TermStore,
    assertions: &[TermId],
    candidate: &ProjectionImplicationCandidate,
    mut should_stop: impl FnMut() -> bool,
) -> Result<CheckedProjectionImplication, ProjectionCertificateRejection> {
    let mut stop = ProjectionStopPoller::new(&mut should_stop);
    stop.boundary()?;
    let [assertion] = assertions else {
        return Err(ProjectionCertificateRejection::AssertionCount {
            found: assertions.len(),
        });
    };
    let assertion = *assertion;
    let root = checked_data(terms, assertion)?;
    let TermData::Forall(binder_decls, body, triggers) = root else {
        return Err(ProjectionCertificateRejection::RootNotDirectForall);
    };
    if binder_decls.is_empty() {
        return Err(ProjectionCertificateRejection::EmptyBinderList);
    }
    if !triggers.is_empty() {
        return Err(ProjectionCertificateRejection::NonEmptyTriggers);
    }
    if terms.sort(assertion) != &Sort::Bool {
        return Err(ProjectionCertificateRejection::IllSortedTerm { term: assertion });
    }

    let mut binder_names = HashMap::new();
    for (index, (name, sort)) in binder_decls.iter().enumerate() {
        stop.step()?;
        require_supported_sort(None, sort)?;
        if binder_names.insert(name.as_str(), index).is_some() {
            return Err(ProjectionCertificateRejection::DuplicateBinderName { name: name.clone() });
        }
    }

    let binder_terms = discover_binder_terms(terms, *body, binder_decls, &binder_names, &mut stop)?;
    stop.charge(binder_terms.len())?;
    let binder_by_term: HashMap<TermId, usize> = binder_terms
        .iter()
        .copied()
        .enumerate()
        .map(|(index, term)| (term, index))
        .collect();

    let definitions = validate_candidates(candidate, binder_decls.len(), &mut stop)?;
    let mut validation = BodyValidation::new(
        terms,
        &binder_by_term,
        &definitions,
        &candidate.definitions,
        &mut stop,
    )?;
    validation.validate(*body, &mut stop)?;
    let checked_definitions = validation.finish(candidate, &mut stop)?;

    stop.boundary()?;
    checked_data(terms, candidate.conclusion)?;
    let implication = extract_implication(terms, *body, candidate.conclusion, &mut stop)?;
    let mut proved = false;
    let mut saw_acyclic_environment = false;
    for strategy in PREMISE_SELECTION_STRATEGIES {
        stop.boundary()?;
        let env = build_premise_environment(
            terms,
            &implication.premise_hypotheses,
            &binder_by_term,
            &definitions,
            &candidate.definitions,
            strategy,
            &mut stop,
        )?;
        match reject_environment_cycles(
            terms,
            &env,
            &binder_by_term,
            &definitions,
            &candidate.definitions,
            &mut stop,
        ) {
            Ok(()) => saw_acyclic_environment = true,
            Err(ProjectionCertificateRejection::CyclicPremiseDefinitions) => continue,
            Err(rejection) => return Err(rejection),
        }

        let mut normalizer = Normalizer::new(
            terms,
            &binder_by_term,
            &definitions,
            &candidate.definitions,
            &env,
        );
        let conclusion = normalizer.normalize(implication.conclusion, 0, &mut stop)?;
        if normalizer.is_bool_constant(conclusion, true) {
            proved = true;
            break;
        }
    }
    if !proved {
        return Err(if saw_acyclic_environment {
            ProjectionCertificateRejection::ConclusionDidNotNormalizeTrue
        } else {
            ProjectionCertificateRejection::CyclicPremiseDefinitions
        });
    }

    Ok(CheckedProjectionImplication {
        assertions: assertions.to_vec(),
        checked_term_count: terms.len(),
        frozen_terms: freeze_reachable_terms(terms, assertions, &mut stop)?,
        definitions: checked_definitions,
    })
}

/// Enforce one deterministic work budget across the complete proof check while
/// throttling cooperative stop callbacks.  Sharing this poller across every
/// phase prevents an early graph walk from escaping the normalization-only
/// limit or multiplying the advertised budget phase by phase.
struct ProjectionStopPoller<'a> {
    should_stop: &'a mut dyn FnMut() -> bool,
    until_poll: u8,
    remaining_work: usize,
}

impl<'a> ProjectionStopPoller<'a> {
    const INTERVAL: u8 = 64;

    fn new(should_stop: &'a mut dyn FnMut() -> bool) -> Self {
        Self {
            should_stop,
            until_poll: 0,
            remaining_work: MAX_PROJECTION_STEPS,
        }
    }

    #[cfg(test)]
    fn with_budget(should_stop: &'a mut dyn FnMut() -> bool, remaining_work: usize) -> Self {
        Self {
            should_stop,
            until_poll: 0,
            remaining_work,
        }
    }

    fn boundary(&mut self) -> Result<(), ProjectionCertificateRejection> {
        self.until_poll = Self::INTERVAL;
        if (self.should_stop)() {
            Err(ProjectionCertificateRejection::Stopped)
        } else {
            Ok(())
        }
    }

    /// Charge deterministic work before performing it.
    ///
    /// Bulk callers use this before allocating, cloning, or scheduling a whole
    /// child list.  An over-budget operation is therefore rejected before any
    /// of that work occurs.  Polling happens before the operation whenever it
    /// would cross the 64-unit polling boundary; the countdown is decremented
    /// on the same call that polls, avoiding a 65-unit interval.
    fn charge(&mut self, work: usize) -> Result<(), ProjectionCertificateRejection> {
        if work == 0 {
            return Ok(());
        }
        let crosses_poll_boundary = self.until_poll == 0
            || work > usize::from(self.until_poll)
            || work > self.remaining_work;
        if crosses_poll_boundary {
            self.boundary()?;
        }
        self.remaining_work = self
            .remaining_work
            .checked_sub(work)
            .ok_or(ProjectionCertificateRejection::ResourceLimit)?;
        let remaining_until_poll = usize::from(self.until_poll).saturating_sub(work);
        self.until_poll = u8::try_from(remaining_until_poll).map_err(|_| {
            ProjectionCertificateRejection::InternalInvariant {
                kind: "projection stop countdown exceeded its u8 representation",
            }
        })?;
        Ok(())
    }

    fn step(&mut self) -> Result<(), ProjectionCertificateRejection> {
        self.charge(1)
    }
}

fn checked_data(
    terms: &TermStore,
    term: TermId,
) -> Result<&TermData, ProjectionCertificateRejection> {
    if term.index() >= terms.len() {
        return Err(ProjectionCertificateRejection::InvalidTermId { term });
    }
    Ok(terms.get(term))
}

fn checked_sort(terms: &TermStore, term: TermId) -> Result<&Sort, ProjectionCertificateRejection> {
    if term.index() >= terms.len() {
        return Err(ProjectionCertificateRejection::InvalidTermId { term });
    }
    Ok(terms.sort(term))
}

fn freeze_reachable_terms(
    terms: &TermStore,
    roots: &[TermId],
    stop: &mut ProjectionStopPoller<'_>,
) -> Result<Vec<FrozenTerm>, ProjectionCertificateRejection> {
    let mut seen = HashSet::new();
    stop.charge(roots.len())?;
    let mut stack = roots.to_vec();
    let mut frozen = Vec::new();
    while let Some(term) = stack.pop() {
        stop.step()?;
        if !seen.insert(term) {
            continue;
        }
        let data = checked_data(terms, term)?;
        match data {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::App(_, args) => {
                stop.charge(args.len())?;
                stack.extend(args.iter().copied());
            }
            TermData::Let(bindings, body) => {
                stop.charge(
                    bindings
                        .len()
                        .checked_add(1)
                        .ok_or(ProjectionCertificateRejection::ResourceLimit)?,
                )?;
                stack.extend(bindings.iter().map(|(_, value)| *value));
                stack.push(*body);
            }
            TermData::Not(child) => {
                stop.step()?;
                stack.push(*child);
            }
            TermData::Ite(condition, then_term, else_term) => {
                stop.charge(3)?;
                stack.extend([*condition, *then_term, *else_term]);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                let trigger_terms = triggers
                    .iter()
                    .try_fold(0usize, |count, trigger| count.checked_add(trigger.len()));
                let child_count = trigger_terms
                    .and_then(|count| count.checked_add(1))
                    .ok_or(ProjectionCertificateRejection::ResourceLimit)?;
                stop.charge(child_count)?;
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            _ => {
                return Err(ProjectionCertificateRejection::UnsupportedNode {
                    term,
                    kind: "unknown frozen term variant",
                });
            }
        }
        frozen.push(FrozenTerm {
            id: term,
            data: data.clone(),
            sort: checked_sort(terms, term)?.clone(),
        });
    }
    Ok(frozen)
}

fn is_supported_sort(sort: &Sort) -> bool {
    match sort {
        Sort::Bool => true,
        Sort::BitVec(width) => width.width > 0,
        _ => false,
    }
}

fn require_supported_sort(
    term: Option<TermId>,
    sort: &Sort,
) -> Result<(), ProjectionCertificateRejection> {
    if is_supported_sort(sort) {
        Ok(())
    } else {
        Err(ProjectionCertificateRejection::UnsupportedSort {
            term,
            sort: Box::new(sort.clone()),
        })
    }
}

fn discover_binder_terms(
    terms: &TermStore,
    body: TermId,
    binder_decls: &[(String, Sort)],
    binder_names: &HashMap<&str, usize>,
    stop: &mut ProjectionStopPoller<'_>,
) -> Result<Vec<TermId>, ProjectionCertificateRejection> {
    stop.charge(binder_decls.len())?;
    let mut found = vec![None; binder_decls.len()];
    let mut seen = HashSet::new();
    let mut stack = vec![body];
    while let Some(term) = stack.pop() {
        stop.step()?;
        if !seen.insert(term) {
            continue;
        }
        let data = checked_data(terms, term)?;
        let sort = checked_sort(terms, term)?;
        require_supported_sort(Some(term), sort)?;
        match data {
            TermData::Const(_) => {}
            TermData::Var(name, _) => {
                if let Some(&index) = binder_names.get(name.as_str()) {
                    let declared = &binder_decls[index].1;
                    if sort != declared {
                        return Err(ProjectionCertificateRejection::BinderSortMismatch {
                            name: name.clone(),
                            declared: Box::new(declared.clone()),
                            found: Box::new(sort.clone()),
                        });
                    }
                    match found[index] {
                        None => found[index] = Some(term),
                        Some(previous) if previous == term => {}
                        Some(_) => {
                            return Err(ProjectionCertificateRejection::AmbiguousBinderIdentity {
                                name: name.clone(),
                            });
                        }
                    }
                }
            }
            TermData::App(_, args) => {
                stop.charge(args.len())?;
                stack.extend(args.iter().copied());
            }
            TermData::Not(child) => {
                stop.step()?;
                stack.push(*child);
            }
            TermData::Ite(condition, then_term, else_term) => {
                stop.charge(3)?;
                stack.extend([*condition, *then_term, *else_term]);
            }
            TermData::Let(_, _) => {
                return Err(ProjectionCertificateRejection::UnsupportedNode { term, kind: "let" });
            }
            TermData::Forall(_, _, _) => {
                return Err(ProjectionCertificateRejection::UnsupportedNode {
                    term,
                    kind: "nested forall",
                });
            }
            TermData::Exists(_, _, _) => {
                return Err(ProjectionCertificateRejection::UnsupportedNode {
                    term,
                    kind: "exists",
                });
            }
            _ => {
                return Err(ProjectionCertificateRejection::UnsupportedNode {
                    term,
                    kind: "unknown term variant",
                });
            }
        }
    }

    stop.charge(binder_decls.len())?;
    found
        .into_iter()
        .zip(binder_decls)
        .map(|(term, (name, _))| {
            term.ok_or_else(|| ProjectionCertificateRejection::MissingBinderOccurrence {
                name: name.clone(),
            })
        })
        .collect()
}

fn validate_candidates(
    candidate: &ProjectionImplicationCandidate,
    binder_count: usize,
    stop: &mut ProjectionStopPoller<'_>,
) -> Result<HashMap<Symbol, usize>, ProjectionCertificateRejection> {
    if candidate.definitions.is_empty() {
        return Err(ProjectionCertificateRejection::NoDefinitions);
    }
    let mut definitions = HashMap::new();
    for (index, definition) in candidate.definitions.iter().enumerate() {
        stop.step()?;
        if !matches!(&definition.symbol, Symbol::Named(name) if !name.is_empty() && !is_builtin_name(name))
        {
            return Err(
                ProjectionCertificateRejection::UnsupportedDefinitionSymbol {
                    symbol: definition.symbol.clone(),
                },
            );
        }
        if definitions
            .insert(definition.symbol.clone(), index)
            .is_some()
        {
            return Err(ProjectionCertificateRejection::DuplicateDefinition {
                symbol: definition.symbol.clone(),
            });
        }
        if definition.parameter_sorts.len() != binder_count {
            return Err(ProjectionCertificateRejection::DefinitionArityMismatch {
                symbol: definition.symbol.clone(),
                expected: binder_count,
                found: definition.parameter_sorts.len(),
            });
        }
        stop.charge(definition.parameter_sorts.len())?;
        for sort in &definition.parameter_sorts {
            require_supported_sort(None, sort)?;
        }
        require_supported_sort(None, &definition.result_sort)?;
        let Some(parameter_sort) = definition
            .parameter_sorts
            .get(definition.projected_parameter)
        else {
            return Err(ProjectionCertificateRejection::ProjectionOutOfRange {
                symbol: definition.symbol.clone(),
                projected_parameter: definition.projected_parameter,
                arity: definition.parameter_sorts.len(),
            });
        };
        if parameter_sort != &definition.result_sort {
            return Err(ProjectionCertificateRejection::ProjectionSortMismatch {
                symbol: definition.symbol.clone(),
                parameter_sort: Box::new(parameter_sort.clone()),
                result_sort: Box::new(definition.result_sort.clone()),
            });
        }
    }
    Ok(definitions)
}

struct BodyValidation<'a> {
    terms: &'a TermStore,
    binder_by_term: &'a HashMap<TermId, usize>,
    definitions: &'a HashMap<Symbol, usize>,
    candidates: &'a [ProjectionUfCandidate],
    seen: HashSet<TermId>,
    uses: Vec<usize>,
    permutations: Vec<Option<Vec<usize>>>,
}

impl<'a> BodyValidation<'a> {
    fn new(
        terms: &'a TermStore,
        binder_by_term: &'a HashMap<TermId, usize>,
        definitions: &'a HashMap<Symbol, usize>,
        candidates: &'a [ProjectionUfCandidate],
        stop: &mut ProjectionStopPoller<'_>,
    ) -> Result<Self, ProjectionCertificateRejection> {
        stop.charge(
            definitions
                .len()
                .checked_mul(2)
                .ok_or(ProjectionCertificateRejection::ResourceLimit)?,
        )?;
        Ok(Self {
            terms,
            binder_by_term,
            definitions,
            candidates,
            seen: HashSet::new(),
            uses: vec![0; definitions.len()],
            permutations: vec![None; definitions.len()],
        })
    }

    fn validate(
        &mut self,
        root: TermId,
        stop: &mut ProjectionStopPoller<'_>,
    ) -> Result<(), ProjectionCertificateRejection> {
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            stop.step()?;
            if !self.seen.insert(term) {
                continue;
            }
            let data = checked_data(self.terms, term)?;
            let sort = checked_sort(self.terms, term)?;
            require_supported_sort(Some(term), sort)?;
            match data {
                TermData::Const(constant) => validate_constant(term, constant, sort)?,
                TermData::Var(_, _) => {}
                TermData::App(symbol, args) => {
                    if let Some(&definition_index) = self.definitions.get(symbol) {
                        let work = args
                            .len()
                            .checked_mul(4)
                            .ok_or(ProjectionCertificateRejection::ResourceLimit)?;
                        stop.charge(work)?;
                        self.validate_selected_application(term, symbol, args, definition_index)?;
                    } else {
                        stop.charge(
                            args.len()
                                .checked_mul(2)
                                .ok_or(ProjectionCertificateRejection::ResourceLimit)?,
                        )?;
                        if !validate_builtin_application(self.terms, term, symbol, args)? {
                            return Err(ProjectionCertificateRejection::UnsupportedApplication {
                                term,
                                symbol: symbol.clone(),
                            });
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(child) => {
                    if sort != &Sort::Bool || checked_sort(self.terms, *child)? != &Sort::Bool {
                        return Err(ProjectionCertificateRejection::IllSortedTerm { term });
                    }
                    stop.step()?;
                    stack.push(*child);
                }
                TermData::Ite(condition, then_term, else_term) => {
                    if checked_sort(self.terms, *condition)? != &Sort::Bool
                        || checked_sort(self.terms, *then_term)? != sort
                        || checked_sort(self.terms, *else_term)? != sort
                    {
                        return Err(ProjectionCertificateRejection::IllSortedTerm { term });
                    }
                    stop.charge(3)?;
                    stack.extend([*condition, *then_term, *else_term]);
                }
                TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                    return Err(ProjectionCertificateRejection::UnsupportedNode {
                        term,
                        kind: "nested binder",
                    });
                }
                _ => {
                    return Err(ProjectionCertificateRejection::UnsupportedNode {
                        term,
                        kind: "unknown term variant",
                    });
                }
            }
        }
        Ok(())
    }

    fn validate_selected_application(
        &mut self,
        term: TermId,
        symbol: &Symbol,
        args: &[TermId],
        definition_index: usize,
    ) -> Result<(), ProjectionCertificateRejection> {
        let definition_count = self.definitions.len();
        if definition_index >= definition_count {
            return Err(ProjectionCertificateRejection::InternalInvariant {
                kind: "definition map index outside definition table",
            });
        }
        let definition = self.candidates.get(definition_index).ok_or(
            ProjectionCertificateRejection::InternalInvariant {
                kind: "definition map index outside candidate table",
            },
        )?;
        if args.len() != definition.parameter_sorts.len()
            || checked_sort(self.terms, term)? != &definition.result_sort
            || args
                .iter()
                .zip(&definition.parameter_sorts)
                .any(|(&arg, sort)| {
                    checked_sort(self.terms, arg).map_or(true, |found| found != sort)
                })
        {
            return Err(
                ProjectionCertificateRejection::ApplicationSignatureMismatch {
                    term,
                    symbol: symbol.clone(),
                },
            );
        }
        let mut permutation = Vec::with_capacity(args.len());
        let mut occupied = vec![false; self.binder_by_term.len()];
        for &arg in args {
            let Some(&binder_index) = self.binder_by_term.get(&arg) else {
                return Err(
                    ProjectionCertificateRejection::ApplicationNotBinderPermutation {
                        term,
                        symbol: symbol.clone(),
                    },
                );
            };
            if binder_index >= occupied.len() || occupied[binder_index] {
                return Err(
                    ProjectionCertificateRejection::ApplicationNotBinderPermutation {
                        term,
                        symbol: symbol.clone(),
                    },
                );
            }
            occupied[binder_index] = true;
            permutation.push(binder_index);
        }
        if args.len() != occupied.len() || occupied.iter().any(|used| !used) {
            return Err(
                ProjectionCertificateRejection::ApplicationNotBinderPermutation {
                    term,
                    symbol: symbol.clone(),
                },
            );
        }
        match &self.permutations[definition_index] {
            Some(previous) if previous != &permutation => {
                return Err(
                    ProjectionCertificateRejection::InconsistentApplicationPermutation {
                        term,
                        symbol: symbol.clone(),
                    },
                );
            }
            None => self.permutations[definition_index] = Some(permutation),
            Some(_) => {}
        }
        self.uses[definition_index] += 1;
        Ok(())
    }

    fn finish(
        self,
        candidate: &ProjectionImplicationCandidate,
        stop: &mut ProjectionStopPoller<'_>,
    ) -> Result<Vec<CheckedProjectionUf>, ProjectionCertificateRejection> {
        stop.charge(candidate.definitions.len())?;
        let mut checked = Vec::with_capacity(candidate.definitions.len());
        for (index, definition) in candidate.definitions.iter().enumerate() {
            stop.step()?;
            if self.uses[index] == 0 {
                return Err(ProjectionCertificateRejection::UnusedDefinition {
                    symbol: definition.symbol.clone(),
                });
            }
            let permutation = self.permutations[index].as_ref().ok_or_else(|| {
                ProjectionCertificateRejection::UnusedDefinition {
                    symbol: definition.symbol.clone(),
                }
            })?;
            stop.charge(
                definition
                    .parameter_sorts
                    .len()
                    .checked_add(permutation.len())
                    .ok_or(ProjectionCertificateRejection::ResourceLimit)?,
            )?;
            let permutation = permutation.clone();
            checked.push(CheckedProjectionUf {
                symbol: definition.symbol.clone(),
                parameter_sorts: definition.parameter_sorts.clone(),
                result_sort: definition.result_sort.clone(),
                projected_parameter: definition.projected_parameter,
                binder_permutation: permutation,
            });
        }
        Ok(checked)
    }
}

fn validate_constant(
    term: TermId,
    constant: &Constant,
    sort: &Sort,
) -> Result<(), ProjectionCertificateRejection> {
    let valid = match (constant, sort) {
        (Constant::Bool(_), Sort::Bool) => true,
        (Constant::BitVec { value, width }, Sort::BitVec(sort_width)) => {
            *width == sort_width.width
                && *width > 0
                && value.sign() != Sign::Minus
                // For a non-negative integer, `value < 2^width` exactly when
                // its significant-bit count is at most `width`. Unlike
                // constructing `2^width`, this stays O(size(value)) even for a
                // hostile declaration such as `(_ BitVec 4294967295)`.
                && value.bits() <= u64::from(*width)
        }
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(ProjectionCertificateRejection::IllSortedTerm { term })
    }
}

fn is_builtin_name(name: &str) -> bool {
    matches!(
        name,
        "and"
            | "or"
            | "not"
            | "=>"
            | "implies"
            | "xor"
            | "="
            | "distinct"
            | "ite"
            | "concat"
            | "bvnot"
            | "bvneg"
            | "bvand"
            | "bvor"
            | "bvxor"
            | "bvnand"
            | "bvnor"
            | "bvxnor"
            | "bvadd"
            | "bvsub"
            | "bvmul"
            | "bvudiv"
            | "bvurem"
            | "bvsdiv"
            | "bvsrem"
            | "bvsmod"
            | "bvshl"
            | "bvlshr"
            | "bvashr"
            | "bvcomp"
            | "bvnego"
            | "bvsaddo"
            | "bvuaddo"
            | "bvsdivo"
            | "bvsmulo"
            | "bvumulo"
            | "bvssubo"
            | "bvusubo"
            | "bvredand"
            | "bvredor"
            | "bv2nat"
            | "bv2int"
            | "int2bv"
            | "ubv_to_int"
            | "sbv_to_int"
            | "bvult"
            | "bvule"
            | "bvugt"
            | "bvuge"
            | "bvslt"
            | "bvsle"
            | "bvsgt"
            | "bvsge"
            | "extract"
            | "zero_extend"
            | "sign_extend"
            | "repeat"
            | "rotate_left"
            | "rotate_right"
    )
}

fn validate_builtin_application(
    terms: &TermStore,
    term: TermId,
    symbol: &Symbol,
    args: &[TermId],
) -> Result<bool, ProjectionCertificateRejection> {
    let result_sort = checked_sort(terms, term)?;
    let arg_sorts: Vec<&Sort> = args
        .iter()
        .map(|&arg| checked_sort(terms, arg))
        .collect::<Result<_, _>>()?;
    let well_sorted = match symbol {
        Symbol::Named(name) => match name.as_str() {
            "and" | "or" => {
                args.len() >= 2
                    && result_sort == &Sort::Bool
                    && arg_sorts.iter().all(|sort| **sort == Sort::Bool)
            }
            "not" => args.len() == 1 && result_sort == &Sort::Bool && arg_sorts[0] == &Sort::Bool,
            "=>" | "implies" | "xor" => {
                args.len() == 2
                    && result_sort == &Sort::Bool
                    && arg_sorts.iter().all(|sort| **sort == Sort::Bool)
            }
            "=" | "distinct" => {
                args.len() == 2 && result_sort == &Sort::Bool && arg_sorts[0] == arg_sorts[1]
            }
            "concat" => match arg_sorts.as_slice() {
                [Sort::BitVec(left), Sort::BitVec(right)] => {
                    matches!(result_sort, Sort::BitVec(result) if left.width.checked_add(right.width) == Some(result.width))
                }
                _ => false,
            },
            "bvnot" | "bvneg" => same_width_bv(&arg_sorts, result_sort, 1),
            "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor" | "bvxnor" | "bvadd" | "bvsub"
            | "bvmul" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod" | "bvshl"
            | "bvlshr" | "bvashr" => same_width_bv(&arg_sorts, result_sort, 2),
            "bvcomp" => {
                same_width_bv_args(&arg_sorts, 2)
                    && matches!(result_sort, Sort::BitVec(width) if width.width == 1)
            }
            "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
                same_width_bv_args(&arg_sorts, 2) && result_sort == &Sort::Bool
            }
            _ => return Ok(false),
        },
        Symbol::Indexed(name, indices) => match name.as_str() {
            "extract" => match (indices.as_slice(), arg_sorts.as_slice(), result_sort) {
                ([high, low], [Sort::BitVec(input)], Sort::BitVec(output)) => {
                    low <= high
                        && *high < input.width
                        && high
                            .checked_sub(*low)
                            .and_then(|width| width.checked_add(1))
                            == Some(output.width)
                }
                _ => false,
            },
            "zero_extend" | "sign_extend" => {
                match (indices.as_slice(), arg_sorts.as_slice(), result_sort) {
                    ([amount], [Sort::BitVec(input)], Sort::BitVec(output)) => {
                        input.width.checked_add(*amount) == Some(output.width)
                    }
                    _ => false,
                }
            }
            "repeat" => match (indices.as_slice(), arg_sorts.as_slice(), result_sort) {
                ([times], [Sort::BitVec(input)], Sort::BitVec(output)) => {
                    *times > 0 && input.width.checked_mul(*times) == Some(output.width)
                }
                _ => false,
            },
            "rotate_left" | "rotate_right" => {
                indices.len() == 1 && same_width_bv(&arg_sorts, result_sort, 1)
            }
            _ => return Ok(false),
        },
        _ => return Ok(false),
    };
    if well_sorted {
        Ok(true)
    } else {
        Err(ProjectionCertificateRejection::IllSortedTerm { term })
    }
}

fn same_width_bv(args: &[&Sort], result: &Sort, arity: usize) -> bool {
    let Sort::BitVec(result_width) = result else {
        return false;
    };
    args.len() == arity
        && args
            .iter()
            .all(|sort| matches!(sort, Sort::BitVec(width) if width.width == result_width.width))
}

fn same_width_bv_args(args: &[&Sort], arity: usize) -> bool {
    let Some(Sort::BitVec(first)) = args.first().copied() else {
        return false;
    };
    args.len() == arity
        && args
            .iter()
            .all(|sort| matches!(sort, Sort::BitVec(width) if width.width == first.width))
}

struct ImplicationShape {
    premise_hypotheses: Vec<Hypothesis>,
    conclusion: TermId,
}

#[derive(Clone, Copy)]
struct Hypothesis {
    term: TermId,
    value: bool,
}

fn extract_implication(
    terms: &TermStore,
    body: TermId,
    candidate_conclusion: TermId,
    stop: &mut ProjectionStopPoller<'_>,
) -> Result<ImplicationShape, ProjectionCertificateRejection> {
    stop.step()?;
    match checked_data(terms, body)? {
        TermData::App(Symbol::Named(name), args)
            if matches!(name.as_str(), "=>" | "implies") && args.len() == 2 =>
        {
            if args[1] != candidate_conclusion {
                return Err(
                    ProjectionCertificateRejection::ConclusionNotTopLevelOperand {
                        conclusion: candidate_conclusion,
                    },
                );
            }
            let mut premise_hypotheses = Vec::new();
            flatten_conjunction(terms, args[0], &mut premise_hypotheses, stop)?;
            Ok(ImplicationShape {
                premise_hypotheses,
                conclusion: args[1],
            })
        }
        TermData::App(Symbol::Named(name), args) if name == "or" && args.len() >= 2 => {
            // The live frontend represents `(=> (and p...) c)` as a sorted,
            // flattened OR clause: `mk_not` applies De Morgan and `mk_or`
            // flattens. The candidate chooses one consequent, but that choice
            // carries no authority: the checker requires exact top-level
            // membership, then treats every other disjunct `d` as hypothesis
            // `not d`. For ANY selected operand this reconstructed implication
            // is exactly equivalent to the complete clause.
            if args
                .iter()
                .filter(|&&arg| arg == candidate_conclusion)
                .count()
                != 1
            {
                return Err(
                    ProjectionCertificateRejection::ConclusionNotTopLevelOperand {
                        conclusion: candidate_conclusion,
                    },
                );
            }
            let mut premise_hypotheses = Vec::with_capacity(args.len() - 1);
            for &arg in args {
                stop.step()?;
                if arg == candidate_conclusion {
                    continue;
                }
                if let TermData::Not(inner) = checked_data(terms, arg)? {
                    premise_hypotheses.push(Hypothesis {
                        term: *inner,
                        value: true,
                    });
                } else {
                    premise_hypotheses.push(Hypothesis {
                        term: arg,
                        value: false,
                    });
                }
            }
            Ok(ImplicationShape {
                premise_hypotheses,
                conclusion: candidate_conclusion,
            })
        }
        _ => Err(ProjectionCertificateRejection::BodyNotImplication),
    }
}

fn flatten_conjunction(
    terms: &TermStore,
    root: TermId,
    output: &mut Vec<Hypothesis>,
    stop: &mut ProjectionStopPoller<'_>,
) -> Result<(), ProjectionCertificateRejection> {
    let mut seen = HashSet::new();
    let mut stack = vec![(root, 0_usize)];
    let mut work = 0_usize;
    while let Some((term, depth)) = stack.pop() {
        stop.step()?;
        work = work
            .checked_add(1)
            .ok_or(ProjectionCertificateRejection::ResourceLimit)?;
        if work > MAX_PROJECTION_STEPS || depth > MAX_PROJECTION_DEPTH {
            return Err(ProjectionCertificateRejection::ResourceLimit);
        }
        if !seen.insert(term) {
            continue;
        }
        match checked_data(terms, term)? {
            TermData::App(Symbol::Named(name), args) if name == "and" => {
                let child_depth = depth
                    .checked_add(1)
                    .ok_or(ProjectionCertificateRejection::ResourceLimit)?;
                stack.extend(args.iter().rev().map(|&arg| (arg, child_depth)));
            }
            TermData::Const(Constant::Bool(true)) => {}
            _ => output.push(Hypothesis { term, value: true }),
        }
    }
    Ok(())
}

fn projected_argument<'a>(
    terms: &'a TermStore,
    term: TermId,
    definitions: &HashMap<Symbol, usize>,
    candidates: &'a [ProjectionUfCandidate],
) -> Result<Option<TermId>, ProjectionCertificateRejection> {
    let TermData::App(symbol, args) = checked_data(terms, term)? else {
        return Ok(None);
    };
    let Some(&definition_index) = definitions.get(symbol) else {
        return Ok(None);
    };
    let definition = candidates.get(definition_index).ok_or(
        ProjectionCertificateRejection::InternalInvariant {
            kind: "definition map index outside projection candidates",
        },
    )?;
    let argument = args.get(definition.projected_parameter).copied().ok_or(
        ProjectionCertificateRejection::InternalInvariant {
            kind: "projected parameter outside validated application arguments",
        },
    )?;
    Ok(Some(argument))
}

fn effective_binder(
    terms: &TermStore,
    term: TermId,
    binder_by_term: &HashMap<TermId, usize>,
    definitions: &HashMap<Symbol, usize>,
    candidates: &[ProjectionUfCandidate],
) -> Result<Option<TermId>, ProjectionCertificateRejection> {
    if binder_by_term.contains_key(&term) {
        return Ok(Some(term));
    }
    if let Some(argument) = projected_argument(terms, term, definitions, candidates)? {
        if binder_by_term.contains_key(&argument) {
            return Ok(Some(argument));
        }
    }
    Ok(None)
}

fn build_premise_environment(
    terms: &TermStore,
    hypotheses: &[Hypothesis],
    binder_by_term: &HashMap<TermId, usize>,
    definitions: &HashMap<Symbol, usize>,
    candidates: &[ProjectionUfCandidate],
    strategy: PremiseSelectionStrategy,
    stop: &mut ProjectionStopPoller<'_>,
) -> Result<PremiseEnvironment, ProjectionCertificateRejection> {
    let mut env = PremiseEnvironment::default();
    let mut work = 0_usize;
    for offset in 0..hypotheses.len() {
        stop.step()?;
        work = work
            .checked_add(1)
            .ok_or(ProjectionCertificateRejection::ResourceLimit)?;
        if work > MAX_PROJECTION_STEPS {
            return Err(ProjectionCertificateRejection::ResourceLimit);
        }
        let index = if strategy.reverse_hypotheses {
            hypotheses.len().checked_sub(offset + 1).ok_or(
                ProjectionCertificateRejection::InternalInvariant {
                    kind: "reverse hypothesis index outside input",
                },
            )?
        } else {
            offset
        };
        let hypothesis = hypotheses[index];
        let mut orientations = premise_orientations(
            terms,
            hypothesis.term,
            hypothesis.value,
            binder_by_term,
            definitions,
            candidates,
            &mut env.conditionals,
            &mut work,
            0,
            stop,
        )?;

        // If a subset Q of the premise conjunction P suffices to normalize the
        // conclusion, then Q => C is stronger than P => C.  It is therefore
        // sound to drop non-orientable hypotheses and later conflicting
        // definitions.  Equality is symmetric, so when both sides are binders
        // prefer the first side that has not already been defined.  This
        // recovers source-definition chains after equality canonicalization
        // has reordered their operands, without trusting source order or
        // requiring every premise conjunct to participate in the certificate.
        if strategy.reverse_orientations {
            orientations.reverse();
        }
        if let Some((binder, replacement)) = orientations
            .into_iter()
            .find(|(binder, _)| !env.definitions.contains_key(binder))
        {
            env.definitions.insert(binder, replacement);
        }
    }
    Ok(env)
}

const MAX_CONDITIONAL_PREMISE_DEPTH: usize = 64;

#[allow(clippy::too_many_arguments)]
fn premise_orientations(
    terms: &TermStore,
    mut term: TermId,
    mut value: bool,
    binder_by_term: &HashMap<TermId, usize>,
    definitions: &HashMap<Symbol, usize>,
    candidates: &[ProjectionUfCandidate],
    conditionals: &mut Vec<ConditionalPremiseValue>,
    work: &mut usize,
    depth: usize,
    stop: &mut ProjectionStopPoller<'_>,
) -> Result<Vec<(TermId, PremiseValue)>, ProjectionCertificateRejection> {
    stop.step()?;
    *work = work
        .checked_add(1)
        .ok_or(ProjectionCertificateRejection::ResourceLimit)?;
    if *work > MAX_PROJECTION_STEPS || depth > MAX_CONDITIONAL_PREMISE_DEPTH {
        return Err(ProjectionCertificateRejection::ResourceLimit);
    }

    let mut negation_depth = 0_usize;
    while let TermData::Not(inner) = checked_data(terms, term)? {
        stop.step()?;
        *work = work
            .checked_add(1)
            .ok_or(ProjectionCertificateRejection::ResourceLimit)?;
        if *work > MAX_PROJECTION_STEPS {
            return Err(ProjectionCertificateRejection::ResourceLimit);
        }
        negation_depth += 1;
        if negation_depth > MAX_PROJECTION_DEPTH {
            return Err(ProjectionCertificateRejection::ResourceLimit);
        }
        term = *inner;
        value = !value;
    }

    match checked_data(terms, term)? {
        TermData::App(Symbol::Named(name), args)
            if matches!(name.as_str(), "=" | "distinct" | "xor") && args.len() == 2 =>
        {
            // A positive equality and a negated binary `distinct` are the
            // same usable premise fact.  For Boolean operands, a negated
            // binary XOR is also exactly equality.  The live frontend can
            // expose either form while flattening a negated conjunction.
            let is_negated_bool_xor = name == "xor"
                && !value
                && checked_sort(terms, args[0])? == &Sort::Bool
                && checked_sort(terms, args[1])? == &Sort::Bool;
            let is_equality =
                (name == "=" && value) || (name == "distinct" && !value) || is_negated_bool_xor;
            if !is_equality {
                return Ok(Vec::new());
            }
            let left = effective_binder(terms, args[0], binder_by_term, definitions, candidates)?;
            let right = effective_binder(terms, args[1], binder_by_term, definitions, candidates)?;
            let mut orientations = Vec::with_capacity(2);
            if let Some(binder) = left {
                orientations.push((binder, PremiseValue::Term(args[1])));
            }
            if let Some(binder) = right {
                if orientations
                    .first()
                    .is_none_or(|(left_binder, _)| *left_binder != binder)
                {
                    orientations.push((binder, PremiseValue::Term(args[0])));
                }
            }
            Ok(orientations)
        }
        TermData::Ite(condition, then_term, else_term)
            if checked_sort(terms, term)? == &Sort::Bool
                && checked_sort(terms, *condition)? == &Sort::Bool =>
        {
            let then_orientations = premise_orientations(
                terms,
                *then_term,
                value,
                binder_by_term,
                definitions,
                candidates,
                conditionals,
                work,
                depth + 1,
                stop,
            )?;
            let else_orientations = premise_orientations(
                terms,
                *else_term,
                value,
                binder_by_term,
                definitions,
                candidates,
                conditionals,
                work,
                depth + 1,
                stop,
            )?;
            let mut orientations = Vec::with_capacity(2);
            for (then_binder, then_value) in then_orientations {
                for &(else_binder, else_value) in &else_orientations {
                    stop.step()?;
                    *work = work
                        .checked_add(1)
                        .ok_or(ProjectionCertificateRejection::ResourceLimit)?;
                    if *work > MAX_PROJECTION_STEPS {
                        return Err(ProjectionCertificateRejection::ResourceLimit);
                    }
                    if then_binder != else_binder
                        || orientations
                            .iter()
                            .any(|(binder, _)| *binder == then_binder)
                    {
                        continue;
                    }
                    let binder_sort = checked_sort(terms, then_binder)?;
                    if premise_value_sort(terms, then_value, conditionals)? != *binder_sort
                        || premise_value_sort(terms, else_value, conditionals)? != *binder_sort
                    {
                        continue;
                    }
                    if conditionals.len() >= MAX_PROJECTION_STEPS {
                        return Err(ProjectionCertificateRejection::ResourceLimit);
                    }
                    let conditional = conditionals.len();
                    conditionals.push(ConditionalPremiseValue {
                        condition: *condition,
                        then_value,
                        else_value,
                        sort: binder_sort.clone(),
                    });
                    orientations.push((then_binder, PremiseValue::Conditional(conditional)));
                }
            }
            Ok(orientations)
        }
        _ => Ok(
            effective_binder(terms, term, binder_by_term, definitions, candidates)?
                .filter(|binder| checked_sort(terms, *binder).is_ok_and(|sort| sort == &Sort::Bool))
                .map(|binder| (binder, PremiseValue::Bool(value)))
                .into_iter()
                .collect(),
        ),
    }
}

fn premise_value_sort(
    terms: &TermStore,
    value: PremiseValue,
    conditionals: &[ConditionalPremiseValue],
) -> Result<Sort, ProjectionCertificateRejection> {
    match value {
        PremiseValue::Term(term) => Ok(checked_sort(terms, term)?.clone()),
        PremiseValue::Bool(_) => Ok(Sort::Bool),
        PremiseValue::Conditional(conditional) => conditionals
            .get(conditional)
            .map(|value| value.sort.clone())
            .ok_or(ProjectionCertificateRejection::InternalInvariant {
                kind: "conditional premise index outside arena",
            }),
    }
}

#[derive(Clone, Copy)]
struct PremiseSelectionStrategy {
    reverse_hypotheses: bool,
    reverse_orientations: bool,
}

// Fixed four-way search: total work is at most four times the per-checker
// premise/environment/normalizer bounds, independent of input choices.
const PREMISE_SELECTION_STRATEGIES: [PremiseSelectionStrategy; 4] = [
    PremiseSelectionStrategy {
        reverse_hypotheses: false,
        reverse_orientations: false,
    },
    PremiseSelectionStrategy {
        reverse_hypotheses: false,
        reverse_orientations: true,
    },
    PremiseSelectionStrategy {
        reverse_hypotheses: true,
        reverse_orientations: false,
    },
    PremiseSelectionStrategy {
        reverse_hypotheses: true,
        reverse_orientations: true,
    },
];

#[derive(Clone, Copy)]
enum PremiseValue {
    Term(TermId),
    Bool(bool),
    Conditional(usize),
}

#[derive(Default)]
struct PremiseEnvironment {
    definitions: HashMap<TermId, PremiseValue>,
    conditionals: Vec<ConditionalPremiseValue>,
}

struct ConditionalPremiseValue {
    condition: TermId,
    then_value: PremiseValue,
    else_value: PremiseValue,
    sort: Sort,
}

fn reject_environment_cycles(
    terms: &TermStore,
    env: &PremiseEnvironment,
    binder_by_term: &HashMap<TermId, usize>,
    definitions: &HashMap<Symbol, usize>,
    candidates: &[ProjectionUfCandidate],
    stop: &mut ProjectionStopPoller<'_>,
) -> Result<(), ProjectionCertificateRejection> {
    let mut dependencies = HashMap::<TermId, Vec<TermId>>::new();
    let mut work = 0_usize;
    for (&binder, &replacement) in &env.definitions {
        stop.step()?;
        let mut found = HashSet::new();
        collect_premise_value_binders(
            terms,
            replacement,
            env,
            binder_by_term,
            definitions,
            candidates,
            &mut found,
            &mut work,
            stop,
        )?;
        dependencies.insert(
            binder,
            found
                .into_iter()
                .filter(|dependency| env.definitions.contains_key(dependency))
                .collect(),
        );
    }
    reject_dependency_cycles(&dependencies, &mut work, stop)
}

#[allow(clippy::too_many_arguments)]
fn collect_premise_value_binders(
    terms: &TermStore,
    root: PremiseValue,
    env: &PremiseEnvironment,
    binder_by_term: &HashMap<TermId, usize>,
    definitions: &HashMap<Symbol, usize>,
    candidates: &[ProjectionUfCandidate],
    output: &mut HashSet<TermId>,
    work: &mut usize,
    stop: &mut ProjectionStopPoller<'_>,
) -> Result<(), ProjectionCertificateRejection> {
    let mut stack = vec![root];
    while let Some(value) = stack.pop() {
        stop.step()?;
        *work = work
            .checked_add(1)
            .ok_or(ProjectionCertificateRejection::ResourceLimit)?;
        if *work > MAX_PROJECTION_STEPS {
            return Err(ProjectionCertificateRejection::ResourceLimit);
        }
        match value {
            PremiseValue::Term(term) => collect_effective_binders(
                terms,
                term,
                binder_by_term,
                definitions,
                candidates,
                output,
                work,
                stop,
            )?,
            PremiseValue::Bool(_) => {}
            PremiseValue::Conditional(conditional) => {
                let conditional = env.conditionals.get(conditional).ok_or(
                    ProjectionCertificateRejection::InternalInvariant {
                        kind: "dependency conditional index outside arena",
                    },
                )?;
                collect_effective_binders(
                    terms,
                    conditional.condition,
                    binder_by_term,
                    definitions,
                    candidates,
                    output,
                    work,
                    stop,
                )?;
                stack.push(conditional.then_value);
                stack.push(conditional.else_value);
            }
        }
    }
    Ok(())
}

fn collect_effective_binders(
    terms: &TermStore,
    root: TermId,
    binder_by_term: &HashMap<TermId, usize>,
    definitions: &HashMap<Symbol, usize>,
    candidates: &[ProjectionUfCandidate],
    output: &mut HashSet<TermId>,
    work: &mut usize,
    stop: &mut ProjectionStopPoller<'_>,
) -> Result<(), ProjectionCertificateRejection> {
    let mut seen = HashSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        stop.step()?;
        *work = work
            .checked_add(1)
            .ok_or(ProjectionCertificateRejection::ResourceLimit)?;
        if *work > MAX_PROJECTION_STEPS {
            return Err(ProjectionCertificateRejection::ResourceLimit);
        }
        if !seen.insert(term) {
            continue;
        }
        if binder_by_term.contains_key(&term) {
            output.insert(term);
            continue;
        }
        if let Some(argument) = projected_argument(terms, term, definitions, candidates)? {
            stack.push(argument);
            continue;
        }
        match checked_data(terms, term)? {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(child) => stack.push(*child),
            TermData::Ite(condition, then_term, else_term) => {
                stack.extend([*condition, *then_term, *else_term]);
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            _ => {
                return Err(ProjectionCertificateRejection::UnsupportedNode {
                    term,
                    kind: "binder in dependency term",
                });
            }
        }
    }
    Ok(())
}

fn reject_dependency_cycles(
    dependencies: &HashMap<TermId, Vec<TermId>>,
    work: &mut usize,
    stop: &mut ProjectionStopPoller<'_>,
) -> Result<(), ProjectionCertificateRejection> {
    let mut state = HashMap::<TermId, u8>::new();
    for &root in dependencies.keys() {
        stop.step()?;
        if state.get(&root) == Some(&2) {
            continue;
        }
        let mut stack = vec![(root, false)];
        while let Some((binder, leaving)) = stack.pop() {
            stop.step()?;
            *work = work
                .checked_add(1)
                .ok_or(ProjectionCertificateRejection::ResourceLimit)?;
            if *work > MAX_PROJECTION_STEPS {
                return Err(ProjectionCertificateRejection::ResourceLimit);
            }
            if leaving {
                state.insert(binder, 2);
                continue;
            }
            match state.get(&binder) {
                Some(1) => {
                    return Err(ProjectionCertificateRejection::CyclicPremiseDefinitions);
                }
                Some(2) => continue,
                _ => {}
            }
            state.insert(binder, 1);
            stack.push((binder, true));
            if let Some(children) = dependencies.get(&binder) {
                for &child in children {
                    if state.get(&child) == Some(&1) {
                        return Err(ProjectionCertificateRejection::CyclicPremiseDefinitions);
                    }
                    if state.get(&child) != Some(&2) {
                        stack.push((child, false));
                    }
                }
            }
        }
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct NormNode {
    sort: Sort,
    kind: NormKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum NormKind {
    Const(Constant),
    Var(TermId),
    App(Symbol, Vec<NormId>),
    Not(NormId),
    And(Vec<NormId>),
    Or(Vec<NormId>),
    Ite(NormId, NormId, NormId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct NormId(usize);

enum NormalizeFrame {
    Enter {
        term: TermId,
        depth: usize,
    },
    Forward {
        term: TermId,
    },
    PremiseEnter {
        value: PremiseValue,
        depth: usize,
    },
    PremiseIteCondition {
        sort: Sort,
        then_value: PremiseValue,
        else_value: PremiseValue,
        depth: usize,
    },
    PremiseIteThen {
        sort: Sort,
        condition: NormId,
        else_value: PremiseValue,
        depth: usize,
    },
    PremiseIteElse {
        sort: Sort,
        condition: NormId,
        then_value: NormId,
    },
    Not {
        term: TermId,
    },
    IteCondition {
        term: TermId,
        sort: Sort,
        then_term: TermId,
        else_term: TermId,
        depth: usize,
    },
    IteThen {
        term: TermId,
        sort: Sort,
        condition: NormId,
        else_term: TermId,
        depth: usize,
    },
    IteElse {
        term: TermId,
        sort: Sort,
        condition: NormId,
        then_term: NormId,
    },
    Application {
        term: TermId,
        sort: Sort,
        symbol: Symbol,
        arity: usize,
    },
}

struct Normalizer<'a> {
    terms: &'a TermStore,
    binder_by_term: &'a HashMap<TermId, usize>,
    definitions: &'a HashMap<Symbol, usize>,
    candidates: &'a [ProjectionUfCandidate],
    env: &'a PremiseEnvironment,
    arena: Vec<NormNode>,
    interned: HashMap<NormNode, NormId>,
    memo: HashMap<TermId, NormId>,
    active: HashSet<TermId>,
    steps: usize,
}

fn next_projection_depth(depth: usize) -> Result<usize, ProjectionCertificateRejection> {
    depth
        .checked_add(1)
        .ok_or(ProjectionCertificateRejection::ResourceLimit)
}

fn pop_normalized(results: &mut Vec<NormId>) -> Result<NormId, ProjectionCertificateRejection> {
    results
        .pop()
        .ok_or(ProjectionCertificateRejection::InternalInvariant {
            kind: "normalizer result stack underflow",
        })
}

impl<'a> Normalizer<'a> {
    fn new(
        terms: &'a TermStore,
        binder_by_term: &'a HashMap<TermId, usize>,
        definitions: &'a HashMap<Symbol, usize>,
        candidates: &'a [ProjectionUfCandidate],
        env: &'a PremiseEnvironment,
    ) -> Self {
        Self {
            terms,
            binder_by_term,
            definitions,
            candidates,
            env,
            arena: Vec::new(),
            interned: HashMap::new(),
            memo: HashMap::new(),
            active: HashSet::new(),
            steps: 0,
        }
    }

    fn normalize(
        &mut self,
        term: TermId,
        depth: usize,
        stop: &mut ProjectionStopPoller<'_>,
    ) -> Result<NormId, ProjectionCertificateRejection> {
        let mut frames = vec![NormalizeFrame::Enter { term, depth }];
        let mut results = Vec::new();

        while let Some(frame) = frames.pop() {
            stop.step()?;
            match frame {
                NormalizeFrame::Enter { term, depth } => {
                    if depth > MAX_PROJECTION_DEPTH || self.steps >= MAX_PROJECTION_STEPS {
                        return Err(ProjectionCertificateRejection::ResourceLimit);
                    }
                    self.steps += 1;
                    if let Some(&normalized) = self.memo.get(&term) {
                        results.push(normalized);
                        continue;
                    }
                    if !self.active.insert(term) {
                        return Err(ProjectionCertificateRejection::CyclicPremiseDefinitions);
                    }

                    if self.binder_by_term.contains_key(&term) {
                        match self.env.definitions.get(&term).copied() {
                            Some(PremiseValue::Term(replacement)) => {
                                frames.push(NormalizeFrame::Forward { term });
                                frames.push(NormalizeFrame::Enter {
                                    term: replacement,
                                    depth: next_projection_depth(depth)?,
                                });
                            }
                            Some(PremiseValue::Bool(value)) => {
                                let normalized = self.bool_constant(value);
                                self.finish_term(term, normalized, &mut results);
                            }
                            Some(value @ PremiseValue::Conditional(_)) => {
                                frames.push(NormalizeFrame::Forward { term });
                                frames.push(NormalizeFrame::PremiseEnter {
                                    value,
                                    depth: next_projection_depth(depth)?,
                                });
                            }
                            None => {
                                let normalized = self.intern(NormNode {
                                    sort: checked_sort(self.terms, term)?.clone(),
                                    kind: NormKind::Var(term),
                                });
                                self.finish_term(term, normalized, &mut results);
                            }
                        }
                        continue;
                    }

                    if let Some(argument) =
                        projected_argument(self.terms, term, self.definitions, self.candidates)?
                    {
                        frames.push(NormalizeFrame::Forward { term });
                        frames.push(NormalizeFrame::Enter {
                            term: argument,
                            depth: next_projection_depth(depth)?,
                        });
                        continue;
                    }

                    let sort = checked_sort(self.terms, term)?.clone();
                    match checked_data(self.terms, term)?.clone() {
                        TermData::Const(constant) => {
                            let normalized = self.intern(NormNode {
                                sort,
                                kind: NormKind::Const(constant),
                            });
                            self.finish_term(term, normalized, &mut results);
                        }
                        TermData::Var(_, _) => {
                            let normalized = self.intern(NormNode {
                                sort,
                                kind: NormKind::Var(term),
                            });
                            self.finish_term(term, normalized, &mut results);
                        }
                        TermData::Not(child) => {
                            frames.push(NormalizeFrame::Not { term });
                            frames.push(NormalizeFrame::Enter {
                                term: child,
                                depth: next_projection_depth(depth)?,
                            });
                        }
                        TermData::Ite(condition, then_term, else_term) => {
                            frames.push(NormalizeFrame::IteCondition {
                                term,
                                sort,
                                then_term,
                                else_term,
                                depth,
                            });
                            frames.push(NormalizeFrame::Enter {
                                term: condition,
                                depth: next_projection_depth(depth)?,
                            });
                        }
                        TermData::App(symbol, args) => {
                            if args.len() > MAX_PROJECTION_STEPS {
                                return Err(ProjectionCertificateRejection::ResourceLimit);
                            }
                            let arity = args.len();
                            let child_depth = next_projection_depth(depth)?;
                            frames.push(NormalizeFrame::Application {
                                term,
                                sort,
                                symbol,
                                arity,
                            });
                            frames.extend(args.into_iter().rev().map(|term| {
                                NormalizeFrame::Enter {
                                    term,
                                    depth: child_depth,
                                }
                            }));
                        }
                        _ => {
                            return Err(ProjectionCertificateRejection::UnsupportedNode {
                                term,
                                kind: "normalizer binder",
                            });
                        }
                    }
                }
                NormalizeFrame::Forward { term } => {
                    let normalized = pop_normalized(&mut results)?;
                    self.finish_term(term, normalized, &mut results);
                }
                NormalizeFrame::PremiseEnter { value, depth } => {
                    if depth > MAX_PROJECTION_DEPTH || self.steps >= MAX_PROJECTION_STEPS {
                        return Err(ProjectionCertificateRejection::ResourceLimit);
                    }
                    self.steps += 1;
                    match value {
                        PremiseValue::Term(term) => {
                            frames.push(NormalizeFrame::Enter { term, depth });
                        }
                        PremiseValue::Bool(value) => results.push(self.bool_constant(value)),
                        PremiseValue::Conditional(conditional) => {
                            let conditional = self.env.conditionals.get(conditional).ok_or(
                                ProjectionCertificateRejection::InternalInvariant {
                                    kind: "normalizer conditional index outside arena",
                                },
                            )?;
                            frames.push(NormalizeFrame::PremiseIteCondition {
                                sort: conditional.sort.clone(),
                                then_value: conditional.then_value,
                                else_value: conditional.else_value,
                                depth,
                            });
                            frames.push(NormalizeFrame::Enter {
                                term: conditional.condition,
                                depth: next_projection_depth(depth)?,
                            });
                        }
                    }
                }
                NormalizeFrame::PremiseIteCondition {
                    sort,
                    then_value,
                    else_value,
                    depth,
                } => {
                    let condition = pop_normalized(&mut results)?;
                    if self.is_bool_constant(condition, true) {
                        frames.push(NormalizeFrame::PremiseEnter {
                            value: then_value,
                            depth: next_projection_depth(depth)?,
                        });
                    } else if self.is_bool_constant(condition, false) {
                        frames.push(NormalizeFrame::PremiseEnter {
                            value: else_value,
                            depth: next_projection_depth(depth)?,
                        });
                    } else {
                        frames.push(NormalizeFrame::PremiseIteThen {
                            sort,
                            condition,
                            else_value,
                            depth,
                        });
                        frames.push(NormalizeFrame::PremiseEnter {
                            value: then_value,
                            depth: next_projection_depth(depth)?,
                        });
                    }
                }
                NormalizeFrame::PremiseIteThen {
                    sort,
                    condition,
                    else_value,
                    depth,
                } => {
                    let then_value = pop_normalized(&mut results)?;
                    frames.push(NormalizeFrame::PremiseIteElse {
                        sort,
                        condition,
                        then_value,
                    });
                    frames.push(NormalizeFrame::PremiseEnter {
                        value: else_value,
                        depth: next_projection_depth(depth)?,
                    });
                }
                NormalizeFrame::PremiseIteElse {
                    sort,
                    condition,
                    then_value,
                } => {
                    let else_value = pop_normalized(&mut results)?;
                    let normalized = if then_value == else_value {
                        then_value
                    } else {
                        self.intern(NormNode {
                            sort,
                            kind: NormKind::Ite(condition, then_value, else_value),
                        })
                    };
                    results.push(normalized);
                }
                NormalizeFrame::Not { term } => {
                    let child = pop_normalized(&mut results)?;
                    let normalized = self.make_not(child);
                    self.finish_term(term, normalized, &mut results);
                }
                NormalizeFrame::IteCondition {
                    term,
                    sort,
                    then_term,
                    else_term,
                    depth,
                } => {
                    let condition = pop_normalized(&mut results)?;
                    if self.is_bool_constant(condition, true) {
                        frames.push(NormalizeFrame::Forward { term });
                        frames.push(NormalizeFrame::Enter {
                            term: then_term,
                            depth: next_projection_depth(depth)?,
                        });
                    } else if self.is_bool_constant(condition, false) {
                        frames.push(NormalizeFrame::Forward { term });
                        frames.push(NormalizeFrame::Enter {
                            term: else_term,
                            depth: next_projection_depth(depth)?,
                        });
                    } else {
                        frames.push(NormalizeFrame::IteThen {
                            term,
                            sort,
                            condition,
                            else_term,
                            depth,
                        });
                        frames.push(NormalizeFrame::Enter {
                            term: then_term,
                            depth: next_projection_depth(depth)?,
                        });
                    }
                }
                NormalizeFrame::IteThen {
                    term,
                    sort,
                    condition,
                    else_term,
                    depth,
                } => {
                    let then_term = pop_normalized(&mut results)?;
                    frames.push(NormalizeFrame::IteElse {
                        term,
                        sort,
                        condition,
                        then_term,
                    });
                    frames.push(NormalizeFrame::Enter {
                        term: else_term,
                        depth: next_projection_depth(depth)?,
                    });
                }
                NormalizeFrame::IteElse {
                    term,
                    sort,
                    condition,
                    then_term,
                } => {
                    let else_term = pop_normalized(&mut results)?;
                    let normalized = if then_term == else_term {
                        then_term
                    } else {
                        self.intern(NormNode {
                            sort,
                            kind: NormKind::Ite(condition, then_term, else_term),
                        })
                    };
                    self.finish_term(term, normalized, &mut results);
                }
                NormalizeFrame::Application {
                    term,
                    sort,
                    symbol,
                    arity,
                } => {
                    let first_argument = results.len().checked_sub(arity).ok_or(
                        ProjectionCertificateRejection::InternalInvariant {
                            kind: "normalizer application result stack underflow",
                        },
                    )?;
                    let normalized = results.split_off(first_argument);
                    let normalized = self.finish_application(sort, symbol, normalized)?;
                    self.finish_term(term, normalized, &mut results);
                }
            }
        }

        if results.len() != 1 || !self.active.is_empty() {
            return Err(ProjectionCertificateRejection::InternalInvariant {
                kind: "normalizer completed with inconsistent stacks",
            });
        }
        results
            .pop()
            .ok_or(ProjectionCertificateRejection::InternalInvariant {
                kind: "normalizer final result missing",
            })
    }

    fn finish_term(&mut self, term: TermId, normalized: NormId, results: &mut Vec<NormId>) {
        self.active.remove(&term);
        self.memo.insert(term, normalized);
        results.push(normalized);
    }

    fn finish_application(
        &mut self,
        sort: Sort,
        symbol: Symbol,
        normalized: Vec<NormId>,
    ) -> Result<NormId, ProjectionCertificateRejection> {
        match &symbol {
            Symbol::Named(name) if name == "and" => Ok(self.make_and(normalized)),
            Symbol::Named(name) if name == "or" => Ok(self.make_or(normalized)),
            Symbol::Named(name) if name == "not" => {
                let [term] = normalized.as_slice() else {
                    return Err(ProjectionCertificateRejection::InternalInvariant {
                        kind: "validated not application changed arity",
                    });
                };
                Ok(self.make_not(*term))
            }
            Symbol::Named(name) if matches!(name.as_str(), "=>" | "implies") => {
                let [left, right] = normalized.as_slice() else {
                    return Err(ProjectionCertificateRejection::InternalInvariant {
                        kind: "validated implication application changed arity",
                    });
                };
                let left = self.make_not(*left);
                Ok(self.make_or(vec![left, *right]))
            }
            Symbol::Named(name) if name == "xor" => {
                let [left, right] = normalized.as_slice() else {
                    return Err(ProjectionCertificateRejection::InternalInvariant {
                        kind: "validated xor application changed arity",
                    });
                };
                Ok(self.make_xor(*left, *right))
            }
            Symbol::Named(name) if name == "=" => {
                let [left, right] = normalized.as_slice() else {
                    return Err(ProjectionCertificateRejection::InternalInvariant {
                        kind: "validated equality application changed arity",
                    });
                };
                Ok(self.make_equality(*left, *right))
            }
            Symbol::Named(name) if name == "distinct" => {
                let [left, right] = normalized.as_slice() else {
                    return Err(ProjectionCertificateRejection::InternalInvariant {
                        kind: "validated distinct application changed arity",
                    });
                };
                let equality = self.make_equality(*left, *right);
                Ok(self.make_not(equality))
            }
            _ => Ok(self.intern(NormNode {
                sort,
                kind: NormKind::App(symbol, normalized),
            })),
        }
    }

    fn intern(&mut self, node: NormNode) -> NormId {
        if let Some(&id) = self.interned.get(&node) {
            return id;
        }
        let id = NormId(self.arena.len());
        self.arena.push(node.clone());
        self.interned.insert(node, id);
        id
    }

    fn bool_constant(&mut self, value: bool) -> NormId {
        self.intern(NormNode {
            sort: Sort::Bool,
            kind: NormKind::Const(Constant::Bool(value)),
        })
    }

    fn is_bool_constant(&self, term: NormId, value: bool) -> bool {
        matches!(
            self.arena.get(term.0),
            Some(NormNode {
                kind: NormKind::Const(Constant::Bool(found)),
                ..
            }) if *found == value
        )
    }

    fn make_not(&mut self, term: NormId) -> NormId {
        if self.is_bool_constant(term, true) {
            return self.bool_constant(false);
        }
        if self.is_bool_constant(term, false) {
            return self.bool_constant(true);
        }
        if let Some(NormNode {
            kind: NormKind::Not(inner),
            ..
        }) = self.arena.get(term.0)
        {
            return *inner;
        }
        self.intern(NormNode {
            sort: Sort::Bool,
            kind: NormKind::Not(term),
        })
    }

    fn make_and(&mut self, terms: Vec<NormId>) -> NormId {
        let mut flat = Vec::new();
        for term in terms {
            if self.is_bool_constant(term, false) {
                return self.bool_constant(false);
            }
            if self.is_bool_constant(term, true) {
                continue;
            }
            match self.arena.get(term.0) {
                Some(NormNode {
                    kind: NormKind::And(children),
                    ..
                }) => flat.extend(children.iter().copied()),
                _ => flat.push(term),
            }
        }
        flat.sort_unstable();
        flat.dedup();
        if contains_complement(&self.arena, &flat) {
            return self.bool_constant(false);
        }
        match flat.as_slice() {
            [] => self.bool_constant(true),
            [only] => *only,
            _ => self.intern(NormNode {
                sort: Sort::Bool,
                kind: NormKind::And(flat),
            }),
        }
    }

    fn make_or(&mut self, terms: Vec<NormId>) -> NormId {
        let mut flat = Vec::new();
        for term in terms {
            if self.is_bool_constant(term, true) {
                return self.bool_constant(true);
            }
            if self.is_bool_constant(term, false) {
                continue;
            }
            match self.arena.get(term.0) {
                Some(NormNode {
                    kind: NormKind::Or(children),
                    ..
                }) => flat.extend(children.iter().copied()),
                _ => flat.push(term),
            }
        }
        flat.sort_unstable();
        flat.dedup();
        if contains_complement(&self.arena, &flat) {
            return self.bool_constant(true);
        }
        match flat.as_slice() {
            [] => self.bool_constant(false),
            [only] => *only,
            _ => self.intern(NormNode {
                sort: Sort::Bool,
                kind: NormKind::Or(flat),
            }),
        }
    }

    fn make_xor(&mut self, left: NormId, right: NormId) -> NormId {
        if left == right {
            return self.bool_constant(false);
        }
        if self.is_bool_constant(left, false) {
            return right;
        }
        if self.is_bool_constant(right, false) {
            return left;
        }
        if self.is_bool_constant(left, true) {
            return self.make_not(right);
        }
        if self.is_bool_constant(right, true) {
            return self.make_not(left);
        }
        if are_complements(&self.arena, left, right) {
            return self.bool_constant(true);
        }
        let mut pair = vec![left, right];
        pair.sort_unstable();
        self.intern(NormNode {
            sort: Sort::Bool,
            kind: NormKind::App(Symbol::named("xor"), pair),
        })
    }

    fn make_equality(&mut self, left: NormId, right: NormId) -> NormId {
        if left == right {
            return self.bool_constant(true);
        }
        let left_node = self.arena.get(left.0).cloned();
        let right_node = self.arena.get(right.0).cloned();
        if let (
            Some(NormNode {
                kind: NormKind::Const(left_constant),
                ..
            }),
            Some(NormNode {
                kind: NormKind::Const(right_constant),
                ..
            }),
        ) = (&left_node, &right_node)
        {
            return self.bool_constant(left_constant == right_constant);
        }
        if matches!(
            left_node,
            Some(NormNode {
                sort: Sort::Bool,
                ..
            })
        ) {
            if self.is_bool_constant(left, true) {
                return right;
            }
            if self.is_bool_constant(right, true) {
                return left;
            }
            if self.is_bool_constant(left, false) {
                return self.make_not(right);
            }
            if self.is_bool_constant(right, false) {
                return self.make_not(left);
            }
            if are_complements(&self.arena, left, right) {
                return self.bool_constant(false);
            }
        }
        let mut pair = vec![left, right];
        pair.sort_unstable();
        self.intern(NormNode {
            sort: Sort::Bool,
            kind: NormKind::App(Symbol::named("="), pair),
        })
    }
}

fn are_complements(arena: &[NormNode], left: NormId, right: NormId) -> bool {
    matches!(arena.get(left.0), Some(NormNode { kind: NormKind::Not(inner), .. }) if *inner == right)
        || matches!(arena.get(right.0), Some(NormNode { kind: NormKind::Not(inner), .. }) if *inner == left)
}

fn contains_complement(arena: &[NormNode], terms: &[NormId]) -> bool {
    terms.iter().any(|term| {
        matches!(
            arena.get(term.0),
            Some(NormNode {
                kind: NormKind::Not(inner),
                ..
            }) if terms.binary_search(inner).is_ok()
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bv8() -> Sort {
        Sort::bitvec(8)
    }

    fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
        terms.mk_app(Symbol::named(name), args, sort)
    }

    fn eq(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
        app(terms, "=", &[left, right], Sort::Bool)
    }

    fn candidate(
        symbol: &str,
        parameter_sorts: Vec<Sort>,
        result_sort: Sort,
        projected_parameter: usize,
        conclusion: TermId,
    ) -> ProjectionImplicationCandidate {
        ProjectionImplicationCandidate {
            definitions: vec![ProjectionUfCandidate {
                symbol: Symbol::named(symbol),
                parameter_sorts,
                result_sort,
                projected_parameter,
            }],
            conclusion,
        }
    }

    fn direct_projection_problem() -> (
        TermStore,
        TermId,
        ProjectionImplicationCandidate,
        TermId,
        TermId,
    ) {
        let mut terms = TermStore::new();
        let sort = bv8();
        let x = terms.mk_var("x", sort.clone());
        let y = terms.mk_var("y", sort.clone());
        let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
        let premise = eq(&mut terms, x, zero);
        let f = app(&mut terms, "misleading_y", &[y, x], sort.clone());
        let conclusion = eq(&mut terms, f, zero);
        let body = app(&mut terms, "=>", &[premise, conclusion], Sort::Bool);
        let root = terms.mk_forall(
            vec![
                ("x".to_string(), sort.clone()),
                ("y".to_string(), sort.clone()),
            ],
            body,
        );
        let proposal = candidate(
            "misleading_y",
            vec![sort.clone(), sort.clone()],
            sort,
            1,
            conclusion,
        );
        (terms, root, proposal, x, y)
    }

    #[test]
    fn accepts_direct_implication_and_binds_exact_snapshot() {
        let (mut terms, root, proposal, _, _) = direct_projection_problem();
        let checked = check_projection_implication(&terms, &[root], &proposal)
            .expect("the total second-argument projection proves the implication");

        assert_eq!(checked.assertion(), root);
        assert_eq!(checked.assertions(), &[root]);
        assert_eq!(checked.definitions().len(), 1);
        assert_eq!(
            checked.definitions()[0].symbol(),
            &Symbol::named("misleading_y")
        );
        assert_eq!(checked.definitions()[0].projected_parameter(), 1);
        assert_eq!(checked.definitions()[0].binder_permutation(), &[1, 0]);
        assert!(checked.matches_snapshot(&terms, &[root]));

        // Appending an unrelated term does not mutate the frozen root DAG.
        let _unrelated = terms.mk_var("unrelated", Sort::Bool);
        assert!(checked.matches_snapshot(&terms, &[root]));
        assert!(!checked.matches_snapshot(&terms, &[]));
    }

    #[test]
    fn cooperative_stop_never_returns_partial_evidence() {
        let (terms, root, proposal, _, _) = direct_projection_problem();
        let mut polls = 0usize;
        let error = check_projection_implication_with_stop(&terms, &[root], &proposal, || {
            polls += 1;
            polls >= 2
        })
        .expect_err("a stopped check must not expose accepted evidence");
        assert_eq!(error, ProjectionCertificateRejection::Stopped);
        assert_eq!(polls, 2);
    }

    #[test]
    fn accepts_live_frontend_flattened_de_morgan_implication() {
        let mut terms = TermStore::new();
        let sort = bv8();
        let x = terms.mk_var("x", sort.clone());
        let y = terms.mk_var("y", sort.clone());
        let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
        let x_zero = eq(&mut terms, x, zero);
        let y_x = eq(&mut terms, y, x);
        let premise = terms.mk_and(vec![x_zero, y_x]);
        let f = app(&mut terms, "f", &[y, x], sort.clone());
        let conclusion = eq(&mut terms, f, zero);

        // This is the actual frontend representation path: `mk_not` applies De
        // Morgan to the premise and `mk_or` flattens/sorts the resulting clause.
        let body = terms.mk_implies(premise, conclusion);
        let TermData::App(Symbol::Named(name), args) = terms.get(body) else {
            panic!("expected flattened OR");
        };
        assert_eq!(name, "or");
        assert_eq!(args.len(), 3);

        let root = terms.mk_forall(
            vec![
                ("x".to_string(), sort.clone()),
                ("y".to_string(), sort.clone()),
            ],
            body,
        );
        let proposal = candidate("f", vec![sort.clone(), sort.clone()], sort, 0, conclusion);
        check_projection_implication(&terms, &[root], &proposal)
            .expect("the exact flattened implication must be accepted");
    }

    #[test]
    fn accepts_bool_substitution_and_dead_ite_branch() {
        let mut terms = TermStore::new();
        let sort = bv8();
        let enabled = terms.mk_var("enabled", Sort::Bool);
        let x = terms.mk_var("x", sort.clone());
        let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
        let one = terms.mk_bitvec(BigInt::from(1_u8), 8);
        let true_term = terms.mk_bool(true);
        let enabled_true = eq(&mut terms, enabled, true_term);
        let x_zero = eq(&mut terms, x, zero);
        let premise = app(&mut terms, "and", &[enabled_true, x_zero], Sort::Bool);
        let f = app(&mut terms, "choose_x", &[enabled, x], sort.clone());
        let selected = terms.mk_ite(enabled, f, one);
        let conclusion = eq(&mut terms, selected, zero);
        let body = app(&mut terms, "=>", &[premise, conclusion], Sort::Bool);
        let root = terms.mk_forall(
            vec![
                ("enabled".to_string(), Sort::Bool),
                ("x".to_string(), sort.clone()),
            ],
            body,
        );
        let proposal = candidate(
            "choose_x",
            vec![Sort::Bool, sort.clone()],
            sort,
            1,
            conclusion,
        );

        check_projection_implication(&terms, &[root], &proposal)
            .expect("premise substitution must reduce the ITE condition to true");
    }

    #[test]
    fn accepts_flattened_positive_and_negative_bool_literal_hypotheses() {
        let mut terms = TermStore::new();
        let sort = bv8();
        let enabled = terms.mk_var("enabled", Sort::Bool);
        let blocked = terms.mk_var("blocked", Sort::Bool);
        let x = terms.mk_var("x", sort.clone());
        let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
        let one = terms.mk_bitvec(BigInt::from(1_u8), 8);
        let not_blocked = terms.mk_not_raw(blocked);
        let x_zero = eq(&mut terms, x, zero);
        let premise = terms.mk_and(vec![enabled, not_blocked, x_zero]);
        let f = app(&mut terms, "select_x", &[enabled, blocked, x], sort.clone());
        let blocked_choice = terms.mk_ite(blocked, one, f);
        let selected = terms.mk_ite(enabled, blocked_choice, one);
        let conclusion = eq(&mut terms, selected, zero);
        let body = terms.mk_implies(premise, conclusion);
        let root = terms.mk_forall(
            vec![
                ("enabled".to_string(), Sort::Bool),
                ("blocked".to_string(), Sort::Bool),
                ("x".to_string(), sort.clone()),
            ],
            body,
        );
        let proposal = candidate(
            "select_x",
            vec![Sort::Bool, Sort::Bool, sort.clone()],
            sort,
            2,
            conclusion,
        );

        check_projection_implication(&terms, &[root], &proposal)
            .expect("flattened b and not-b hypotheses must rewrite to true and false");
    }

    #[test]
    fn rejects_wrong_projection() {
        let (terms, root, mut proposal, _, _) = direct_projection_problem();
        proposal.definitions[0].projected_parameter = 0;
        let result = check_projection_implication(&terms, &[root], &proposal);
        assert_eq!(
            result.unwrap_err(),
            ProjectionCertificateRejection::ConclusionDidNotNormalizeTrue
        );
    }

    #[test]
    fn rejects_omitted_repeated_and_transformed_binder_arguments() {
        for shape in ["omitted", "repeated", "transformed"] {
            let mut terms = TermStore::new();
            let sort = bv8();
            let x = terms.mk_var("x", sort.clone());
            let y = terms.mk_var("y", sort.clone());
            let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
            let x_zero = eq(&mut terms, x, zero);
            let y_zero = eq(&mut terms, y, zero);
            let premise = app(&mut terms, "and", &[x_zero, y_zero], Sort::Bool);
            let transformed = app(&mut terms, "bvadd", &[x, zero], sort.clone());
            let args = match shape {
                "omitted" => vec![x],
                "repeated" => vec![x, x],
                "transformed" => vec![y, transformed],
                _ => unreachable!(),
            };
            let f = app(&mut terms, "f", &args, sort.clone());
            let conclusion = eq(&mut terms, f, zero);
            let body = app(&mut terms, "=>", &[premise, conclusion], Sort::Bool);
            let root = terms.mk_forall(
                vec![
                    ("x".to_string(), sort.clone()),
                    ("y".to_string(), sort.clone()),
                ],
                body,
            );
            let proposal = candidate("f", vec![sort.clone(), sort.clone()], sort, 1, conclusion);
            let error = check_projection_implication(&terms, &[root], &proposal).unwrap_err();
            assert!(
                matches!(
                    error,
                    ProjectionCertificateRejection::ApplicationSignatureMismatch { .. }
                        | ProjectionCertificateRejection::ApplicationNotBinderPermutation { .. }
                ),
                "{shape}: {error:?}"
            );
        }
    }

    #[test]
    fn rejects_one_symbol_at_two_binder_permutations() {
        let mut terms = TermStore::new();
        let sort = bv8();
        let x = terms.mk_var("x", sort.clone());
        let y = terms.mk_var("y", sort.clone());
        let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
        let x_zero = eq(&mut terms, x, zero);
        let y_zero = eq(&mut terms, y, zero);
        let premise = app(&mut terms, "and", &[x_zero, y_zero], Sort::Bool);
        let f_yx = app(&mut terms, "f", &[y, x], sort.clone());
        let f_xy = app(&mut terms, "f", &[x, y], sort.clone());
        let first = eq(&mut terms, f_yx, zero);
        let second = eq(&mut terms, f_xy, zero);
        let conclusion = app(&mut terms, "and", &[first, second], Sort::Bool);
        let body = app(&mut terms, "=>", &[premise, conclusion], Sort::Bool);
        let root = terms.mk_forall(
            vec![
                ("x".to_string(), sort.clone()),
                ("y".to_string(), sort.clone()),
            ],
            body,
        );
        let proposal = candidate("f", vec![sort.clone(), sort.clone()], sort, 1, conclusion);

        assert!(matches!(
            check_projection_implication(&terms, &[root], &proposal),
            Err(ProjectionCertificateRejection::InconsistentApplicationPermutation { .. })
        ));
    }

    #[test]
    fn rejects_forged_signature_and_builtin_collision() {
        let (terms, root, mut proposal, _, _) = direct_projection_problem();
        proposal.definitions[0].parameter_sorts[0] = Sort::Bool;
        assert!(matches!(
            check_projection_implication(&terms, &[root], &proposal),
            Err(ProjectionCertificateRejection::ApplicationSignatureMismatch { .. })
        ));

        proposal.definitions[0].symbol = Symbol::named("extract");
        assert!(matches!(
            check_projection_implication(&terms, &[root], &proposal),
            Err(ProjectionCertificateRejection::UnsupportedDefinitionSymbol { .. })
        ));
    }

    #[test]
    fn rejects_cycles_and_finds_a_helpful_duplicate_subset_strategy() {
        for duplicate in [false, true] {
            let mut terms = TermStore::new();
            let sort = bv8();
            let x = terms.mk_var("x", sort.clone());
            let y = terms.mk_var("y", sort.clone());
            let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
            let first = eq(&mut terms, x, y);
            let second = if duplicate {
                eq(&mut terms, x, zero)
            } else {
                eq(&mut terms, y, x)
            };
            let premise = app(&mut terms, "and", &[first, second], Sort::Bool);
            let f = app(&mut terms, "f", &[x, y], sort.clone());
            let conclusion = eq(&mut terms, f, zero);
            let body = app(&mut terms, "=>", &[premise, conclusion], Sort::Bool);
            let root = terms.mk_forall(
                vec![
                    ("x".to_string(), sort.clone()),
                    ("y".to_string(), sort.clone()),
                ],
                body,
            );
            let proposal = candidate("f", vec![sort.clone(), sort.clone()], sort, 0, conclusion);
            if duplicate {
                let binder_by_term = HashMap::from([(x, 0_usize), (y, 1_usize)]);
                let definitions = HashMap::from([(Symbol::named("f"), 0_usize)]);
                let mut never_stop = || false;
                let mut stop = ProjectionStopPoller::new(&mut never_stop);
                let implication = extract_implication(&terms, body, conclusion, &mut stop)
                    .expect("test implication shape");

                let first_env = build_premise_environment(
                    &terms,
                    &implication.premise_hypotheses,
                    &binder_by_term,
                    &definitions,
                    &proposal.definitions,
                    PREMISE_SELECTION_STRATEGIES[0],
                    &mut stop,
                )
                .expect("first deterministic environment");
                let mut first = Normalizer::new(
                    &terms,
                    &binder_by_term,
                    &definitions,
                    &proposal.definitions,
                    &first_env,
                );
                let first_result = first
                    .normalize(conclusion, 0, &mut stop)
                    .expect("normalize first strategy");
                assert!(!first.is_bool_constant(first_result, true));

                let second_env = build_premise_environment(
                    &terms,
                    &implication.premise_hypotheses,
                    &binder_by_term,
                    &definitions,
                    &proposal.definitions,
                    PREMISE_SELECTION_STRATEGIES[1],
                    &mut stop,
                )
                .expect("second deterministic environment");
                let mut second = Normalizer::new(
                    &terms,
                    &binder_by_term,
                    &definitions,
                    &proposal.definitions,
                    &second_env,
                );
                let second_result = second
                    .normalize(conclusion, 0, &mut stop)
                    .expect("normalize second strategy");
                assert!(second.is_bool_constant(second_result, true));

                check_projection_implication(&terms, &[root], &proposal).expect(
                    "right-first orientation must retain x = 0 after left-first is unhelpful",
                );
            } else {
                let error = check_projection_implication(&terms, &[root], &proposal).unwrap_err();
                assert_eq!(
                    error,
                    ProjectionCertificateRejection::CyclicPremiseDefinitions
                );
            }
        }
    }

    #[test]
    fn accepts_sound_premise_subset_with_alternate_equality_orientation() {
        let mut terms = TermStore::new();
        let sort = bv8();
        let x = terms.mk_var("x", sort.clone());
        let y = terms.mk_var("y", sort.clone());
        let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
        let one = terms.mk_bitvec(BigInt::from(1_u8), 8);

        let x_zero = eq(&mut terms, x, zero);
        // `x` is already defined, so the symmetric equality must orient y -> x.
        let bridge = eq(&mut terms, x, y);
        // A later conflicting definition and a non-orientable hypothesis can
        // both be dropped: the retained subset proves a stronger implication.
        let x_one = eq(&mut terms, x, one);
        let zero_one = eq(&mut terms, zero, one);
        let premise = app(
            &mut terms,
            "and",
            &[x_zero, bridge, x_one, zero_one],
            Sort::Bool,
        );
        let f = app(&mut terms, "f", &[x, y], sort.clone());
        let conclusion = eq(&mut terms, f, zero);
        let body = app(&mut terms, "=>", &[premise, conclusion], Sort::Bool);
        let root = terms.mk_forall(
            vec![
                ("x".to_string(), sort.clone()),
                ("y".to_string(), sort.clone()),
            ],
            body,
        );
        let proposal = candidate("f", vec![sort.clone(), sort.clone()], sort, 1, conclusion);

        check_projection_implication(&terms, &[root], &proposal)
            .expect("a sound retained premise subset must certify the projection");
    }

    #[test]
    fn accepts_flattened_negated_distinct_as_positive_equality() {
        let mut terms = TermStore::new();
        let sort = bv8();
        let x = terms.mk_var("x", sort.clone());
        let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
        let negated_premise = app(&mut terms, "distinct", &[x, zero], Sort::Bool);
        let f = app(&mut terms, "f", &[x], sort.clone());
        let conclusion = eq(&mut terms, f, zero);
        // `(distinct x 0) or C` is the flattened form of `(= x 0) => C`.
        let body = app(&mut terms, "or", &[negated_premise, conclusion], Sort::Bool);
        let root = terms.mk_forall(vec![("x".to_string(), sort.clone())], body);
        let proposal = candidate("f", vec![sort.clone()], sort, 0, conclusion);

        check_projection_implication(&terms, &[root], &proposal)
            .expect("negated binary distinct must recover its equality hypothesis");
    }

    #[test]
    fn accepts_flattened_negated_bool_xor_as_positive_equality() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let y = terms.mk_var("y", Sort::Bool);
        let negated_premise = app(&mut terms, "xor", &[x, y], Sort::Bool);
        let f = app(&mut terms, "f", &[x, y], Sort::Bool);
        let conclusion = eq(&mut terms, f, x);
        // `(xor x y) or C` is `(not (xor x y)) => C`, and the premise
        // `not (xor x y)` is precisely the Boolean equality x = y.
        let body = app(&mut terms, "or", &[negated_premise, conclusion], Sort::Bool);
        let root = terms.mk_forall(
            vec![("x".to_string(), Sort::Bool), ("y".to_string(), Sort::Bool)],
            body,
        );
        let proposal = candidate("f", vec![Sort::Bool, Sort::Bool], Sort::Bool, 1, conclusion);

        check_projection_implication(&terms, &[root], &proposal)
            .expect("negated binary Bool XOR must recover its equality hypothesis");
    }

    #[test]
    fn accepts_synthetic_conditional_premise_definition() {
        let mut terms = TermStore::new();
        let sort = bv8();
        let condition = terms.mk_var("condition", Sort::Bool);
        let x = terms.mk_var("x", sort.clone());
        let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
        let one = terms.mk_bitvec(BigInt::from(1_u8), 8);
        let then_eq = eq(&mut terms, x, zero);
        let else_eq = eq(&mut terms, x, one);
        let then_neq = terms.mk_not_raw(then_eq);
        let else_neq = terms.mk_not_raw(else_eq);
        let negated_definition = terms.mk_ite_raw(condition, then_neq, else_neq);
        let replacement = terms.mk_ite_raw(condition, zero, one);
        let f = app(&mut terms, "f", &[condition, x], sort.clone());
        let conclusion = eq(&mut terms, f, replacement);
        let body = app(
            &mut terms,
            "or",
            &[negated_definition, conclusion],
            Sort::Bool,
        );
        let root = terms.mk_forall(
            vec![
                ("condition".to_string(), Sort::Bool),
                ("x".to_string(), sort.clone()),
            ],
            body,
        );
        let proposal = candidate("f", vec![Sort::Bool, sort.clone()], sort, 1, conclusion);

        check_projection_implication(&terms, &[root], &proposal)
            .expect("matching ITE branches must reconstruct one conditional binder definition");
    }

    #[test]
    fn rejects_invalid_conditional_premise_definitions() {
        let sort = bv8();

        // Wrong polarity: asserting the branch disequalities cannot define x.
        {
            let mut terms = TermStore::new();
            let condition = terms.mk_var("condition", Sort::Bool);
            let x = terms.mk_var("x", sort.clone());
            let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
            let one = terms.mk_bitvec(BigInt::from(1_u8), 8);
            let then_eq = eq(&mut terms, x, zero);
            let else_eq = eq(&mut terms, x, one);
            let then_neq = terms.mk_not_raw(then_eq);
            let else_neq = terms.mk_not_raw(else_eq);
            let wrong_polarity = terms.mk_ite_raw(condition, then_neq, else_neq);
            let replacement = terms.mk_ite_raw(condition, zero, one);
            let f = app(&mut terms, "f", &[condition, x], sort.clone());
            let conclusion = eq(&mut terms, f, replacement);
            let body = app(&mut terms, "=>", &[wrong_polarity, conclusion], Sort::Bool);
            let root = terms.mk_forall(
                vec![
                    ("condition".to_string(), Sort::Bool),
                    ("x".to_string(), sort.clone()),
                ],
                body,
            );
            let proposal = candidate(
                "f",
                vec![Sort::Bool, sort.clone()],
                sort.clone(),
                1,
                conclusion,
            );
            assert_eq!(
                check_projection_implication(&terms, &[root], &proposal).unwrap_err(),
                ProjectionCertificateRejection::ConclusionDidNotNormalizeTrue
            );
        }

        // Different branch binders cannot be combined into one definition.
        {
            let mut terms = TermStore::new();
            let condition = terms.mk_var("condition", Sort::Bool);
            let x = terms.mk_var("x", sort.clone());
            let y = terms.mk_var("y", sort.clone());
            let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
            let one = terms.mk_bitvec(BigInt::from(1_u8), 8);
            let then_eq = eq(&mut terms, x, zero);
            let else_eq = eq(&mut terms, y, one);
            let then_neq = terms.mk_not_raw(then_eq);
            let else_neq = terms.mk_not_raw(else_eq);
            let mixed_definition = terms.mk_ite_raw(condition, then_neq, else_neq);
            let f = app(&mut terms, "f", &[condition, x, y], sort.clone());
            let conclusion = eq(&mut terms, f, zero);
            let body = app(
                &mut terms,
                "or",
                &[mixed_definition, conclusion],
                Sort::Bool,
            );
            let root = terms.mk_forall(
                vec![
                    ("condition".to_string(), Sort::Bool),
                    ("x".to_string(), sort.clone()),
                    ("y".to_string(), sort.clone()),
                ],
                body,
            );
            let proposal = candidate(
                "f",
                vec![Sort::Bool, sort.clone(), sort.clone()],
                sort.clone(),
                1,
                conclusion,
            );
            assert_eq!(
                check_projection_implication(&terms, &[root], &proposal).unwrap_err(),
                ProjectionCertificateRejection::ConclusionDidNotNormalizeTrue
            );
        }

        // Matching branches that define x in terms of x are still cyclic.
        {
            let mut terms = TermStore::new();
            let condition = terms.mk_var("condition", Sort::Bool);
            let x = terms.mk_var("x", sort.clone());
            let self_eq = eq(&mut terms, x, x);
            let self_neq = terms.mk_not_raw(self_eq);
            let cyclic_definition = terms.mk_ite_raw(condition, self_neq, self_neq);
            let f = app(&mut terms, "f", &[condition, x], sort.clone());
            let conclusion = eq(&mut terms, f, x);
            let body = app(
                &mut terms,
                "or",
                &[cyclic_definition, conclusion],
                Sort::Bool,
            );
            let root = terms.mk_forall(
                vec![
                    ("condition".to_string(), Sort::Bool),
                    ("x".to_string(), sort.clone()),
                ],
                body,
            );
            let proposal = candidate("f", vec![Sort::Bool, sort.clone()], sort, 1, conclusion);
            assert_eq!(
                check_projection_implication(&terms, &[root], &proposal).unwrap_err(),
                ProjectionCertificateRejection::CyclicPremiseDefinitions
            );
        }
    }

    #[test]
    fn rejects_nested_binders_triggers_and_ambiguous_identity() {
        let sort = bv8();

        let mut nested_terms = TermStore::new();
        let x = nested_terms.mk_var("x", sort.clone());
        let y = nested_terms.mk_var("y", sort.clone());
        let f = app(&mut nested_terms, "f", &[x], sort.clone());
        let inner_eq = eq(&mut nested_terms, f, x);
        let inner = nested_terms.mk_forall(vec![("y".to_string(), sort.clone())], inner_eq);
        let outer = nested_terms.mk_forall(vec![("x".to_string(), sort.clone())], inner);
        let proposal = candidate("f", vec![sort.clone()], sort.clone(), 0, inner_eq);
        assert!(matches!(
            check_projection_implication(&nested_terms, &[outer], &proposal),
            Err(ProjectionCertificateRejection::UnsupportedNode { .. })
        ));
        let _ = y;

        let (mut trigger_terms, _, _, _, _) = direct_projection_problem();
        let tx = trigger_terms.mk_var("tx", sort.clone());
        let tf = app(&mut trigger_terms, "misleading_y", &[tx, tx], sort.clone());
        let t_eq = eq(&mut trigger_terms, tf, tx);
        let triggered = trigger_terms.mk_forall_with_triggers(
            vec![("tx".to_string(), sort.clone())],
            t_eq,
            vec![vec![tf]],
        );
        let trigger_proposal = candidate("misleading_y", vec![sort.clone()], sort.clone(), 0, t_eq);
        assert_eq!(
            check_projection_implication(&trigger_terms, &[triggered], &trigger_proposal)
                .unwrap_err(),
            ProjectionCertificateRejection::NonEmptyTriggers
        );

        let mut ambiguous_terms = TermStore::new();
        let x_first = ambiguous_terms.mk_var("x", sort.clone());
        let x_second = ambiguous_terms.mk_fresh_named_var("x", sort.clone());
        let zero = ambiguous_terms.mk_bitvec(BigInt::from(0_u8), 8);
        let premise = eq(&mut ambiguous_terms, x_first, zero);
        let af = app(&mut ambiguous_terms, "f", &[x_second], sort.clone());
        let conclusion = eq(&mut ambiguous_terms, af, zero);
        let body = app(
            &mut ambiguous_terms,
            "=>",
            &[premise, conclusion],
            Sort::Bool,
        );
        let ambiguous = ambiguous_terms.mk_forall(vec![("x".to_string(), sort.clone())], body);
        let proposal = candidate("f", vec![sort.clone()], sort, 0, conclusion);
        assert!(matches!(
            check_projection_implication(&ambiguous_terms, &[ambiguous], &proposal),
            Err(ProjectionCertificateRejection::AmbiguousBinderIdentity { .. })
        ));
    }

    #[test]
    fn rejects_non_operand_conclusion_and_undeclared_application() {
        let mut terms = TermStore::new();
        let sort = bv8();
        let x = terms.mk_var("x", sort.clone());
        let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
        let premise = eq(&mut terms, x, zero);
        let not_premise = terms.mk_not_raw(premise);
        let f = app(&mut terms, "f", &[x], sort.clone());
        let first = eq(&mut terms, f, zero);
        let second = eq(&mut terms, x, zero);
        let ambiguous_body = app(&mut terms, "or", &[not_premise, first, second], Sort::Bool);
        let ambiguous = terms.mk_forall(vec![("x".to_string(), sort.clone())], ambiguous_body);
        let proposal = candidate("f", vec![sort.clone()], sort.clone(), 0, zero);
        assert_eq!(
            check_projection_implication(&terms, &[ambiguous], &proposal).unwrap_err(),
            ProjectionCertificateRejection::ConclusionNotTopLevelOperand { conclusion: zero }
        );

        let mut undeclared_terms = TermStore::new();
        let ux = undeclared_terms.mk_var("x", sort.clone());
        let uzero = undeclared_terms.mk_bitvec(BigInt::from(0_u8), 8);
        let upremise = eq(&mut undeclared_terms, ux, uzero);
        let g = app(&mut undeclared_terms, "g", &[ux], sort.clone());
        let uconclusion = eq(&mut undeclared_terms, g, uzero);
        let ubody = app(
            &mut undeclared_terms,
            "=>",
            &[upremise, uconclusion],
            Sort::Bool,
        );
        let uroot = undeclared_terms.mk_forall(vec![("x".to_string(), sort.clone())], ubody);
        let undeclared_proposal = candidate("f", vec![sort.clone()], sort, 0, uconclusion);
        assert!(matches!(
            check_projection_implication(&undeclared_terms, &[uroot], &undeclared_proposal),
            Err(ProjectionCertificateRejection::UnsupportedApplication { .. })
        ));
    }

    #[test]
    fn shared_conjunction_dag_is_flattened_once() {
        let mut terms = TermStore::new();
        let sort = bv8();
        let x = terms.mk_var("x", sort.clone());
        let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
        let mut premise = eq(&mut terms, x, zero);

        // Unfolding this DAG as a tree would visit 2^128 leaves. The checker
        // must instead visit each distinct conjunction node once.
        for _ in 0..128 {
            premise = app(&mut terms, "and", &[premise, premise], Sort::Bool);
        }

        let f = app(&mut terms, "f", &[x], sort.clone());
        let conclusion = eq(&mut terms, f, zero);
        let body = app(&mut terms, "=>", &[premise, conclusion], Sort::Bool);
        let root = terms.mk_forall(vec![("x".to_string(), sort.clone())], body);
        let proposal = candidate("f", vec![sort.clone()], sort, 0, conclusion);

        check_projection_implication(&terms, &[root], &proposal)
            .expect("shared premise DAG must be processed in DAG-linear work");
    }

    #[test]
    fn huge_bitvector_width_validation_does_not_materialize_modulus() {
        let mut terms = TermStore::new();
        let diagnostic_term = terms.mk_bool(false);
        let huge_zero = Constant::BitVec {
            value: BigInt::from(0_u8),
            width: u32::MAX,
        };

        assert_eq!(
            validate_constant(diagnostic_term, &huge_zero, &Sort::bitvec(u32::MAX)),
            Ok(())
        );

        let too_large = Constant::BitVec {
            value: BigInt::from(256_u16),
            width: 8,
        };
        assert_eq!(
            validate_constant(diagnostic_term, &too_large, &Sort::bitvec(8)),
            Err(ProjectionCertificateRejection::IllSortedTerm {
                term: diagnostic_term
            })
        );
    }

    #[test]
    fn impossible_definition_index_is_an_internal_invariant_failure() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let application = app(&mut terms, "f", &[x], Sort::Bool);
        let symbol = Symbol::named("f");
        let definitions = HashMap::from([(symbol.clone(), 1)]);
        let candidates = vec![ProjectionUfCandidate {
            symbol,
            parameter_sorts: vec![Sort::Bool],
            result_sort: Sort::Bool,
            projected_parameter: 0,
        }];

        assert_eq!(
            projected_argument(&terms, application, &definitions, &candidates).unwrap_err(),
            ProjectionCertificateRejection::InternalInvariant {
                kind: "definition map index outside projection candidates"
            }
        );
    }

    #[test]
    fn impossible_projected_argument_is_an_internal_invariant_failure() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let application = app(&mut terms, "f", &[x], Sort::Bool);
        let symbol = Symbol::named("f");
        let definitions = HashMap::from([(symbol.clone(), 0)]);
        let candidates = vec![ProjectionUfCandidate {
            symbol,
            parameter_sorts: vec![Sort::Bool, Sort::Bool],
            result_sort: Sort::Bool,
            projected_parameter: 1,
        }];

        assert_eq!(
            projected_argument(&terms, application, &definitions, &candidates).unwrap_err(),
            ProjectionCertificateRejection::InternalInvariant {
                kind: "projected parameter outside validated application arguments"
            }
        );
    }

    #[test]
    fn deterministic_work_budget_is_global_and_fail_closed() {
        let mut never_stop = || false;
        let mut stop = ProjectionStopPoller::with_budget(&mut never_stop, 2);
        assert_eq!(stop.step(), Ok(()));
        assert_eq!(stop.step(), Ok(()));
        assert_eq!(
            stop.step(),
            Err(ProjectionCertificateRejection::ResourceLimit)
        );

        let mut external_stop = || true;
        let mut stopped = ProjectionStopPoller::with_budget(&mut external_stop, 0);
        assert_eq!(
            stopped.step(),
            Err(ProjectionCertificateRejection::Stopped),
            "an external solve stop retains its distinct reason at the budget boundary"
        );

        let mut never_stop = || false;
        let mut bulk = ProjectionStopPoller::with_budget(&mut never_stop, 3);
        assert_eq!(
            bulk.charge(4),
            Err(ProjectionCertificateRejection::ResourceLimit),
            "an over-budget bulk operation must be rejected atomically"
        );
        assert_eq!(bulk.charge(3), Ok(()));
        assert_eq!(
            bulk.step(),
            Err(ProjectionCertificateRejection::ResourceLimit),
            "a rejected bulk charge must not consume the remaining budget"
        );
    }

    #[test]
    fn cooperative_stop_polling_has_an_exact_sixty_four_unit_interval() {
        use std::cell::Cell;

        let polls = Cell::new(0_usize);
        let mut count_poll = || {
            polls.set(polls.get() + 1);
            false
        };
        let mut stop = ProjectionStopPoller::with_budget(&mut count_poll, 1_000);

        stop.boundary().expect("the initial poll must continue");
        assert_eq!(polls.get(), 1);
        for _ in 0..ProjectionStopPoller::INTERVAL {
            stop.step().expect("the test budget is ample");
        }
        assert_eq!(polls.get(), 1, "exactly 64 charged units fit after a poll");
        stop.step().expect("the test budget is ample");
        assert_eq!(
            polls.get(),
            2,
            "the next unit must poll before doing more work"
        );
    }

    #[test]
    fn high_fanout_graph_walks_charge_children_before_scheduling() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let high_fanout = app(&mut terms, "and", &[x, x, x, x], Sort::Bool);

        {
            let mut never_stop = || false;
            let mut stop = ProjectionStopPoller::with_budget(&mut never_stop, 3);
            assert_eq!(
                freeze_reachable_terms(&terms, &[high_fanout], &mut stop).unwrap_err(),
                ProjectionCertificateRejection::ResourceLimit
            );
        }

        {
            let binder_decls = vec![("x".to_string(), Sort::Bool)];
            let binder_names = HashMap::from([("x", 0_usize)]);
            let mut never_stop = || false;
            let mut stop = ProjectionStopPoller::with_budget(&mut never_stop, 3);
            assert_eq!(
                discover_binder_terms(
                    &terms,
                    high_fanout,
                    &binder_decls,
                    &binder_names,
                    &mut stop,
                )
                .unwrap_err(),
                ProjectionCertificateRejection::ResourceLimit
            );
        }

        {
            let binder_by_term = HashMap::from([(x, 0_usize)]);
            let definitions = HashMap::new();
            let candidates = Vec::new();
            let mut never_stop = || false;
            let mut stop = ProjectionStopPoller::with_budget(&mut never_stop, 4);
            let mut validation = BodyValidation::new(
                &terms,
                &binder_by_term,
                &definitions,
                &candidates,
                &mut stop,
            )
            .expect("empty validation tables require no bulk work");
            assert_eq!(
                validation.validate(high_fanout, &mut stop),
                Err(ProjectionCertificateRejection::ResourceLimit)
            );
        }
    }

    #[test]
    fn deep_normalization_hits_resource_limit_on_small_native_stack() {
        let rejection = std::thread::Builder::new()
            .name("projection-small-stack".to_string())
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                let mut terms = TermStore::new();
                let x = terms.mk_var("x", Sort::Bool);
                let f = app(&mut terms, "f", &[x], Sort::Bool);
                let mut conclusion = f;
                for _ in 0..=MAX_PROJECTION_DEPTH {
                    conclusion = terms.mk_not_raw(conclusion);
                }
                let body = app(&mut terms, "=>", &[x, conclusion], Sort::Bool);
                let root = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], body);
                let proposal = candidate("f", vec![Sort::Bool], Sort::Bool, 0, conclusion);

                check_projection_implication(&terms, &[root], &proposal)
                    .map(|_| ())
                    .unwrap_err()
            })
            .expect("small-stack test thread must start")
            .join()
            .expect("the iterative checker must not overflow its native stack");

        assert_eq!(rejection, ProjectionCertificateRejection::ResourceLimit);
    }
}
