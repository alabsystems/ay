// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Public SMT-LIB sort identity retained beside engine sort lowering.
//!
//! Z3 5.0.0 gives `FiniteSet` its own sort identity. AY intentionally keeps
//! using the mature characteristic-array implementation internally, so this
//! module carries the missing public identity through textual elaboration and
//! rejects terms that would become spuriously well-sorted after lowering. It
//! also retains character-valued indexed literals and operations as
//! [`Sort::Char`] instead of conflating them with plain integers.

use std::fmt;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, TermId};

use crate::command::{self, ParsedConstant, QualifiedIdentifier, Term as ParsedTerm};
use crate::sexp::{SExpr, PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE};

use super::{Context, ElaborateError, Result, SymbolInfo};

/// A public SMT-LIB sort before implementation lowering.
///
/// `FiniteSet` is deliberately not represented by [`Sort`]: the engine lowers
/// it to an array. Character-valued terms are represented here by `Sort::Char`
/// but lower to integers in the currently supported ground fragment. This tree
/// retains those Z3 5.0.0 type identities at every nesting level.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum PublicSort {
    /// A core sort with no `FiniteSet` identity hidden inside it. `Sort::Char`
    /// retains character-valued literal/operator identity over Int lowering;
    /// the free textual `Unicode` sort remains unsupported until AY can enforce
    /// its finite domain.
    Core(Sort),
    /// An array sort.
    Array(Box<Self>, Box<Self>),
    /// A sequence sort.
    Seq(Box<Self>),
    /// Z3 5.0.0's distinct finite-set sort.
    FiniteSet(Box<Self>),
    /// A context-polymorphic `set.singleton`/shared set constructor result.
    ///
    /// Z3 resolves these constructors to either legacy `Set` or `FiniteSet`
    /// from their use site. This variant is occurrence metadata only and is
    /// never stored for a declaration.
    AmbiguousSet(Box<Self>),
    /// A non-finite-set term whose exact public type is irrelevant here.
    ///
    /// The ordinary engine elaborator has already checked its full type.
    Unknown,
}

impl PublicSort {
    /// Whether this sort contains a `FiniteSet` at any nesting depth.
    #[must_use]
    pub fn contains_finite_set(&self) -> bool {
        match self {
            Self::FiniteSet(_) => true,
            Self::Array(index, element) => {
                index.contains_finite_set() || element.contains_finite_set()
            }
            Self::Seq(element) | Self::AmbiguousSet(element) => element.contains_finite_set(),
            Self::Core(_) | Self::Unknown => false,
        }
    }

    fn contains_char(&self) -> bool {
        match self {
            Self::Core(Sort::Char) => true,
            Self::Array(index, element) => index.contains_char() || element.contains_char(),
            Self::Seq(element) | Self::FiniteSet(element) | Self::AmbiguousSet(element) => {
                element.contains_char()
            }
            Self::Core(_) | Self::Unknown => false,
        }
    }

    /// Engine sort obtained by lowering `FiniteSet(T)` to `Array(T, Bool)`.
    #[must_use]
    pub fn engine_sort(&self) -> Option<Sort> {
        match self {
            Self::Core(sort) => Some(sort.clone()),
            Self::Array(index, element) => {
                Some(Sort::array(index.engine_sort()?, element.engine_sort()?))
            }
            Self::Seq(element) => Some(Sort::seq(element.engine_sort()?)),
            Self::FiniteSet(element) | Self::AmbiguousSet(element) => {
                Some(Sort::array(element.engine_sort()?, Sort::Bool))
            }
            Self::Unknown => None,
        }
    }

    pub(super) fn from_engine(sort: &Sort) -> Self {
        match sort {
            Sort::Array(array) => Self::Array(
                Box::new(Self::from_engine(&array.index_sort)),
                Box::new(Self::from_engine(&array.element_sort)),
            ),
            Sort::Seq(element) => Self::Seq(Box::new(Self::from_engine(element))),
            _ => Self::Core(sort.clone()),
        }
    }

    fn legacy_set_basis(&self) -> Option<&Self> {
        match self {
            Self::Array(index, element) if matches!(element.as_ref(), Self::Core(Sort::Bool)) => {
                Some(index)
            }
            _ => None,
        }
    }
}

impl fmt::Display for PublicSort {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Core(sort) => write!(formatter, "{sort}"),
            Self::Array(index, element) => write!(formatter, "(Array {index} {element})"),
            Self::Seq(element) => write!(formatter, "(Seq {element})"),
            Self::FiniteSet(element) => write!(formatter, "(FiniteSet {element})"),
            Self::AmbiguousSet(element) => write!(formatter, "(set.constructor {element})"),
            Self::Unknown => formatter.write_str("<engine-checked-sort>"),
        }
    }
}

/// Finite-set provenance for one parsed assertion.
///
/// The flags let API adapters distinguish constructor-only formulas from
/// arbitrary finite-set values and finite-set binders, which currently need a
/// conservative fail-closed gate in backends that cannot retain public sorts.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct FiniteSetTermMetadata {
    /// The assertion uses the Z3 5.0.0 `FiniteSet` theory.
    pub uses_finite_set: bool,
    /// It reads a declared/boundary function or constant of finite-set sort.
    pub has_arbitrary_value: bool,
    /// It binds a finite-set value in a quantifier or lambda.
    pub has_finite_set_binder: bool,
}

/// Z3 5.0.0 finite-set operation retained at one parsed term occurrence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum FiniteSetOp {
    /// Qualified empty-set constant.
    Empty,
    /// Singleton constructor.
    Singleton,
    /// Union.
    Union,
    /// Intersection.
    Intersect,
    /// Difference.
    Difference,
    /// Membership.
    In,
    /// Cardinality.
    Size,
    /// Subset predicate.
    Subset,
    /// Image under a function.
    Map,
    /// Filter by a predicate.
    Filter,
    /// Inclusive integer range.
    Range,
}

/// Public metadata for one parsed term occurrence.
///
/// `engine_term` names the lowered AY term for this occurrence. `arguments`
/// retain source argument order even when lowering rewrites the operation
/// (for example, `set.singleton` becomes an array `store`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PublicTermMetadata {
    /// Lowered engine term for this occurrence.
    pub engine_term: TermId,
    /// Public sort before lowering.
    pub public_sort: PublicSort,
    /// Finite-set operator, when this occurrence is one.
    pub finite_set_op: Option<FiniteSetOp>,
    /// Parsed public sorts of binders introduced by this occurrence.
    ///
    /// This is populated for `forall`, `exists`, and `lambda`. Bound engine
    /// terms are allocated during elaboration and cannot be reconstructed from
    /// the already-built root, but their declared public sorts remain exact.
    pub public_bound_sorts: Vec<PublicSort>,
    /// Parsed/source arguments in order.
    pub arguments: Vec<Self>,
}

/// Public metadata aligned with one hard assertion.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PublicAssertionMetadata {
    /// Aggregate finite-set usage flags.
    pub finite_sets: FiniteSetTermMetadata,
    /// Occurrence tree when the assertion uses `FiniteSet`.
    pub root: Option<PublicTermMetadata>,
}

impl FiniteSetTermMetadata {
    fn merge(&mut self, other: Self) {
        self.uses_finite_set |= other.uses_finite_set;
        self.has_arbitrary_value |= other.has_arbitrary_value;
        self.has_finite_set_binder |= other.has_finite_set_binder;
    }
}

/// Public signature for a declared SMT-LIB symbol.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PublicSymbolSignature {
    /// Surface symbol name.
    pub name: String,
    /// Engine/internal identity used by lowered applications.
    pub internal_name: String,
    /// Public argument sorts.
    pub arguments: Vec<PublicSort>,
    /// Public result sort.
    pub result: PublicSort,
    /// Whether a nullary result is an unconstrained declared value.
    pub is_arbitrary_constant: bool,
    /// Whether this signature belongs to a `define-fun` body.
    pub is_definition: bool,
}

#[derive(Debug, Clone)]
pub(super) struct PublicTermInfo {
    pub(super) sort: PublicSort,
    pub(super) metadata: FiniteSetTermMetadata,
}

impl PublicTermInfo {
    fn plain(sort: PublicSort) -> Self {
        Self {
            sort,
            metadata: FiniteSetTermMetadata::default(),
        }
    }
}

impl Context {
    /// Per-assertion finite-set provenance, aligned with [`Self::assertions`].
    #[must_use]
    pub fn assertion_finite_set_metadata(&self) -> &[PublicAssertionMetadata] {
        &self.assertion_finite_set_metadata
    }

    /// Public metadata aligned with soft constraints.
    #[must_use]
    pub fn soft_finite_set_metadata(&self) -> &[PublicAssertionMetadata] {
        &self.soft_finite_set_metadata
    }

    /// Public metadata aligned with optimization objectives.
    #[must_use]
    pub fn objective_finite_set_metadata(&self) -> &[PublicAssertionMetadata] {
        &self.objective_finite_set_metadata
    }

    /// Public signatures of all live declarations.
    #[must_use]
    pub fn public_symbol_signatures(&self) -> Vec<PublicSymbolSignature> {
        self.symbol_iter()
            .map(|(name, info)| PublicSymbolSignature {
                name: name.clone(),
                internal_name: self.symbol_identity_name(name, info).to_string(),
                arguments: info.public_arg_sorts.clone(),
                result: info.public_sort.clone(),
                is_arbitrary_constant: info.public_arg_sorts.is_empty()
                    && info.term.is_some()
                    && !self.fun_defs.contains_key(name),
                is_definition: self.fun_defs.contains_key(name),
            })
            .collect()
    }

    pub(super) fn elaborate_public_sort(&mut self, sort: &command::Sort) -> Result<PublicSort> {
        self.elaborate_public_sort_inner(sort, &HashMap::default())
    }

    pub(super) fn parsed_sort_contains_finite_set(&self, sort: &command::Sort) -> bool {
        match sort {
            command::Sort::Simple(name) => self
                .public_sort_defs
                .get(name)
                .is_some_and(PublicSort::contains_finite_set),
            command::Sort::Indexed(_, _) => false,
            command::Sort::Parameterized(name, parameters) => {
                if name == "FiniteSet"
                    || parameters
                        .iter()
                        .any(|parameter| self.parsed_sort_contains_finite_set(parameter))
                {
                    return true;
                }
                self.parametric_sort_defs
                    .get(name)
                    .is_some_and(|(_, body)| self.parsed_sort_contains_finite_set(body))
            }
        }
    }

    fn elaborate_public_sort_inner(
        &mut self,
        sort: &command::Sort,
        subst: &HashMap<String, PublicSort>,
    ) -> Result<PublicSort> {
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
            self.elaborate_public_sort_dispatch(sort, subst)
        })
    }

    fn elaborate_public_sort_dispatch(
        &mut self,
        sort: &command::Sort,
        subst: &HashMap<String, PublicSort>,
    ) -> Result<PublicSort> {
        match sort {
            command::Sort::Simple(name) => {
                if let Some(bound) = subst.get(name) {
                    return Ok(bound.clone());
                }
                if let Some(alias) = self.public_sort_defs.get(name) {
                    return Ok(alias.clone());
                }
                let engine_subst = public_engine_subst(subst)?;
                let engine = self.elaborate_sort_inner(sort, &engine_subst)?;
                Ok(PublicSort::from_engine(&engine))
            }
            command::Sort::Parameterized(name, parameters) => match name.as_str() {
                "Array" => {
                    expect_sort_arity(name, parameters, 2)?;
                    Ok(PublicSort::Array(
                        Box::new(self.elaborate_public_sort_inner(&parameters[0], subst)?),
                        Box::new(self.elaborate_public_sort_inner(&parameters[1], subst)?),
                    ))
                }
                "->" if self
                    .logic
                    .as_deref()
                    .is_none_or(|logic| matches!(logic, "HORN" | "ALL")) =>
                {
                    expect_sort_arity(name, parameters, 2)?;
                    Ok(PublicSort::Array(
                        Box::new(self.elaborate_public_sort_inner(&parameters[0], subst)?),
                        Box::new(self.elaborate_public_sort_inner(&parameters[1], subst)?),
                    ))
                }
                "Seq" => {
                    expect_sort_arity(name, parameters, 1)?;
                    Ok(PublicSort::Seq(Box::new(
                        self.elaborate_public_sort_inner(&parameters[0], subst)?,
                    )))
                }
                "Set" => {
                    expect_sort_arity(name, parameters, 1)?;
                    Ok(PublicSort::Array(
                        Box::new(self.elaborate_public_sort_inner(&parameters[0], subst)?),
                        Box::new(PublicSort::Core(Sort::Bool)),
                    ))
                }
                "FiniteSet" => {
                    expect_sort_arity(name, parameters, 1)?;
                    self.mark_uses_set();
                    Ok(PublicSort::FiniteSet(Box::new(
                        self.elaborate_public_sort_inner(&parameters[0], subst)?,
                    )))
                }
                "Multiset" => {
                    expect_sort_arity(name, parameters, 1)?;
                    Ok(PublicSort::Array(
                        Box::new(self.elaborate_public_sort_inner(&parameters[0], subst)?),
                        Box::new(PublicSort::Core(Sort::Int)),
                    ))
                }
                "Map" => {
                    expect_sort_arity(name, parameters, 2)?;
                    Ok(PublicSort::Array(
                        Box::new(self.elaborate_public_sort_inner(&parameters[0], subst)?),
                        Box::new(self.elaborate_public_sort_inner(&parameters[1], subst)?),
                    ))
                }
                other if self.parametric_sort_defs.contains_key(other) => {
                    let (parameter_names, body) = self
                        .parametric_sort_defs
                        .get(other)
                        .cloned()
                        .ok_or_else(|| ElaborateError::UnknownSort(other.to_string()))?;
                    if parameter_names.len() != parameters.len() {
                        return Err(ElaborateError::InvalidConstant(format!(
                            "{other} requires {} type parameters, got {}",
                            parameter_names.len(),
                            parameters.len()
                        )));
                    }
                    if self
                        .expanding_sort_synonyms
                        .iter()
                        .any(|active| active == other)
                    {
                        return Err(ElaborateError::InvalidConstant(format!(
                            "recursive sort synonym: {other}"
                        )));
                    }
                    let arguments = parameters
                        .iter()
                        .map(|parameter| self.elaborate_public_sort_inner(parameter, subst))
                        .collect::<Result<Vec<_>>>()?;
                    let inner = parameter_names.into_iter().zip(arguments).collect();
                    self.expanding_sort_synonyms.push(other.to_string());
                    let result = self.elaborate_public_sort_inner(&body, &inner);
                    self.expanding_sort_synonyms.pop();
                    result
                }
                other if self.parametric_datatypes.contains_key(other) => {
                    let public_arguments = parameters
                        .iter()
                        .map(|parameter| self.elaborate_public_sort_inner(parameter, subst))
                        .collect::<Result<Vec<_>>>()?;
                    if public_arguments.iter().any(PublicSort::contains_finite_set) {
                        return Err(ElaborateError::Unsupported(format!(
                            "datatype instantiation '{other}' with a FiniteSet argument is unsupported because member public sorts cannot be retained"
                        )));
                    }
                    let engine_subst = public_engine_subst(subst)?;
                    let engine = self.elaborate_sort_inner(sort, &engine_subst)?;
                    Ok(PublicSort::from_engine(&engine))
                }
                _ => {
                    let engine_subst = public_engine_subst(subst)?;
                    let engine = self.elaborate_sort_inner(sort, &engine_subst)?;
                    Ok(PublicSort::from_engine(&engine))
                }
            },
            command::Sort::Indexed(_, _) => {
                let engine_subst = public_engine_subst(subst)?;
                let engine = self.elaborate_sort_inner(sort, &engine_subst)?;
                Ok(PublicSort::from_engine(&engine))
            }
        }
    }

    pub(super) fn validate_public_assertion(
        &mut self,
        term: &ParsedTerm,
        engine_term: TermId,
    ) -> Result<PublicAssertionMetadata> {
        let info = self.public_term_info(term, &HashMap::default())?;
        if matches!(
            self.finite_set_typing_mode,
            super::FiniteSetTypingMode::Z3_5Strict
        ) {
            self.validate_strict_finite_set_retention_shape(term, &HashMap::default())?;
        }
        let root = if info.metadata.uses_finite_set || has_shared_set_occurrence(term) {
            Some(self.build_public_term_metadata(
                term,
                &HashMap::default(),
                &HashMap::default(),
                Some(engine_term),
                None,
            )?)
        } else {
            None
        };
        Ok(PublicAssertionMetadata {
            finite_sets: info.metadata,
            root,
        })
    }

    /// Reject parsed shapes whose lowered term identity cannot yet be paired
    /// with an exact occurrence tree for the Z3 5 public AST.
    ///
    /// `let` substitution, macro expansion, and binder/match bodies can replace
    /// a FiniteSet occurrence with a hash-consed Array backing before the
    /// adapter sees it. Publishing that backing would make `Z3_get_*` report a
    /// misleading Array declaration or sort. Binder-only terms remain valid:
    /// `(forall ((s (FiniteSet Int))) true)` has an exact public bound sort and
    /// a body with no FiniteSet occurrence to reconstruct.
    fn validate_strict_finite_set_retention_shape(
        &mut self,
        term: &ParsedTerm,
        env: &HashMap<String, PublicSort>,
    ) -> Result<()> {
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || match term {
            ParsedTerm::Let(bindings, body) => {
                if self.parsed_term_contains_finite_set_occurrence(term, env)? {
                    return Err(unretained_finite_set_shape("let"));
                }
                let mut body_env = env.clone();
                for (name, value) in bindings {
                    self.validate_strict_finite_set_retention_shape(value, env)?;
                    let value_sort = self.public_term_info(value, env)?.sort;
                    body_env.insert(name.clone(), value_sort);
                }
                self.validate_strict_finite_set_retention_shape(body, &body_env)
            }
            ParsedTerm::Forall(bindings, body)
            | ParsedTerm::Exists(bindings, body)
            | ParsedTerm::Lambda(bindings, body) => {
                let mut body_env = env.clone();
                for (name, sort) in bindings {
                    body_env.insert(name.clone(), self.elaborate_public_sort(sort)?);
                }
                if self.parsed_term_contains_finite_set_occurrence(body, &body_env)? {
                    return Err(unretained_finite_set_shape("quantifier/lambda body"));
                }
                self.validate_strict_finite_set_retention_shape(body, &body_env)
            }
            ParsedTerm::Match(scrutinee, cases) => {
                if self.parsed_term_contains_finite_set_occurrence(term, env)? {
                    return Err(unretained_finite_set_shape("match"));
                }
                self.validate_strict_finite_set_retention_shape(scrutinee, env)?;
                for (_, body) in cases {
                    self.validate_strict_finite_set_retention_shape(body, env)?;
                }
                Ok(())
            }
            ParsedTerm::App(name, arguments) => {
                if self.defined_function_contains_finite_set(name)? {
                    return Err(unretained_finite_set_shape("define-fun expansion"));
                }
                for argument in arguments {
                    self.validate_strict_finite_set_retention_shape(argument, env)?;
                }
                Ok(())
            }
            ParsedTerm::IndexedApp(_, _, arguments) => {
                for argument in arguments {
                    self.validate_strict_finite_set_retention_shape(argument, env)?;
                }
                Ok(())
            }
            ParsedTerm::QualifiedApp(identifier, _, arguments) => {
                if let Some(name) = identifier.as_symbol() {
                    if self.defined_function_contains_finite_set(name)? {
                        return Err(unretained_finite_set_shape("define-fun expansion"));
                    }
                }
                for argument in arguments {
                    self.validate_strict_finite_set_retention_shape(argument, env)?;
                }
                Ok(())
            }
            ParsedTerm::Annotated(body, annotations) => {
                if has_unretained_finite_set_trigger(annotations, env) {
                    return Err(unretained_finite_set_shape(
                        "quantifier pattern/no-pattern annotation",
                    ));
                }
                self.validate_strict_finite_set_retention_shape(body, env)
            }
            ParsedTerm::Symbol(name) => {
                if self.defined_function_contains_finite_set(name)? {
                    Err(unretained_finite_set_shape("define-fun expansion"))
                } else {
                    Ok(())
                }
            }
            ParsedTerm::Const(_) => Ok(()),
        })
    }

    fn parsed_term_contains_finite_set_occurrence(
        &mut self,
        term: &ParsedTerm,
        env: &HashMap<String, PublicSort>,
    ) -> Result<bool> {
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
            let info = self.public_term_info(term, env)?;
            if info.sort.contains_finite_set() || info.metadata.uses_finite_set {
                return Ok(true);
            }
            match term {
                ParsedTerm::App(_, arguments)
                | ParsedTerm::IndexedApp(_, _, arguments)
                | ParsedTerm::QualifiedApp(_, _, arguments) => {
                    for argument in arguments {
                        if self.parsed_term_contains_finite_set_occurrence(argument, env)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                ParsedTerm::Let(bindings, body) => {
                    let mut body_env = env.clone();
                    for (name, value) in bindings {
                        if self.parsed_term_contains_finite_set_occurrence(value, env)? {
                            return Ok(true);
                        }
                        let value_sort = self.public_term_info(value, env)?.sort;
                        body_env.insert(name.clone(), value_sort);
                    }
                    self.parsed_term_contains_finite_set_occurrence(body, &body_env)
                }
                ParsedTerm::Forall(bindings, body)
                | ParsedTerm::Exists(bindings, body)
                | ParsedTerm::Lambda(bindings, body) => {
                    let mut body_env = env.clone();
                    for (name, sort) in bindings {
                        body_env.insert(name.clone(), self.elaborate_public_sort(sort)?);
                    }
                    self.parsed_term_contains_finite_set_occurrence(body, &body_env)
                }
                ParsedTerm::Annotated(body, annotations) => {
                    if has_unretained_finite_set_trigger(annotations, env) {
                        return Ok(true);
                    }
                    self.parsed_term_contains_finite_set_occurrence(body, env)
                }
                ParsedTerm::Match(scrutinee, cases) => {
                    if self.parsed_term_contains_finite_set_occurrence(scrutinee, env)? {
                        return Ok(true);
                    }
                    for (_, body) in cases {
                        if self.parsed_term_contains_finite_set_occurrence(body, env)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                ParsedTerm::Const(_) | ParsedTerm::Symbol(_) => Ok(false),
            }
        })
    }

    fn defined_function_contains_finite_set(&mut self, name: &str) -> Result<bool> {
        let Some((parameters, _, body)) = self.fun_defs.get(name).cloned() else {
            return Ok(false);
        };
        let Some(symbol) = self.symbols.get(name) else {
            return Ok(false);
        };
        let public_arguments = symbol.public_arg_sorts.clone();
        let public_result = symbol.public_sort.clone();
        if public_result.contains_finite_set()
            || public_arguments.iter().any(PublicSort::contains_finite_set)
        {
            return Ok(true);
        }
        let env = parameters
            .into_iter()
            .map(|(name, _)| name)
            .zip(public_arguments)
            .collect();
        self.parsed_term_contains_finite_set_occurrence(&body, &env)
    }

    fn build_public_term_metadata(
        &mut self,
        term: &ParsedTerm,
        public_env: &HashMap<String, PublicSort>,
        engine_env: &HashMap<String, TermId>,
        known_engine_term: Option<TermId>,
        expected_sort: Option<&PublicSort>,
    ) -> Result<PublicTermMetadata> {
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
            let info = self.public_term_info(term, public_env)?;
            let engine_term = match known_engine_term {
                Some(term) => term,
                None => self.elaborate_term(term, engine_env)?,
            };
            let public_sort = resolve_occurrence_sort(info.sort, expected_sort);
            let finite_set_op = match term {
                ParsedTerm::App(name, _) => finite_set_op(name),
                ParsedTerm::QualifiedApp(QualifiedIdentifier::Symbol(name), _, _)
                    if name == "set.empty" =>
                {
                    Some(FiniteSetOp::Empty)
                }
                _ => None,
            };
            let public_bound_sorts = match term {
                ParsedTerm::Forall(bindings, _)
                | ParsedTerm::Exists(bindings, _)
                | ParsedTerm::Lambda(bindings, _) => bindings
                    .iter()
                    .map(|(_, sort)| self.elaborate_public_sort(sort))
                    .collect::<Result<Vec<_>>>()?,
                _ => Vec::new(),
            };
            let arguments = match term {
                ParsedTerm::App(name, arguments) => {
                    let argument_infos = arguments
                        .iter()
                        .map(|argument| self.public_term_info(argument, public_env))
                        .collect::<Result<Vec<_>>>()?;
                    let expected = self.application_argument_expectations(
                        name,
                        &argument_infos,
                        &public_sort,
                    )?;
                    arguments
                        .iter()
                        .zip(expected.iter())
                        .map(|(argument, expected)| {
                            self.build_public_term_metadata(
                                argument,
                                public_env,
                                engine_env,
                                None,
                                expected.as_ref(),
                            )
                        })
                        .collect::<Result<Vec<_>>>()?
                }
                ParsedTerm::IndexedApp(_, _, arguments)
                | ParsedTerm::QualifiedApp(_, _, arguments) => arguments
                    .iter()
                    .map(|argument| {
                        self.build_public_term_metadata(
                            argument, public_env, engine_env, None, None,
                        )
                    })
                    .collect::<Result<Vec<_>>>()?,
                ParsedTerm::Let(bindings, body) => {
                    let mut nodes = Vec::with_capacity(bindings.len() + 1);
                    let mut public_values = Vec::with_capacity(bindings.len());
                    let mut engine_values = Vec::with_capacity(bindings.len());
                    for (name, value) in bindings {
                        let node = self.build_public_term_metadata(
                            value, public_env, engine_env, None, None,
                        )?;
                        public_values.push((name.clone(), node.public_sort.clone()));
                        engine_values.push((name.clone(), node.engine_term));
                        nodes.push(node);
                    }
                    let mut body_public_env = public_env.clone();
                    body_public_env.extend(public_values);
                    let mut body_engine_env = engine_env.clone();
                    body_engine_env.extend(engine_values);
                    nodes.push(self.build_public_term_metadata(
                        body,
                        &body_public_env,
                        &body_engine_env,
                        None,
                        None,
                    )?);
                    nodes
                }
                // Bound-variable engine identities are freshly allocated during
                // elaboration and cannot be reconstructed after the root was
                // built. The aggregate binder flag makes adapters fail closed;
                // do not publish misleading child-to-root identities.
                ParsedTerm::Forall(_, _)
                | ParsedTerm::Exists(_, _)
                | ParsedTerm::Lambda(_, _)
                | ParsedTerm::Match(_, _) => Vec::new(),
                ParsedTerm::Annotated(body, _) => {
                    vec![self.build_public_term_metadata(body, public_env, engine_env, None, None)?]
                }
                ParsedTerm::Const(_) | ParsedTerm::Symbol(_) => Vec::new(),
            };
            Ok(PublicTermMetadata {
                engine_term,
                public_sort,
                finite_set_op,
                public_bound_sorts,
                arguments,
            })
        })
    }

    pub(super) fn validate_public_definition(
        &mut self,
        parameters: &[(String, command::Sort)],
        result: &command::Sort,
        body: &ParsedTerm,
    ) -> Result<()> {
        let mut env = HashMap::default();
        for (name, sort) in parameters {
            env.insert(name.clone(), self.elaborate_public_sort(sort)?);
        }
        let expected = self.elaborate_public_sort(result)?;
        let actual_info = self.public_term_info(body, &env)?;
        if matches!(
            self.finite_set_typing_mode,
            super::FiniteSetTypingMode::Z3_5Strict
        ) && (expected.contains_finite_set()
            || env.values().any(PublicSort::contains_finite_set)
            || self.parsed_term_contains_finite_set_occurrence(body, &env)?)
        {
            return Err(unretained_finite_set_shape("define-fun body"));
        }
        let actual = actual_info.sort;
        require_compatible("define-fun result", &expected, &actual)
    }

    pub(super) fn validate_public_term(&mut self, term: &ParsedTerm) -> Result<()> {
        self.public_term_info(term, &HashMap::default()).map(|_| ())
    }

    fn public_term_info(
        &mut self,
        term: &ParsedTerm,
        env: &HashMap<String, PublicSort>,
    ) -> Result<PublicTermInfo> {
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
            self.public_term_info_dispatch(term, env)
        })
    }

    fn public_term_info_dispatch(
        &mut self,
        term: &ParsedTerm,
        env: &HashMap<String, PublicSort>,
    ) -> Result<PublicTermInfo> {
        match term {
            ParsedTerm::Const(constant) => Ok(PublicTermInfo::plain(match constant {
                ParsedConstant::True | ParsedConstant::False => PublicSort::Core(Sort::Bool),
                ParsedConstant::Numeral(_) => PublicSort::Core(Sort::Int),
                ParsedConstant::Decimal(_) => PublicSort::Core(Sort::Real),
                ParsedConstant::Hexadecimal(value) => {
                    PublicSort::Core(Sort::bitvec((value.len() * 4) as u32))
                }
                ParsedConstant::Binary(value) => PublicSort::Core(Sort::bitvec(value.len() as u32)),
                ParsedConstant::String(_) => PublicSort::Core(Sort::String),
            })),
            ParsedTerm::Symbol(name) => {
                if let Some(sort) = env.get(name) {
                    return Ok(PublicTermInfo::plain(sort.clone()));
                }
                if let Some(info) = self.symbols.get(name) {
                    let mut metadata = FiniteSetTermMetadata::default();
                    if info.public_sort.contains_finite_set() {
                        metadata.uses_finite_set = true;
                        metadata.has_arbitrary_value = true;
                    }
                    return Ok(PublicTermInfo {
                        sort: info.public_sort.clone(),
                        metadata,
                    });
                }
                Ok(PublicTermInfo::plain(symbol_literal_sort(name)))
            }
            ParsedTerm::App(name, arguments) => {
                let arguments = arguments
                    .iter()
                    .map(|argument| self.public_term_info(argument, env))
                    .collect::<Result<Vec<_>>>()?;
                self.public_application(name, arguments)
            }
            ParsedTerm::IndexedApp(name, indices, arguments) => {
                let arguments = arguments
                    .iter()
                    .map(|argument| self.public_term_info(argument, env))
                    .collect::<Result<Vec<_>>>()?;
                let mut metadata = merged_metadata(&arguments);
                // Both spellings are accepted by the indexed-term elaborator
                // (`indexed.rs`, `name == "Char" || name == "char"`) and by z3.
                // Tracking only `Char` here left `(_ char #x61)` with an
                // engine-checked sort, so `char.to_int` rejected its own
                // literal as sort-incompatible.
                if (name == "Char" || name == "char") && arguments.is_empty() && indices.len() == 1
                {
                    return Ok(PublicTermInfo {
                        sort: PublicSort::Core(Sort::Char),
                        metadata,
                    });
                }
                if name == "as-array" && arguments.is_empty() {
                    if let Some(target) = indices.first().and_then(command::Index::as_symbol) {
                        if let Some(info) = self.symbols.get(target) {
                            if info.public_arg_sorts.len() == 1 {
                                let sort = PublicSort::Array(
                                    Box::new(info.public_arg_sorts[0].clone()),
                                    Box::new(info.public_sort.clone()),
                                );
                                metadata.uses_finite_set |= sort.contains_finite_set();
                                metadata.has_arbitrary_value |= sort.contains_finite_set();
                                return Ok(PublicTermInfo { sort, metadata });
                            }
                        }
                    }
                }
                if name == "map" {
                    let target = indices.first().and_then(command::Index::as_symbol);
                    let Some(target) = target else {
                        if arguments
                            .iter()
                            .any(|argument| argument.sort.contains_finite_set())
                        {
                            return Err(ElaborateError::Unsupported(
                                "(_ map ...): FiniteSet-bearing map target is unresolved"
                                    .to_string(),
                            ));
                        }
                        return Ok(PublicTermInfo {
                            sort: PublicSort::Unknown,
                            metadata,
                        });
                    };
                    let Some(info) = self.symbols.get(target) else {
                        if arguments
                            .iter()
                            .any(|argument| argument.sort.contains_finite_set())
                        {
                            return Err(ElaborateError::UndefinedSymbol(target.to_string()));
                        }
                        return Ok(PublicTermInfo {
                            sort: PublicSort::Unknown,
                            metadata,
                        });
                    };
                    if info.public_arg_sorts.len() != arguments.len() {
                        return Err(ElaborateError::IllSorted(format!(
                            "(_ map {target}): expected {} arrays, got {}",
                            info.public_arg_sorts.len(),
                            arguments.len()
                        )));
                    }
                    let mut index_sort: Option<PublicSort> = None;
                    for ((argument, expected_element), position) in arguments
                        .iter()
                        .zip(info.public_arg_sorts.iter())
                        .zip(0usize..)
                    {
                        let PublicSort::Array(index, element) = &argument.sort else {
                            if argument.sort.contains_finite_set()
                                || expected_element.contains_finite_set()
                            {
                                return Err(ElaborateError::IllSorted(format!(
                                    "(_ map {target}): argument {position} is not an Array"
                                )));
                            }
                            return Ok(PublicTermInfo {
                                sort: PublicSort::Unknown,
                                metadata,
                            });
                        };
                        require_compatible("(_ map ...)", expected_element, element)?;
                        if let Some(common) = &index_sort {
                            require_compatible("(_ map ...) index", common, index)?;
                        } else {
                            index_sort = Some(index.as_ref().clone());
                        }
                    }
                    let sort = PublicSort::Array(
                        Box::new(index_sort.unwrap_or(PublicSort::Unknown)),
                        Box::new(info.public_sort.clone()),
                    );
                    metadata.uses_finite_set |= sort.contains_finite_set();
                    metadata.has_arbitrary_value |= sort.contains_finite_set();
                    return Ok(PublicTermInfo { sort, metadata });
                }
                if matches!(
                    name.as_str(),
                    "at-most" | "at-least" | "pble" | "pbge" | "pbeq"
                ) {
                    return Ok(PublicTermInfo {
                        sort: PublicSort::Core(Sort::Bool),
                        metadata,
                    });
                }
                if arguments
                    .iter()
                    .any(|argument| argument.sort.contains_finite_set())
                {
                    return Err(ElaborateError::Unsupported(format!(
                        "indexed application '{name}' has no public FiniteSet sort rule"
                    )));
                }
                Ok(PublicTermInfo {
                    sort: PublicSort::Unknown,
                    metadata,
                })
            }
            ParsedTerm::QualifiedApp(identifier, parsed_sort, arguments) => {
                let arguments = arguments
                    .iter()
                    .map(|argument| self.public_term_info(argument, env))
                    .collect::<Result<Vec<_>>>()?;
                let mut metadata = merged_metadata(&arguments);
                let qualified_sort = self.elaborate_public_sort(parsed_sort)?;
                let name = identifier.as_symbol();
                if name == Some("set.empty") {
                    if matches!(
                        self.finite_set_typing_mode,
                        super::FiniteSetTypingMode::Z3_5Strict
                    ) && !matches!(qualified_sort, PublicSort::FiniteSet(_))
                    {
                        return Err(ElaborateError::IllSorted(format!(
                            "set.empty: Z3 5.0.0 expects FiniteSet, got {qualified_sort}"
                        )));
                    }
                    metadata.uses_finite_set |= qualified_sort.contains_finite_set();
                    return Ok(PublicTermInfo {
                        sort: qualified_sort,
                        metadata,
                    });
                }
                if name == Some("map.empty") {
                    let PublicSort::Array(_, value) = &qualified_sort else {
                        return Err(ElaborateError::IllSorted(format!(
                            "map.empty: expected Map/Array, got {qualified_sort}"
                        )));
                    };
                    metadata.uses_finite_set |= qualified_sort.contains_finite_set();
                    // The map lowering materializes a fresh default value.
                    // Although the official map API masks it behind an empty
                    // domain, the Array carrier also permits `select`, so a
                    // FiniteSet-bearing default is an observable arbitrary
                    // value and must activate the SAT-only provenance gate.
                    metadata.has_arbitrary_value |= value.contains_finite_set();
                    return Ok(PublicTermInfo {
                        sort: qualified_sort,
                        metadata,
                    });
                }
                if name == Some("const") {
                    let PublicSort::Array(_, element) = &qualified_sort else {
                        if qualified_sort.contains_finite_set() {
                            return Err(ElaborateError::IllSorted(format!(
                                "const: expected Array, got {qualified_sort}"
                            )));
                        }
                        metadata.uses_finite_set |= qualified_sort.contains_finite_set();
                        return Ok(PublicTermInfo {
                            sort: qualified_sort,
                            metadata,
                        });
                    };
                    if let Some(value) = arguments.first() {
                        require_compatible("const array value", element, &value.sort)?;
                    }
                    metadata.uses_finite_set |= qualified_sort.contains_finite_set();
                    return Ok(PublicTermInfo {
                        sort: qualified_sort,
                        metadata,
                    });
                }
                if let Some(name) = name {
                    if let Some(info) =
                        self.public_declared_candidate(name, &arguments, Some(&qualified_sort))
                    {
                        metadata.uses_finite_set |= info.public_sort.contains_finite_set();
                        metadata.has_arbitrary_value |= info.public_sort.contains_finite_set();
                        return Ok(PublicTermInfo {
                            sort: info.public_sort,
                            metadata,
                        });
                    }
                    if self.has_symbol_binding(name) && qualified_sort.contains_finite_set() {
                        return Err(surface_mismatch(&qualified_sort, &PublicSort::Unknown));
                    }
                }
                if qualified_sort.contains_finite_set() {
                    return Err(ElaborateError::Unsupported(format!(
                        "qualified application returning {qualified_sort} has no public FiniteSet provenance rule"
                    )));
                }
                metadata.uses_finite_set |= qualified_sort.contains_finite_set();
                Ok(PublicTermInfo {
                    sort: qualified_sort,
                    metadata,
                })
            }
            ParsedTerm::Let(bindings, body) => {
                let mut values = Vec::with_capacity(bindings.len());
                let mut metadata = FiniteSetTermMetadata::default();
                for (name, value) in bindings {
                    let info = self.public_term_info(value, env)?;
                    metadata.merge(info.metadata);
                    values.push((name.clone(), info.sort));
                }
                let mut body_env = env.clone();
                body_env.extend(values);
                let mut result = self.public_term_info(body, &body_env)?;
                result.metadata.merge(metadata);
                Ok(result)
            }
            ParsedTerm::Forall(bindings, body) | ParsedTerm::Exists(bindings, body) => {
                let mut body_env = env.clone();
                let mut metadata = FiniteSetTermMetadata::default();
                for (name, parsed_sort) in bindings {
                    let sort = self.elaborate_public_sort(parsed_sort)?;
                    if sort.contains_finite_set() {
                        metadata.uses_finite_set = true;
                        metadata.has_finite_set_binder = true;
                    }
                    body_env.insert(name.clone(), sort);
                }
                let body = self.public_term_info(body, &body_env)?;
                metadata.merge(body.metadata);
                Ok(PublicTermInfo {
                    sort: PublicSort::Core(Sort::Bool),
                    metadata,
                })
            }
            ParsedTerm::Lambda(bindings, body) => {
                let mut body_env = env.clone();
                let mut binder_sorts = Vec::with_capacity(bindings.len());
                let mut metadata = FiniteSetTermMetadata::default();
                for (name, parsed_sort) in bindings {
                    let sort = self.elaborate_public_sort(parsed_sort)?;
                    if sort.contains_finite_set() {
                        metadata.uses_finite_set = true;
                        metadata.has_finite_set_binder = true;
                    }
                    body_env.insert(name.clone(), sort.clone());
                    binder_sorts.push(sort);
                }
                let body = self.public_term_info(body, &body_env)?;
                metadata.merge(body.metadata);
                let sort = binder_sorts
                    .into_iter()
                    .rev()
                    .fold(body.sort, |range, domain| {
                        PublicSort::Array(Box::new(domain), Box::new(range))
                    });
                Ok(PublicTermInfo { sort, metadata })
            }
            ParsedTerm::Annotated(body, _) => self.public_term_info(body, env),
            ParsedTerm::Match(scrutinee, cases) => {
                let scrutinee = self.public_term_info(scrutinee, env)?;
                let mut metadata = scrutinee.metadata;
                let mut result_sort: Option<PublicSort> = None;
                for (_, body) in cases {
                    let body = self.public_term_info(body, env)?;
                    metadata.merge(body.metadata);
                    result_sort = Some(match result_sort {
                        Some(previous) => joined_sort(&previous, &body.sort)
                            .ok_or_else(|| surface_mismatch(&previous, &body.sort))?,
                        None => body.sort,
                    });
                }
                Ok(PublicTermInfo {
                    sort: result_sort.unwrap_or(PublicSort::Unknown),
                    metadata,
                })
            }
        }
    }

    fn public_application(
        &self,
        name: &str,
        arguments: Vec<PublicTermInfo>,
    ) -> Result<PublicTermInfo> {
        let mut metadata = merged_metadata(&arguments);
        let sorts: Vec<PublicSort> = arguments.iter().map(|info| info.sort.clone()).collect();
        let result = match name {
            "=" | "distinct" => {
                for pair in sorts.windows(2) {
                    require_compatible(name, &pair[0], &pair[1])?;
                }
                PublicSort::Core(Sort::Bool)
            }
            "ite" if sorts.len() == 3 => {
                require_compatible("ite", &sorts[1], &sorts[2])?;
                joined_sort(&sorts[1], &sorts[2])
                    .ok_or_else(|| surface_mismatch(&sorts[1], &sorts[2]))?
            }
            "select" if sorts.len() == 2 => match &sorts[0] {
                PublicSort::FiniteSet(_) => return Err(finite_set_array_error("select")),
                PublicSort::Array(index, element) => {
                    require_compatible("select index", index, &sorts[1])?;
                    element.as_ref().clone()
                }
                PublicSort::AmbiguousSet(element) => {
                    require_compatible("select index", element, &sorts[1])?;
                    PublicSort::Core(Sort::Bool)
                }
                _ => PublicSort::Unknown,
            },
            "default" if sorts.len() == 1 => match &sorts[0] {
                PublicSort::FiniteSet(_) => return Err(finite_set_array_error("default")),
                PublicSort::Array(_, element) => element.as_ref().clone(),
                PublicSort::AmbiguousSet(_) => PublicSort::Core(Sort::Bool),
                _ => PublicSort::Unknown,
            },
            "store" if sorts.len() == 3 => match &sorts[0] {
                PublicSort::FiniteSet(_) => return Err(finite_set_array_error("store")),
                PublicSort::Array(index, element) => {
                    require_compatible("store index", index, &sorts[1])?;
                    require_compatible("store value", element, &sorts[2])?;
                    sorts[0].clone()
                }
                PublicSort::AmbiguousSet(element) => {
                    require_compatible("store index", element, &sorts[1])?;
                    require_compatible("store value", &PublicSort::Core(Sort::Bool), &sorts[2])?;
                    PublicSort::Array(
                        Box::new(element.as_ref().clone()),
                        Box::new(PublicSort::Core(Sort::Bool)),
                    )
                }
                _ => PublicSort::Unknown,
            },
            "set.singleton" if sorts.len() == 1 => match self.finite_set_typing_mode {
                super::FiniteSetTypingMode::LegacyCompatible => {
                    PublicSort::AmbiguousSet(Box::new(sorts[0].clone()))
                }
                super::FiniteSetTypingMode::Z3_5Strict => {
                    metadata.uses_finite_set = true;
                    PublicSort::FiniteSet(Box::new(sorts[0].clone()))
                }
            },
            "set.in" if sorts.len() == 2 => {
                let basis = require_finite_set(name, &sorts[1])?;
                require_compatible(name, basis, &sorts[0])?;
                metadata.uses_finite_set = true;
                PublicSort::Core(Sort::Bool)
            }
            "set.size" if sorts.len() == 1 => {
                require_finite_set(name, &sorts[0])?;
                metadata.uses_finite_set = true;
                PublicSort::Core(Sort::Int)
            }
            "set.intersect" | "set.difference" if !sorts.is_empty() => {
                let basis = require_matching_finite_sets(name, &sorts)?;
                metadata.uses_finite_set = true;
                PublicSort::FiniteSet(Box::new(basis))
            }
            "set.range" if sorts.len() == 2 => {
                metadata.uses_finite_set = true;
                PublicSort::FiniteSet(Box::new(PublicSort::Core(Sort::Int)))
            }
            "set.map" if sorts.len() == 2 => {
                let basis = require_finite_set(name, &sorts[1])?;
                let image = match &sorts[0] {
                    PublicSort::Array(domain, image) => {
                        require_compatible(name, domain, basis)?;
                        image.as_ref().clone()
                    }
                    other => {
                        return Err(ElaborateError::IllSorted(format!(
                            "{name}: expected Array function, got {other}"
                        )));
                    }
                };
                metadata.uses_finite_set = true;
                metadata.has_finite_set_binder |=
                    basis.contains_finite_set() || image.contains_finite_set();
                PublicSort::FiniteSet(Box::new(image))
            }
            "set.filter" if sorts.len() == 2 => {
                let basis = require_finite_set(name, &sorts[1])?.clone();
                let PublicSort::Array(domain, range) = &sorts[0] else {
                    return Err(ElaborateError::IllSorted(format!(
                        "{name}: expected Array predicate, got {}",
                        sorts[0]
                    )));
                };
                require_compatible(name, domain, &basis)?;
                require_compatible(name, range, &PublicSort::Core(Sort::Bool))?;
                metadata.uses_finite_set = true;
                metadata.has_finite_set_binder |= basis.contains_finite_set();
                PublicSort::FiniteSet(Box::new(basis))
            }
            "set.member" if sorts.len() == 2 => {
                let basis = require_legacy_set(name, &sorts[1])?;
                require_compatible(name, &basis, &sorts[0])?;
                PublicSort::Core(Sort::Bool)
            }
            "set.card" if sorts.len() == 1 => {
                require_legacy_set(name, &sorts[0])?;
                PublicSort::Core(Sort::Int)
            }
            "set.insert" | "set.remove" if sorts.len() == 2 => {
                let basis = require_legacy_set(name, &sorts[1])?;
                require_compatible(name, &basis, &sorts[0])?;
                PublicSort::Array(Box::new(basis), Box::new(PublicSort::Core(Sort::Bool)))
            }
            "set.inter" | "set.minus" | "set.complement" if !sorts.is_empty() => {
                let basis = require_matching_legacy_sets(name, &sorts)?;
                PublicSort::Array(Box::new(basis), Box::new(PublicSort::Core(Sort::Bool)))
            }
            "set.union" if !sorts.is_empty() => {
                if matches!(
                    self.finite_set_typing_mode,
                    super::FiniteSetTypingMode::Z3_5Strict
                ) {
                    metadata.uses_finite_set = true;
                    PublicSort::FiniteSet(Box::new(require_matching_finite_sets(name, &sorts)?))
                } else {
                    shared_set_result(name, &sorts)?
                }
            }
            "set.subset" if !sorts.is_empty() => {
                if matches!(
                    self.finite_set_typing_mode,
                    super::FiniteSetTypingMode::Z3_5Strict
                ) {
                    require_matching_finite_sets(name, &sorts)?;
                    metadata.uses_finite_set = true;
                } else {
                    shared_set_result(name, &sorts)?;
                }
                metadata.has_finite_set_binder |= sorts
                    .iter()
                    .filter_map(collection_basis)
                    .any(PublicSort::contains_finite_set);
                PublicSort::Core(Sort::Bool)
            }
            "char.<=" if sorts.len() == 2 => {
                let char_sort = PublicSort::Core(Sort::Char);
                require_compatible(name, &char_sort, &sorts[0])?;
                require_compatible(name, &char_sort, &sorts[1])?;
                PublicSort::Core(Sort::Bool)
            }
            "char.to_int" if sorts.len() == 1 => {
                require_compatible(name, &PublicSort::Core(Sort::Char), &sorts[0])?;
                PublicSort::Core(Sort::Int)
            }
            "char.is_digit" if sorts.len() == 1 => {
                require_compatible(name, &PublicSort::Core(Sort::Char), &sorts[0])?;
                PublicSort::Core(Sort::Bool)
            }
            "char.to_bv" if sorts.len() == 1 => {
                require_compatible(name, &PublicSort::Core(Sort::Char), &sorts[0])?;
                PublicSort::Core(Sort::bitvec(18))
            }
            "char.from_bv" if sorts.len() == 1 => {
                require_compatible(name, &PublicSort::Core(Sort::bitvec(18)), &sorts[0])?;
                PublicSort::Core(Sort::Char)
            }
            "seq.unit" if sorts.len() == 1 => PublicSort::Seq(Box::new(sorts[0].clone())),
            "seq.++" if !sorts.is_empty() => {
                require_sequence_operand(name, &sorts[0])?;
                for sort in &sorts[1..] {
                    require_sequence_operand(name, sort)?;
                    require_compatible(name, &sorts[0], sort)?;
                }
                sorts[0].clone()
            }
            "seq.extract" if sorts.len() == 3 => {
                require_sequence_operand(name, &sorts[0])?;
                require_public_int(name, &sorts[1])?;
                require_public_int(name, &sorts[2])?;
                sorts[0].clone()
            }
            "seq.at" if sorts.len() == 2 => {
                require_sequence_operand(name, &sorts[0])?;
                require_public_int(name, &sorts[1])?;
                sorts[0].clone()
            }
            "seq.replace" | "seq.replace_all" if sorts.len() == 3 => {
                require_sequence_operand(name, &sorts[0])?;
                require_sequence_operand(name, &sorts[1])?;
                require_sequence_operand(name, &sorts[2])?;
                require_compatible(name, &sorts[0], &sorts[1])?;
                require_compatible(name, &sorts[0], &sorts[2])?;
                sorts[0].clone()
            }
            "seq.nth" if sorts.len() == 2 => {
                require_public_int(name, &sorts[1])?;
                match &sorts[0] {
                    PublicSort::Seq(element) => element.as_ref().clone(),
                    PublicSort::Core(Sort::String) => PublicSort::Core(Sort::Char),
                    other => {
                        return Err(ElaborateError::IllSorted(format!(
                            "{name}: expected Seq/String, got {other}"
                        )));
                    }
                }
            }
            "seq.len" if sorts.len() == 1 => {
                require_sequence_operand(name, &sorts[0])?;
                PublicSort::Core(Sort::Int)
            }
            "seq.map" if sorts.len() == 2 => {
                let PublicSort::Array(domain, image) = &sorts[0] else {
                    return Err(ElaborateError::IllSorted(format!(
                        "{name}: expected Array function, got {}",
                        sorts[0]
                    )));
                };
                let PublicSort::Seq(element) = &sorts[1] else {
                    return Err(ElaborateError::IllSorted(format!(
                        "{name}: expected Seq operand, got {}",
                        sorts[1]
                    )));
                };
                require_compatible(name, domain, element)?;
                PublicSort::Seq(Box::new(image.as_ref().clone()))
            }
            "seq.mapi" if sorts.len() == 3 => {
                let PublicSort::Array(index, inner) = &sorts[0] else {
                    return Err(ElaborateError::IllSorted(format!(
                        "{name}: expected two-argument Array function, got {}",
                        sorts[0]
                    )));
                };
                require_public_int(name, index)?;
                let PublicSort::Array(domain, image) = inner.as_ref() else {
                    return Err(ElaborateError::IllSorted(format!(
                        "{name}: expected two-argument Array function, got {}",
                        sorts[0]
                    )));
                };
                require_public_int(name, &sorts[1])?;
                let PublicSort::Seq(element) = &sorts[2] else {
                    return Err(ElaborateError::IllSorted(format!(
                        "{name}: expected Seq operand, got {}",
                        sorts[2]
                    )));
                };
                require_compatible(name, domain, element)?;
                PublicSort::Seq(Box::new(image.as_ref().clone()))
            }
            "seq.indexof" | "seq.last_indexof" if sorts.len() >= 2 => {
                require_sequence_operand(name, &sorts[0])?;
                require_sequence_operand(name, &sorts[1])?;
                require_compatible(name, &sorts[0], &sorts[1])?;
                if let Some(offset) = sorts.get(2) {
                    require_public_int(name, offset)?;
                }
                PublicSort::Core(Sort::Int)
            }
            "seq.contains" | "seq.prefixof" | "seq.suffixof" if sorts.len() == 2 => {
                require_sequence_operand(name, &sorts[0])?;
                require_sequence_operand(name, &sorts[1])?;
                require_compatible(name, &sorts[0], &sorts[1])?;
                PublicSort::Core(Sort::Bool)
            }
            "seq.in.re" | "seq.in_re" if sorts.iter().any(PublicSort::contains_finite_set) => {
                return Err(ElaborateError::Unsupported(format!(
                    "{name}: regular-language public identity over FiniteSet elements is unavailable"
                )));
            }
            "and" | "or" | "not" | "xor" | "=>" | "implies" | "<" | "<=" | ">" | ">="
            | "is_int" => PublicSort::Core(Sort::Bool),
            "to_real" if sorts.len() == 1 => PublicSort::Core(Sort::Real),
            "to_int" if sorts.len() == 1 => PublicSort::Core(Sort::Int),
            "+" | "-" | "*" | "min" | "max" if !sorts.is_empty() => joined_numeric_sort(&sorts),
            "~" if sorts.len() == 1 => {
                if self.int_real_coercions() && matches!(&sorts[0], PublicSort::Core(Sort::Bool)) {
                    PublicSort::Core(Sort::Int)
                } else {
                    joined_numeric_sort(&sorts)
                }
            }
            "/" if sorts.len() >= 2 => PublicSort::Core(Sort::Real),
            "div" | "mod" | "rem" if !sorts.is_empty() => PublicSort::Core(Sort::Int),
            "abs" if sorts.len() == 1 => sorts[0].clone(),
            _ => {
                if let Some(info) = self.public_declared_candidate(name, &arguments, None) {
                    if info.public_sort.contains_finite_set() {
                        metadata.uses_finite_set = true;
                        metadata.has_arbitrary_value = true;
                    }
                    info.public_sort
                } else if sorts.iter().any(PublicSort::contains_finite_set) {
                    return Err(ElaborateError::Unsupported(format!(
                        "{name}: public sort inference for a FiniteSet-bearing application is unavailable"
                    )));
                } else {
                    PublicSort::Unknown
                }
            }
        };
        metadata.uses_finite_set |= result.contains_finite_set();
        Ok(PublicTermInfo {
            sort: result,
            metadata,
        })
    }

    fn application_argument_expectations(
        &self,
        name: &str,
        arguments: &[PublicTermInfo],
        result: &PublicSort,
    ) -> Result<Vec<Option<PublicSort>>> {
        let sorts: Vec<PublicSort> = arguments.iter().map(|info| info.sort.clone()).collect();
        let mut expected = vec![None; sorts.len()];
        match name {
            "=" | "distinct" if !sorts.is_empty() => {
                let mut common = sorts[0].clone();
                for sort in &sorts[1..] {
                    common = joined_sort(&common, sort)
                        .ok_or_else(|| surface_mismatch(&common, sort))?;
                }
                common = default_ambiguous_set(common);
                expected.fill(Some(common));
            }
            "ite" if sorts.len() == 3 => {
                let common = default_ambiguous_set(
                    joined_sort(&sorts[1], &sorts[2])
                        .ok_or_else(|| surface_mismatch(&sorts[1], &sorts[2]))?,
                );
                expected[1] = Some(common.clone());
                expected[2] = Some(common);
            }
            "select" | "default" if !sorts.is_empty() => {
                expected[0] = Some(default_legacy_set_if_ambiguous(sorts[0].clone()));
            }
            "store" if sorts.len() == 3 => {
                let array = default_legacy_set_if_ambiguous(sorts[0].clone());
                if let PublicSort::Array(index, element) = &array {
                    expected[1] = Some(index.as_ref().clone());
                    expected[2] = Some(element.as_ref().clone());
                }
                expected[0] = Some(array);
            }
            "set.singleton" if sorts.len() == 1 => {
                expected[0] = collection_basis(result).cloned();
            }
            "set.in" if sorts.len() == 2 => {
                let collection = PublicSort::FiniteSet(Box::new(sorts[0].clone()));
                expected[1] = Some(collection);
            }
            "set.size" if sorts.len() == 1 => {
                expected[0] = Some(PublicSort::FiniteSet(Box::new(PublicSort::Unknown)));
            }
            "set.intersect" | "set.difference" if !sorts.is_empty() => {
                let collection = default_finite_set_if_ambiguous(result.clone());
                expected.fill(Some(collection));
            }
            "set.map" if sorts.len() == 2 => {
                let basis = require_finite_set(name, &sorts[1])?.clone();
                expected[0] = Some(PublicSort::Array(
                    Box::new(basis.clone()),
                    Box::new(
                        collection_basis(result)
                            .cloned()
                            .unwrap_or(PublicSort::Unknown),
                    ),
                ));
                expected[1] = Some(PublicSort::FiniteSet(Box::new(basis)));
            }
            "set.filter" if sorts.len() == 2 => {
                let basis = require_finite_set(name, &sorts[1])?.clone();
                expected[0] = Some(PublicSort::Array(
                    Box::new(basis.clone()),
                    Box::new(PublicSort::Core(Sort::Bool)),
                ));
                expected[1] = Some(PublicSort::FiniteSet(Box::new(basis)));
            }
            "set.member" if sorts.len() == 2 => {
                expected[1] = Some(PublicSort::Array(
                    Box::new(sorts[0].clone()),
                    Box::new(PublicSort::Core(Sort::Bool)),
                ));
            }
            "set.card" if sorts.len() == 1 => {
                expected[0] = Some(PublicSort::Array(
                    Box::new(PublicSort::Unknown),
                    Box::new(PublicSort::Core(Sort::Bool)),
                ));
            }
            "set.insert" | "set.remove" if sorts.len() == 2 => {
                expected[1] = Some(PublicSort::Array(
                    Box::new(sorts[0].clone()),
                    Box::new(PublicSort::Core(Sort::Bool)),
                ));
            }
            "set.inter" | "set.minus" | "set.complement" if !sorts.is_empty() => {
                expected.fill(Some(default_legacy_set_if_ambiguous(result.clone())));
            }
            "set.union" if !sorts.is_empty() => {
                expected.fill(Some(default_ambiguous_set(result.clone())));
            }
            "set.subset" if !sorts.is_empty() => {
                let shared = default_ambiguous_set(shared_set_result(name, &sorts)?);
                expected.fill(Some(shared));
            }
            "seq.map" if sorts.len() == 2 => {
                if let PublicSort::Seq(image) = result {
                    if let PublicSort::Array(domain, _) = &sorts[0] {
                        expected[0] = Some(PublicSort::Array(
                            Box::new(domain.as_ref().clone()),
                            Box::new(image.as_ref().clone()),
                        ));
                        expected[1] = Some(PublicSort::Seq(Box::new(domain.as_ref().clone())));
                    }
                }
            }
            "seq.mapi" if sorts.len() == 3 => {
                if let PublicSort::Seq(image) = result {
                    if let PublicSort::Array(index, inner) = &sorts[0] {
                        if let PublicSort::Array(domain, _) = inner.as_ref() {
                            expected[0] = Some(PublicSort::Array(
                                Box::new(index.as_ref().clone()),
                                Box::new(PublicSort::Array(
                                    Box::new(domain.as_ref().clone()),
                                    Box::new(image.as_ref().clone()),
                                )),
                            ));
                            expected[1] = Some(PublicSort::Core(Sort::Int));
                            expected[2] = Some(PublicSort::Seq(Box::new(domain.as_ref().clone())));
                        }
                    }
                }
            }
            _ => {
                if let Some(info) = self.public_declared_candidate(name, arguments, Some(result)) {
                    for (slot, sort) in expected.iter_mut().zip(info.public_arg_sorts) {
                        *slot = Some(sort);
                    }
                }
            }
        }
        Ok(expected)
    }

    fn public_declared_candidate(
        &self,
        name: &str,
        arguments: &[PublicTermInfo],
        result: Option<&PublicSort>,
    ) -> Option<SymbolInfo> {
        let matches = |info: &&SymbolInfo| {
            info.public_arg_sorts.len() == arguments.len()
                && info
                    .public_arg_sorts
                    .iter()
                    .zip(arguments)
                    .all(|(expected, actual)| public_compatible(expected, &actual.sort))
                && result.is_none_or(|expected| public_compatible(expected, &info.public_sort))
        };
        let mut candidates: Vec<&SymbolInfo> = Vec::new();
        if let Some(overloads) = self.overloaded_symbols.get(name) {
            candidates.extend(overloads);
        } else if let Some(info) = self.symbols.get(name) {
            candidates.push(info);
        }
        candidates.into_iter().find(matches).cloned()
    }
}

fn expect_sort_arity(name: &str, parameters: &[command::Sort], expected: usize) -> Result<()> {
    if parameters.len() == expected {
        Ok(())
    } else {
        Err(ElaborateError::InvalidConstant(format!(
            "{name} requires {expected} type parameters"
        )))
    }
}

fn public_engine_subst(subst: &HashMap<String, PublicSort>) -> Result<HashMap<String, Sort>> {
    subst
        .iter()
        .map(|(name, sort)| {
            sort.engine_sort()
                .map(|sort| (name.clone(), sort))
                .ok_or_else(|| {
                    ElaborateError::Unsupported(format!(
                        "cannot lower unresolved public sort parameter {name}"
                    ))
                })
        })
        .collect()
}

fn symbol_literal_sort(name: &str) -> PublicSort {
    if name.starts_with('-') {
        if name.contains('.') {
            return PublicSort::Core(Sort::Real);
        }
        return PublicSort::Core(Sort::Int);
    }
    if matches!(name, "re.none" | "re.all" | "re.allchar") {
        return PublicSort::Core(Sort::RegLan);
    }
    PublicSort::Unknown
}

fn finite_set_op(name: &str) -> Option<FiniteSetOp> {
    Some(match name {
        "set.singleton" => FiniteSetOp::Singleton,
        "set.union" => FiniteSetOp::Union,
        "set.intersect" => FiniteSetOp::Intersect,
        "set.difference" => FiniteSetOp::Difference,
        "set.in" => FiniteSetOp::In,
        "set.size" => FiniteSetOp::Size,
        "set.subset" => FiniteSetOp::Subset,
        "set.map" => FiniteSetOp::Map,
        "set.filter" => FiniteSetOp::Filter,
        "set.range" => FiniteSetOp::Range,
        _ => return None,
    })
}

fn unretained_finite_set_shape(shape: &str) -> ElaborateError {
    ElaborateError::Unsupported(format!(
        "Z3 5.0.0 FiniteSet public AST retention for {shape} is not yet available"
    ))
}

fn has_unretained_finite_set_trigger(
    annotations: &[(String, SExpr)],
    env: &HashMap<String, PublicSort>,
) -> bool {
    annotations.iter().any(|(keyword, value)| {
        matches!(keyword.as_str(), ":pattern" | ":no-pattern")
            && (env.values().any(PublicSort::contains_finite_set)
                || sexpr_contains_finite_set_surface(value))
    })
}

fn sexpr_contains_finite_set_surface(sexpr: &SExpr) -> bool {
    match sexpr {
        SExpr::Symbol(name) => {
            name == "FiniteSet"
                || matches!(
                    name.as_str(),
                    "set.empty"
                        | "set.singleton"
                        | "set.union"
                        | "set.intersect"
                        | "set.difference"
                        | "set.in"
                        | "set.size"
                        | "set.subset"
                        | "set.map"
                        | "set.filter"
                        | "set.range"
                )
        }
        SExpr::List(items) => items.iter().any(sexpr_contains_finite_set_surface),
        SExpr::Keyword(_)
        | SExpr::Numeral(_)
        | SExpr::Decimal(_)
        | SExpr::Hexadecimal(_)
        | SExpr::Binary(_)
        | SExpr::String(_)
        | SExpr::True
        | SExpr::False => false,
    }
}

fn has_shared_set_occurrence(term: &ParsedTerm) -> bool {
    match term {
        ParsedTerm::App(name, arguments) => {
            matches!(name.as_str(), "set.singleton" | "set.union" | "set.subset")
                || arguments.iter().any(has_shared_set_occurrence)
        }
        ParsedTerm::IndexedApp(_, _, arguments) => arguments.iter().any(has_shared_set_occurrence),
        ParsedTerm::QualifiedApp(identifier, _, arguments) => {
            identifier.as_symbol() == Some("set.empty")
                || arguments.iter().any(has_shared_set_occurrence)
        }
        ParsedTerm::Let(bindings, body) => {
            bindings
                .iter()
                .any(|(_, value)| has_shared_set_occurrence(value))
                || has_shared_set_occurrence(body)
        }
        ParsedTerm::Forall(_, body)
        | ParsedTerm::Exists(_, body)
        | ParsedTerm::Lambda(_, body)
        | ParsedTerm::Annotated(body, _) => has_shared_set_occurrence(body),
        ParsedTerm::Match(scrutinee, cases) => {
            has_shared_set_occurrence(scrutinee)
                || cases
                    .iter()
                    .any(|(_, body)| has_shared_set_occurrence(body))
        }
        ParsedTerm::Const(_) | ParsedTerm::Symbol(_) => false,
    }
}

fn merged_metadata(arguments: &[PublicTermInfo]) -> FiniteSetTermMetadata {
    let mut metadata = FiniteSetTermMetadata::default();
    for argument in arguments {
        metadata.merge(argument.metadata);
    }
    metadata
}

fn public_compatible(expected: &PublicSort, actual: &PublicSort) -> bool {
    if !expected.contains_finite_set()
        && !actual.contains_finite_set()
        && !expected.contains_char()
        && !actual.contains_char()
    {
        return true;
    }
    match (expected, actual) {
        (PublicSort::FiniteSet(left), PublicSort::FiniteSet(right))
        | (PublicSort::Array(left, _), PublicSort::AmbiguousSet(right))
        | (PublicSort::AmbiguousSet(left), PublicSort::Array(right, _))
        | (PublicSort::FiniteSet(left), PublicSort::AmbiguousSet(right))
        | (PublicSort::AmbiguousSet(left), PublicSort::FiniteSet(right))
        | (PublicSort::AmbiguousSet(left), PublicSort::AmbiguousSet(right)) => {
            public_compatible(left, right)
        }
        (
            PublicSort::Array(left_index, left_element),
            PublicSort::Array(right_index, right_element),
        ) => {
            public_compatible(left_index, right_index)
                && public_compatible(left_element, right_element)
        }
        (PublicSort::Seq(left), PublicSort::Seq(right)) => public_compatible(left, right),
        (PublicSort::Core(left), PublicSort::Core(right)) => left == right,
        (PublicSort::Unknown, other) | (other, PublicSort::Unknown) => {
            !other.contains_finite_set() && !other.contains_char()
        }
        _ => false,
    }
}

fn joined_sort(left: &PublicSort, right: &PublicSort) -> Option<PublicSort> {
    if !public_compatible(left, right) {
        return None;
    }
    match (left, right) {
        (PublicSort::Core(Sort::Int), PublicSort::Core(Sort::Real))
        | (PublicSort::Core(Sort::Real), PublicSort::Core(Sort::Int)) => {
            Some(PublicSort::Core(Sort::Real))
        }
        (PublicSort::AmbiguousSet(_), other) | (other, PublicSort::AmbiguousSet(_)) => {
            Some(other.clone())
        }
        (PublicSort::Unknown, other) | (other, PublicSort::Unknown)
            if !other.contains_finite_set() =>
        {
            Some(other.clone())
        }
        _ => Some(left.clone()),
    }
}

fn joined_numeric_sort(sorts: &[PublicSort]) -> PublicSort {
    if sorts
        .iter()
        .any(|sort| matches!(sort, PublicSort::Core(Sort::Real)))
    {
        PublicSort::Core(Sort::Real)
    } else if sorts
        .iter()
        .all(|sort| matches!(sort, PublicSort::Core(Sort::Int)))
    {
        PublicSort::Core(Sort::Int)
    } else {
        // The engine elaborator has already checked and assigned the concrete
        // non-FiniteSet arithmetic sort. Unknown here is preferable to
        // fabricating a public identity for an extension operator.
        PublicSort::Unknown
    }
}

fn resolve_occurrence_sort(sort: PublicSort, expected: Option<&PublicSort>) -> PublicSort {
    match (sort, expected) {
        (PublicSort::AmbiguousSet(element), Some(PublicSort::FiniteSet(expected_element))) => {
            PublicSort::FiniteSet(Box::new(resolve_occurrence_sort(
                *element,
                Some(expected_element),
            )))
        }
        (
            PublicSort::AmbiguousSet(element),
            Some(PublicSort::Array(expected_element, expected_range)),
        ) if matches!(expected_range.as_ref(), PublicSort::Core(Sort::Bool)) => PublicSort::Array(
            Box::new(resolve_occurrence_sort(*element, Some(expected_element))),
            Box::new(PublicSort::Core(Sort::Bool)),
        ),
        (PublicSort::Array(index, element), Some(PublicSort::Array(ei, ee))) => PublicSort::Array(
            Box::new(resolve_occurrence_sort(*index, Some(ei))),
            Box::new(resolve_occurrence_sort(*element, Some(ee))),
        ),
        (PublicSort::FiniteSet(element), Some(PublicSort::FiniteSet(expected_element))) => {
            PublicSort::FiniteSet(Box::new(resolve_occurrence_sort(
                *element,
                Some(expected_element),
            )))
        }
        (PublicSort::Seq(element), Some(PublicSort::Seq(expected_element))) => PublicSort::Seq(
            Box::new(resolve_occurrence_sort(*element, Some(expected_element))),
        ),
        (sort, _) => sort,
    }
}

fn default_ambiguous_set(sort: PublicSort) -> PublicSort {
    match sort {
        PublicSort::AmbiguousSet(element) => PublicSort::FiniteSet(element),
        other => other,
    }
}

fn default_finite_set_if_ambiguous(sort: PublicSort) -> PublicSort {
    default_ambiguous_set(sort)
}

fn default_legacy_set_if_ambiguous(sort: PublicSort) -> PublicSort {
    match sort {
        PublicSort::AmbiguousSet(element) => {
            PublicSort::Array(element, Box::new(PublicSort::Core(Sort::Bool)))
        }
        other => other,
    }
}

fn collection_basis(sort: &PublicSort) -> Option<&PublicSort> {
    match sort {
        PublicSort::FiniteSet(element) | PublicSort::AmbiguousSet(element) => Some(element),
        other => other.legacy_set_basis(),
    }
}

fn require_sequence_operand(operation: &str, sort: &PublicSort) -> Result<()> {
    if matches!(sort, PublicSort::Seq(_) | PublicSort::Core(Sort::String)) {
        Ok(())
    } else {
        Err(ElaborateError::IllSorted(format!(
            "{operation}: expected Seq/String, got {sort}"
        )))
    }
}

fn require_public_int(operation: &str, sort: &PublicSort) -> Result<()> {
    if matches!(sort, PublicSort::Core(Sort::Int) | PublicSort::Unknown) {
        Ok(())
    } else {
        Err(ElaborateError::IllSorted(format!(
            "{operation}: expected Int index, got {sort}"
        )))
    }
}

fn require_compatible(operation: &str, expected: &PublicSort, actual: &PublicSort) -> Result<()> {
    if public_compatible(expected, actual) {
        Ok(())
    } else {
        Err(ElaborateError::IllSorted(format!(
            "{operation}: public sorts {expected} and {actual} are incompatible"
        )))
    }
}

fn surface_mismatch(expected: &PublicSort, actual: &PublicSort) -> ElaborateError {
    ElaborateError::SortMismatch {
        expected: expected.to_string(),
        actual: actual.to_string(),
    }
}

fn finite_set_array_error(operation: &str) -> ElaborateError {
    ElaborateError::IllSorted(format!(
        "{operation}: FiniteSet is not an Array sort in Z3 5.0.0"
    ))
}

fn require_finite_set<'a>(operation: &str, sort: &'a PublicSort) -> Result<&'a PublicSort> {
    match sort {
        PublicSort::FiniteSet(element) | PublicSort::AmbiguousSet(element) => Ok(element),
        other => Err(ElaborateError::IllSorted(format!(
            "{operation}: expected FiniteSet, got {other}"
        ))),
    }
}

fn require_matching_finite_sets(operation: &str, sorts: &[PublicSort]) -> Result<PublicSort> {
    let first = sorts
        .first()
        .ok_or_else(|| ElaborateError::InvalidConstant(format!("{operation} needs arguments")))?;
    let basis = require_finite_set(operation, first)?.clone();
    for sort in &sorts[1..] {
        let other = require_finite_set(operation, sort)?;
        require_compatible(operation, &basis, other)?;
    }
    Ok(basis)
}

fn require_legacy_set(operation: &str, sort: &PublicSort) -> Result<PublicSort> {
    match sort {
        PublicSort::FiniteSet(_) => Err(ElaborateError::IllSorted(format!(
            "{operation}: legacy Set operator does not accept FiniteSet"
        ))),
        PublicSort::AmbiguousSet(element) => Ok(element.as_ref().clone()),
        PublicSort::Array(index, element)
            if matches!(element.as_ref(), PublicSort::Core(Sort::Bool)) =>
        {
            Ok(index.as_ref().clone())
        }
        PublicSort::Unknown => Ok(PublicSort::Unknown),
        other => Err(ElaborateError::IllSorted(format!(
            "{operation}: expected legacy Set/Array, got {other}"
        ))),
    }
}

fn require_matching_legacy_sets(operation: &str, sorts: &[PublicSort]) -> Result<PublicSort> {
    let first = sorts
        .first()
        .ok_or_else(|| ElaborateError::InvalidConstant(format!("{operation} needs arguments")))?;
    let basis = require_legacy_set(operation, first)?;
    for sort in &sorts[1..] {
        let other = require_legacy_set(operation, sort)?;
        require_compatible(operation, &basis, &other)?;
    }
    Ok(basis)
}

fn shared_set_result(operation: &str, sorts: &[PublicSort]) -> Result<PublicSort> {
    let mut finite_basis: Option<PublicSort> = None;
    let mut legacy_basis: Option<PublicSort> = None;
    let mut ambiguous_basis: Option<PublicSort> = None;
    for sort in sorts {
        match sort {
            PublicSort::FiniteSet(element) => {
                if legacy_basis.is_some() {
                    return Err(ElaborateError::IllSorted(format!(
                        "{operation}: cannot mix FiniteSet and legacy Set/Array"
                    )));
                }
                if let Some(existing) = &finite_basis {
                    require_compatible(operation, existing, element)?;
                } else {
                    finite_basis = Some(element.as_ref().clone());
                }
            }
            PublicSort::AmbiguousSet(element) => {
                if let Some(existing) = &ambiguous_basis {
                    require_compatible(operation, existing, element)?;
                } else {
                    ambiguous_basis = Some(element.as_ref().clone());
                }
            }
            other if other.legacy_set_basis().is_some() || matches!(other, PublicSort::Unknown) => {
                if finite_basis.is_some() {
                    return Err(ElaborateError::IllSorted(format!(
                        "{operation}: cannot mix FiniteSet and legacy Set/Array"
                    )));
                }
                let basis = other
                    .legacy_set_basis()
                    .cloned()
                    .unwrap_or(PublicSort::Unknown);
                if let Some(existing) = &legacy_basis {
                    require_compatible(operation, existing, &basis)?;
                } else {
                    legacy_basis = Some(basis);
                }
            }
            other => {
                return Err(ElaborateError::IllSorted(format!(
                    "{operation}: expected Set/FiniteSet, got {other}"
                )));
            }
        }
    }
    if let Some(basis) = finite_basis {
        if let Some(ambiguous) = ambiguous_basis {
            require_compatible(operation, &basis, &ambiguous)?;
        }
        Ok(PublicSort::FiniteSet(Box::new(basis)))
    } else if let Some(basis) = legacy_basis {
        if let Some(ambiguous) = ambiguous_basis {
            require_compatible(operation, &basis, &ambiguous)?;
        }
        Ok(PublicSort::Array(
            Box::new(basis),
            Box::new(PublicSort::Core(Sort::Bool)),
        ))
    } else {
        Ok(PublicSort::AmbiguousSet(Box::new(
            ambiguous_basis.unwrap_or(PublicSort::Unknown),
        )))
    }
}
