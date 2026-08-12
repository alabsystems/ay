// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Language-boundary enforcement for the 25 official SMT-LIB 2.7 logics.
//!
//! SMT-LIB logic declarations define a language, not merely a solver hint.
//! AY historically treated them as upper bounds, which meant that a script
//! could silently use quantifiers, theories, free symbols, or nonlinear forms
//! excluded by its declared logic.  The ordinary SMT-LIB CLI opts into this
//! module; the explicit Z3 compatibility mode keeps Z3's permissive overlay.

use ay_core::Sort as CoreSort;
use num_bigint::BigUint;

use crate::command::{
    Command, Constant, Index, QualifiedIdentifier, Sort as ParsedSort, Term as ParsedTerm,
};

use super::{Context, ElaborateError, Result};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ExpansionPolicy {
    ConstantsOnly,
    FreeSortsAndConstants,
    FreeSortsAndFunctions,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ArithmeticPolicy {
    None,
    IntegerDifference,
    UfIntegerDifference,
    LinearInteger,
    NonlinearIntegerWithoutPower,
    FullInteger,
    RealDifference,
    LinearReal,
    NonlinearReal,
    MixedLinear,
    MixedNonlinear,
}

impl ArithmeticPolicy {
    const fn has_integers(self) -> bool {
        matches!(
            self,
            Self::IntegerDifference
                | Self::UfIntegerDifference
                | Self::LinearInteger
                | Self::NonlinearIntegerWithoutPower
                | Self::FullInteger
                | Self::MixedLinear
                | Self::MixedNonlinear
        )
    }

    const fn has_reals(self) -> bool {
        matches!(
            self,
            Self::RealDifference
                | Self::LinearReal
                | Self::NonlinearReal
                | Self::MixedLinear
                | Self::MixedNonlinear
        )
    }

    const fn permits_nonlinear_integer(self) -> bool {
        matches!(
            self,
            Self::NonlinearIntegerWithoutPower | Self::FullInteger | Self::MixedNonlinear
        )
    }

    const fn permits_integer_division_family(self) -> bool {
        self.permits_nonlinear_integer()
    }

    const fn permits_integer_power(self) -> bool {
        matches!(self, Self::FullInteger)
    }

    const fn permits_nonlinear_real(self) -> bool {
        matches!(self, Self::NonlinearReal | Self::MixedNonlinear)
    }

    const fn is_difference(self) -> bool {
        matches!(
            self,
            Self::IntegerDifference | Self::UfIntegerDifference | Self::RealDifference
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ArrayPolicy {
    None,
    Any,
    IntToInt,
    IntToRealOrNested,
    BitVectorToBitVector,
}

#[derive(Clone, Copy, Debug)]
struct LogicPolicy {
    quantifiers: bool,
    expansion: ExpansionPolicy,
    arithmetic: ArithmeticPolicy,
    arrays: ArrayPolicy,
    bitvectors: bool,
}

impl LogicPolicy {
    const fn new(
        quantifiers: bool,
        expansion: ExpansionPolicy,
        arithmetic: ArithmeticPolicy,
        arrays: ArrayPolicy,
        bitvectors: bool,
    ) -> Self {
        Self {
            quantifiers,
            expansion,
            arithmetic,
            arrays,
            bitvectors,
        }
    }

    fn official(name: &str) -> Option<Self> {
        use ArithmeticPolicy as A;
        use ArrayPolicy as R;
        use ExpansionPolicy as E;
        Some(match name {
            "AUFLIA" => Self::new(
                true,
                E::FreeSortsAndFunctions,
                A::LinearInteger,
                R::IntToInt,
                false,
            ),
            "AUFLIRA" => Self::new(
                true,
                E::FreeSortsAndFunctions,
                A::MixedLinear,
                R::IntToRealOrNested,
                false,
            ),
            "AUFNIRA" => Self::new(
                true,
                E::FreeSortsAndFunctions,
                A::MixedNonlinear,
                R::Any,
                false,
            ),
            "LIA" => Self::new(true, E::ConstantsOnly, A::LinearInteger, R::None, false),
            "LRA" => Self::new(true, E::ConstantsOnly, A::LinearReal, R::None, false),
            "QF_ABV" => Self::new(
                false,
                E::ConstantsOnly,
                A::None,
                R::BitVectorToBitVector,
                true,
            ),
            "QF_AUFBV" => Self::new(
                false,
                E::FreeSortsAndFunctions,
                A::None,
                R::BitVectorToBitVector,
                true,
            ),
            "QF_AUFLIA" => Self::new(
                false,
                E::FreeSortsAndFunctions,
                A::LinearInteger,
                R::IntToInt,
                false,
            ),
            "QF_AX" => Self::new(false, E::FreeSortsAndConstants, A::None, R::Any, false),
            "QF_BV" => Self::new(false, E::ConstantsOnly, A::None, R::None, true),
            "QF_EIA" => Self::new(false, E::ConstantsOnly, A::FullInteger, R::None, false),
            "QF_IDL" => Self::new(
                false,
                E::ConstantsOnly,
                A::IntegerDifference,
                R::None,
                false,
            ),
            "QF_LIA" => Self::new(false, E::ConstantsOnly, A::LinearInteger, R::None, false),
            "QF_LRA" => Self::new(false, E::ConstantsOnly, A::LinearReal, R::None, false),
            "QF_NIA" => Self::new(
                false,
                E::ConstantsOnly,
                A::NonlinearIntegerWithoutPower,
                R::None,
                false,
            ),
            "QF_NRA" => Self::new(false, E::ConstantsOnly, A::NonlinearReal, R::None, false),
            "QF_RDL" => Self::new(false, E::ConstantsOnly, A::RealDifference, R::None, false),
            "QF_UF" => Self::new(false, E::FreeSortsAndFunctions, A::None, R::None, false),
            "QF_UFBV" => Self::new(false, E::FreeSortsAndFunctions, A::None, R::None, true),
            "QF_UFIDL" => Self::new(
                false,
                E::FreeSortsAndFunctions,
                A::UfIntegerDifference,
                R::None,
                false,
            ),
            "QF_UFLIA" => Self::new(
                false,
                E::FreeSortsAndFunctions,
                A::LinearInteger,
                R::None,
                false,
            ),
            "QF_UFLRA" => Self::new(
                false,
                E::FreeSortsAndFunctions,
                A::LinearReal,
                R::None,
                false,
            ),
            "QF_UFNRA" => Self::new(
                false,
                E::FreeSortsAndFunctions,
                A::NonlinearReal,
                R::None,
                false,
            ),
            "UFLRA" => Self::new(
                true,
                E::FreeSortsAndFunctions,
                A::LinearReal,
                R::None,
                false,
            ),
            "UFNIA" => Self::new(
                true,
                E::FreeSortsAndFunctions,
                A::NonlinearIntegerWithoutPower,
                R::None,
                false,
            ),
            _ => return None,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SortShape {
    Bool,
    Int,
    Real,
    BitVector,
    Array(Box<Self>, Box<Self>),
    Other,
}

impl Context {
    /// Whether the current declaration environment includes integer
    /// arithmetic for the Bool-to-Int coercion used by Z3 arithmetic apps.
    /// Null logic and Z3 extension logics use the global registry; an official
    /// SMT-LIB real-only/non-arithmetic logic does not acquire Int operations
    /// merely because coercions are enabled.
    pub(super) fn logic_allows_bool_to_int_coercion(&self) -> bool {
        let Some(policy) = self.logic.as_deref().and_then(LogicPolicy::official) else {
            return true;
        };
        policy.arithmetic.has_integers()
    }

    /// Enforce the SMT-LIB execution-mode preconditions that are visible from
    /// frontend state.  `Context` owns the start/assert boundary (whether a
    /// logic has been selected); result-specific sat/unsat inspection remains
    /// in `Executor`, which owns the last decision.
    pub(super) fn validate_command_execution_mode(&self, command: &Command) -> Result<()> {
        // Checked BEFORE the strict-compliance escape, because the pinned oracle
        // rejects a second `set-logic` too — this one is not SMT-LIB pedantry
        // that z3 waives, it is behaviour z3 shares:
        //
        //   (set-logic ALL) (set-logic QF_UF)
        //     z3: (error "line 2 column 11: the logic has already been set")
        //
        // It previously rode along inside the strict gate, so turning that gate
        // off by default silently took this with it and ay accepted the second
        // `set-logic` in silence. Message matches z3's wording exactly.
        // Keyed on the ORIGIN of the logic, not merely on its presence. An API
        // constructor installs a logic without going through the command
        // stream, and z3 does not count that as a `set-logic`: `SolverFor(L)`
        // followed by a parsed script containing `(set-logic M)` is accepted by
        // z3 even when `M != L`. Two `(set-logic ...)` in ONE parsed stream
        // still error, which is what the CLI contract needs.
        if self.logic_set_by_command && matches!(command, Command::SetLogic(_)) {
            return Err(ElaborateError::Unsupported(
                "the logic has already been set".to_string(),
            ));
        }

        if !self.strict_logic_compliance {
            return Ok(());
        }

        let in_start_mode = self.logic.is_none();
        if in_start_mode {
            let allowed = matches!(
                command,
                Command::SetLogic(_)
                    | Command::SetOption(..)
                    | Command::SetOptionAttribute(_)
                    | Command::SetInfo(..)
                    | Command::SetInfoAttribute(_)
                    | Command::Echo(_)
                    | Command::Exit
                    | Command::GetInfo(_)
                    | Command::GetOption(_)
                    | Command::Reset
                    | Command::ResetAssertions
            );
            if !allowed {
                return execution_mode_violation(command, "start");
            }
        } else if self.logic_set_by_command && matches!(command, Command::SetLogic(_)) {
            // Same origin rule under strict compliance, so strict mode does not
            // reproduce the divergence the permissive path just fixed.
            return execution_mode_violation(command, "assert/sat/unsat");
        }

        if let Command::SetOption(keyword, _) | Command::SetOptionAttribute(keyword) = command {
            let key = keyword.trim_start_matches(':');
            if !in_start_mode && is_start_only_option(key) {
                return Err(ElaborateError::Unsupported(format!(
                    "option :{key} can be set only in start mode"
                )));
            }
        }
        Ok(())
    }

    pub(super) fn validate_command_against_declared_logic(&self, command: &Command) -> Result<()> {
        if !self.strict_logic_compliance || matches!(command, Command::SetLogic(_)) {
            return Ok(());
        }
        let Some(logic) = self.logic.as_deref() else {
            return Ok(());
        };
        let Some(policy) = LogicPolicy::official(logic) else {
            return Ok(());
        };
        self.validate_logic_command(logic, policy, command)
    }

    fn validate_logic_command(
        &self,
        logic: &str,
        policy: LogicPolicy,
        command: &Command,
    ) -> Result<()> {
        match command {
            Command::DeclareSort(_, _) if policy.expansion == ExpansionPolicy::ConstantsOnly => {
                return logic_violation(logic, "free sort declarations are excluded");
            }
            Command::DeclareSort(_, _) | Command::DeclareSortParameter(_) => {}
            Command::DefineSort(_, parameters, sort) => {
                self.validate_logic_sort(logic, policy, sort, parameters)?;
            }
            Command::DeclareDatatype(..) | Command::DeclareDatatypes(..) => {
                return logic_violation(logic, "the datatype theory is excluded");
            }
            Command::DeclareConst(_, sort) => {
                self.validate_logic_sort(logic, policy, sort, &[])?;
            }
            Command::DeclareFun(_, arguments, result) => {
                if !arguments.is_empty()
                    && policy.expansion != ExpansionPolicy::FreeSortsAndFunctions
                {
                    return logic_violation(logic, "free function declarations are excluded");
                }
                for sort in arguments {
                    self.validate_logic_sort(logic, policy, sort, &[])?;
                }
                self.validate_logic_sort(logic, policy, result, &[])?;
            }
            Command::DefineFun(_, parameters, result, body)
            | Command::DefineFunRec(_, parameters, result, body) => {
                let bound = parameters
                    .iter()
                    .map(|(name, _)| name.clone())
                    .collect::<Vec<_>>();
                for (_, sort) in parameters {
                    self.validate_logic_sort(logic, policy, sort, &[])?;
                }
                self.validate_logic_sort(logic, policy, result, &[])?;
                self.validate_logic_term(logic, policy, body, &bound)?;
            }
            Command::DefineFunsRec(declarations, bodies) => {
                for ((_name, parameters, result), body) in declarations.iter().zip(bodies) {
                    let bound = parameters
                        .iter()
                        .map(|(name, _)| name.clone())
                        .collect::<Vec<_>>();
                    for (_, sort) in parameters {
                        self.validate_logic_sort(logic, policy, sort, &[])?;
                    }
                    self.validate_logic_sort(logic, policy, result, &[])?;
                    self.validate_logic_term(logic, policy, body, &bound)?;
                }
            }
            Command::Assert(term)
            | Command::Display(term, _)
            | Command::DebugSet(_, term, _)
            | Command::Simplify(term)
            | Command::Eval(term)
            | Command::Maximize(term)
            | Command::Minimize(term)
            | Command::SygusConstraint(term)
            | Command::Rule(term)
            | Command::Query(term) => {
                self.validate_logic_term(logic, policy, term, &[])?;
            }
            Command::AssertSoft { term, .. } => {
                self.validate_logic_term(logic, policy, term, &[])?;
            }
            Command::CheckSatAssuming(terms) => {
                for term in terms {
                    self.validate_logic_term(logic, policy, term, &[])?;
                }
            }
            Command::GetValue(terms) => {
                for (_, term) in terms {
                    self.validate_logic_term(logic, policy, term, &[])?;
                }
            }
            Command::GetConsequences(assumptions, variables) => {
                for term in assumptions.iter().chain(variables) {
                    self.validate_logic_term(logic, policy, term, &[])?;
                }
            }
            Command::GetInterpolant(left, right) | Command::ComputeInterpolant(left, right) => {
                self.validate_logic_term(logic, policy, left, &[])?;
                self.validate_logic_term(logic, policy, right, &[])?;
            }
            Command::GetAbduct(_, goal) => {
                self.validate_logic_term(logic, policy, goal, &[])?;
            }
            _ => {}
        }
        Ok(())
    }

    fn validate_logic_sort(
        &self,
        logic: &str,
        policy: LogicPolicy,
        sort: &ParsedSort,
        bound_sort_parameters: &[String],
    ) -> Result<()> {
        match sort {
            ParsedSort::Simple(name) if bound_sort_parameters.contains(name) => Ok(()),
            ParsedSort::Simple(name) if self.sort_parameters.contains(name) => Ok(()),
            ParsedSort::Simple(name) if name == "Bool" => Ok(()),
            ParsedSort::Simple(name) if name == "Int" => {
                if policy.arithmetic.has_integers() {
                    Ok(())
                } else {
                    logic_violation(logic, "the integer theory is excluded")
                }
            }
            ParsedSort::Simple(name) if name == "Real" => {
                if policy.arithmetic.has_reals() {
                    Ok(())
                } else {
                    logic_violation(logic, "the real theory is excluded")
                }
            }
            ParsedSort::Simple(name) => {
                if let Some(core) = self.sort_defs.get(name) {
                    Self::validate_core_sort(logic, policy, core)
                } else if is_non_registry_theory_sort(name) {
                    logic_violation(logic, "an excluded theory sort is used")
                } else if policy.expansion == ExpansionPolicy::ConstantsOnly {
                    logic_violation(logic, "free sorts are excluded")
                } else {
                    Ok(())
                }
            }
            ParsedSort::Indexed(name, indices) if name == "BitVec" => {
                if !policy.bitvectors {
                    logic_violation(logic, "the bit-vector theory is excluded")
                } else {
                    let width =
                        single_numeral_index(indices).and_then(|text| text.parse::<u64>().ok());
                    if width == Some(0) {
                        logic_violation(logic, "zero-width bit-vectors are excluded")
                    } else {
                        Ok(())
                    }
                }
            }
            ParsedSort::Parameterized(name, arguments) if name == "Array" => {
                if arguments.len() != 2 || policy.arrays == ArrayPolicy::None {
                    return logic_violation(logic, "the requested array sort is excluded");
                }
                let shape = self.parsed_sort_shape(sort);
                if !array_shape_allowed(policy.arrays, &shape) {
                    return logic_violation(logic, "the array sort is outside the logic language");
                }
                for argument in arguments {
                    self.validate_logic_sort(logic, policy, argument, bound_sort_parameters)?;
                }
                Ok(())
            }
            ParsedSort::Parameterized(name, arguments) => {
                if is_non_registry_theory_sort(name) {
                    return logic_violation(logic, "an excluded theory sort is used");
                }
                if policy.expansion == ExpansionPolicy::ConstantsOnly {
                    return logic_violation(logic, "free sort constructors are excluded");
                }
                for argument in arguments {
                    self.validate_logic_sort(logic, policy, argument, bound_sort_parameters)?;
                }
                Ok(())
            }
            ParsedSort::Indexed(_, _) => logic_violation(logic, "an excluded indexed sort is used"),
        }
    }

    fn validate_core_sort(logic: &str, policy: LogicPolicy, sort: &CoreSort) -> Result<()> {
        match sort {
            CoreSort::Bool => Ok(()),
            CoreSort::Int if policy.arithmetic.has_integers() => Ok(()),
            CoreSort::Real if policy.arithmetic.has_reals() => Ok(()),
            CoreSort::BitVec(width) if policy.bitvectors && width.width > 0 => Ok(()),
            CoreSort::Array(array) => {
                let shape = core_sort_shape(sort);
                if policy.arrays == ArrayPolicy::None || !array_shape_allowed(policy.arrays, &shape)
                {
                    return logic_violation(logic, "the array sort is outside the logic language");
                }
                Self::validate_core_sort(logic, policy, &array.index_sort)?;
                Self::validate_core_sort(logic, policy, &array.element_sort)
            }
            CoreSort::Uninterpreted(_) if policy.expansion != ExpansionPolicy::ConstantsOnly => {
                Ok(())
            }
            _ => logic_violation(logic, "the sort is outside the logic language"),
        }
    }

    fn parsed_sort_shape(&self, sort: &ParsedSort) -> SortShape {
        match sort {
            ParsedSort::Simple(name) if name == "Bool" => SortShape::Bool,
            ParsedSort::Simple(name) if name == "Int" => SortShape::Int,
            ParsedSort::Simple(name) if name == "Real" => SortShape::Real,
            ParsedSort::Simple(name) => self
                .sort_defs
                .get(name)
                .map(core_sort_shape)
                .unwrap_or(SortShape::Other),
            ParsedSort::Indexed(name, _) if name == "BitVec" => SortShape::BitVector,
            ParsedSort::Parameterized(name, arguments)
                if name == "Array" && arguments.len() == 2 =>
            {
                SortShape::Array(
                    Box::new(self.parsed_sort_shape(&arguments[0])),
                    Box::new(self.parsed_sort_shape(&arguments[1])),
                )
            }
            _ => SortShape::Other,
        }
    }

    fn validate_logic_term(
        &self,
        logic: &str,
        policy: LogicPolicy,
        term: &ParsedTerm,
        bound_names: &[String],
    ) -> Result<()> {
        match term {
            ParsedTerm::Const(Constant::Numeral(_)) => {
                if !policy.arithmetic.has_integers() && !policy.arithmetic.has_reals() {
                    return logic_violation(logic, "numeric terms are excluded");
                }
            }
            ParsedTerm::Const(Constant::Decimal(_)) => {
                if !policy.arithmetic.has_reals() {
                    return logic_violation(logic, "real terms are excluded");
                }
            }
            ParsedTerm::Const(Constant::Hexadecimal(_) | Constant::Binary(_)) => {
                if !policy.bitvectors {
                    return logic_violation(logic, "bit-vector terms are excluded");
                }
            }
            ParsedTerm::Const(Constant::String(_)) => {
                return logic_violation(logic, "the string theory is excluded");
            }
            ParsedTerm::Const(Constant::True | Constant::False) | ParsedTerm::Symbol(_) => {}
            ParsedTerm::Forall(bindings, body) | ParsedTerm::Exists(bindings, body) => {
                if !policy.quantifiers {
                    return logic_violation(logic, "quantifiers are excluded");
                }
                let mut nested = bound_names.to_vec();
                for (name, sort) in bindings {
                    self.validate_logic_sort(logic, policy, sort, &[])?;
                    nested.push(name.clone());
                }
                self.validate_logic_term(logic, policy, body, &nested)?;
            }
            ParsedTerm::Lambda(_, _) | ParsedTerm::Match(_, _) => {
                return logic_violation(logic, "higher-order or datatype terms are excluded");
            }
            ParsedTerm::Let(bindings, body) => {
                let mut nested = bound_names.to_vec();
                for (name, value) in bindings {
                    self.validate_logic_term(logic, policy, value, bound_names)?;
                    nested.push(name.clone());
                }
                self.validate_logic_term(logic, policy, body, &nested)?;
            }
            ParsedTerm::Annotated(body, _) => {
                self.validate_logic_term(logic, policy, body, bound_names)?;
            }
            ParsedTerm::App(name, arguments) => {
                self.validate_logic_application(logic, policy, name, arguments, bound_names)?;
            }
            ParsedTerm::IndexedApp(name, indices, arguments) => {
                for argument in arguments {
                    self.validate_logic_term(logic, policy, argument, bound_names)?;
                }
                if let Some(value) = name.strip_prefix("bv") {
                    if !policy.bitvectors {
                        return logic_violation(logic, "bit-vector terms are excluded");
                    }
                    validate_bv_numeral(logic, value, indices)?;
                } else if is_bitvector_operator(name) {
                    if !policy.bitvectors {
                        return logic_violation(logic, "bit-vector terms are excluded");
                    }
                } else {
                    return logic_violation(logic, "an excluded indexed operator is used");
                }
            }
            ParsedTerm::QualifiedApp(identifier, sort, arguments) => {
                self.validate_logic_sort(logic, policy, sort, &[])?;
                for argument in arguments {
                    self.validate_logic_term(logic, policy, argument, bound_names)?;
                }
                if matches!(identifier, QualifiedIdentifier::Symbol(name) if name == "const")
                    && policy.arrays == ArrayPolicy::None
                {
                    return logic_violation(logic, "array constants are excluded");
                }
            }
        }
        Ok(())
    }

    fn validate_logic_application(
        &self,
        logic: &str,
        policy: LogicPolicy,
        name: &str,
        arguments: &[ParsedTerm],
        bound_names: &[String],
    ) -> Result<()> {
        for argument in arguments {
            self.validate_logic_term(logic, policy, argument, bound_names)?;
        }

        if is_array_operator(name) {
            if policy.arrays == ArrayPolicy::None {
                return logic_violation(logic, "the array theory is excluded");
            }
            return Ok(());
        }
        if is_bitvector_operator(name) {
            if !policy.bitvectors {
                return logic_violation(logic, "the bit-vector theory is excluded");
            }
            return Ok(());
        }
        if is_non_registry_theory_operator(name) {
            return logic_violation(logic, "an excluded theory operator is used");
        }

        match name {
            "+" | "-" | "~" => {
                require_arithmetic(logic, policy)?;
            }
            "*" => {
                require_arithmetic(logic, policy)?;
                let symbolic = arguments
                    .iter()
                    .filter(|argument| !is_numeric_constant(argument))
                    .count();
                if symbolic >= 2 {
                    let real = arguments.iter().any(|argument| {
                        matches!(self.infer_term_sort(argument, bound_names), SortShape::Real)
                    }) || (!policy.arithmetic.has_integers()
                        && policy.arithmetic.has_reals());
                    if real {
                        if !policy.arithmetic.permits_nonlinear_real() {
                            return logic_violation(logic, "nonlinear real arithmetic is excluded");
                        }
                    } else if !policy.arithmetic.permits_nonlinear_integer() {
                        return logic_violation(logic, "nonlinear integer arithmetic is excluded");
                    }
                }
            }
            "**" if !policy.arithmetic.permits_integer_power() => {
                return logic_violation(logic, "integer exponentiation is excluded");
            }
            "/" => {
                if !policy.arithmetic.has_reals() {
                    return logic_violation(logic, "real division is excluded");
                }
                if arguments
                    .get(1)
                    .is_some_and(|value| !is_numeric_constant(value))
                    && !policy.arithmetic.permits_nonlinear_real()
                {
                    return logic_violation(logic, "division by a variable is excluded");
                }
            }
            "div" | "mod" | "rem" | "abs"
                if !policy.arithmetic.has_integers()
                    || !policy.arithmetic.permits_integer_division_family() =>
            {
                return logic_violation(logic, "integer div/mod/abs terms are excluded");
            }
            "to_real" | "to_int" | "is_int"
                if !policy.arithmetic.has_integers() || !policy.arithmetic.has_reals() =>
            {
                return logic_violation(logic, "mixed integer/real coercions are excluded");
            }
            "<" | "<=" | ">" | ">=" | "="
                if policy.arithmetic.is_difference()
                    && arguments.iter().any(is_arithmetic_root)
                    && !is_difference_atom(arguments) =>
            {
                return logic_violation(logic, "the atom is outside difference logic");
            }
            _ => {}
        }
        Ok(())
    }

    fn infer_term_sort(&self, term: &ParsedTerm, _bound_names: &[String]) -> SortShape {
        match term {
            ParsedTerm::Const(Constant::True | Constant::False) => SortShape::Bool,
            ParsedTerm::Const(Constant::Numeral(_)) => SortShape::Int,
            ParsedTerm::Const(Constant::Decimal(_)) => SortShape::Real,
            ParsedTerm::Const(Constant::Hexadecimal(_) | Constant::Binary(_)) => {
                SortShape::BitVector
            }
            ParsedTerm::Symbol(name) => self
                .symbols
                .get(name)
                .map(|info| core_sort_shape(&info.sort))
                .or_else(|| {
                    self.fun_defs
                        .get(name)
                        .map(|(_, result, _)| core_sort_shape(result))
                })
                .unwrap_or(SortShape::Other),
            ParsedTerm::App(name, arguments) => match name.as_str() {
                "and" | "or" | "not" | "=>" | "xor" | "=" | "distinct" | "<" | "<=" | ">"
                | ">=" => SortShape::Bool,
                "/" => SortShape::Real,
                "+" | "-" | "~" | "*" | "div" | "mod" | "rem" | "abs" | "**" => {
                    if arguments
                        .iter()
                        .any(|argument| self.infer_term_sort(argument, &[]) == SortShape::Real)
                    {
                        SortShape::Real
                    } else {
                        SortShape::Int
                    }
                }
                _ if is_bitvector_operator(name) => SortShape::BitVector,
                _ => self
                    .symbols
                    .get(name)
                    .map(|info| core_sort_shape(&info.sort))
                    .or_else(|| {
                        self.fun_defs
                            .get(name)
                            .map(|(_, result, _)| core_sort_shape(result))
                    })
                    .unwrap_or(SortShape::Other),
            },
            ParsedTerm::IndexedApp(name, _, _)
                if matches!(
                    name.as_str(),
                    "at-most" | "at-least" | "pble" | "pbge" | "pbeq"
                ) =>
            {
                SortShape::Bool
            }
            ParsedTerm::IndexedApp(name, _, _) if name.starts_with("bv") => SortShape::BitVector,
            ParsedTerm::QualifiedApp(_, sort, _) => self.parsed_sort_shape(sort),
            ParsedTerm::Annotated(body, _) => self.infer_term_sort(body, &[]),
            _ => SortShape::Other,
        }
    }
}

fn execution_mode_violation<T>(command: &Command, mode: &str) -> Result<T> {
    Err(ElaborateError::Unsupported(format!(
        "{} is not available in {mode} mode",
        command_name(command)
    )))
}

fn command_name(command: &Command) -> &'static str {
    match command {
        Command::SetLogic(_) => "set-logic",
        Command::SetOption(..) | Command::SetOptionAttribute(_) => "set-option",
        Command::SetInfo(..) | Command::SetInfoAttribute(_) => "set-info",
        Command::DeclareSort(..) => "declare-sort",
        Command::DeclareSortParameter(_) => "declare-sort-parameter",
        Command::DefineSort(..) => "define-sort",
        Command::DeclareDatatype(..) => "declare-datatype",
        Command::DeclareDatatypes(..) => "declare-datatypes",
        Command::DeclareFun(..) => "declare-fun",
        Command::DeclareConst(..) => "declare-const",
        Command::DefineFun(..) => "define-fun",
        Command::DefineFunRec(..) => "define-fun-rec",
        Command::DefineFunsRec(..) => "define-funs-rec",
        Command::Assert(_) => "assert",
        Command::CheckSat => "check-sat",
        Command::CheckSatAssuming(_) => "check-sat-assuming",
        Command::Echo(_) => "echo",
        Command::Exit => "exit",
        Command::GetAssertions => "get-assertions",
        Command::GetAssignment => "get-assignment",
        Command::GetInfo(_) => "get-info",
        Command::GetModel => "get-model",
        Command::GetOption(_) => "get-option",
        Command::GetProof => "get-proof",
        Command::GetUnsatAssumptions => "get-unsat-assumptions",
        Command::GetUnsatCore | Command::GetUnsatCoreWithFarkas => "get-unsat-core",
        Command::GetValue(_) => "get-value",
        Command::Pop(_) => "pop",
        Command::Push(_) => "push",
        Command::Reset => "reset",
        Command::ResetAssertions => "reset-assertions",
        _ => "extension command",
    }
}

fn is_start_only_option(key: &str) -> bool {
    key == "global-declarations"
        || key == "interactive-mode"
        || key == "random-seed"
        || key.starts_with("produce-")
}

fn core_sort_shape(sort: &CoreSort) -> SortShape {
    match sort {
        CoreSort::Bool => SortShape::Bool,
        CoreSort::Int => SortShape::Int,
        CoreSort::Real => SortShape::Real,
        CoreSort::BitVec(_) => SortShape::BitVector,
        CoreSort::Array(array) => SortShape::Array(
            Box::new(core_sort_shape(&array.index_sort)),
            Box::new(core_sort_shape(&array.element_sort)),
        ),
        _ => SortShape::Other,
    }
}

fn array_shape_allowed(policy: ArrayPolicy, shape: &SortShape) -> bool {
    let SortShape::Array(index, element) = shape else {
        return false;
    };
    match policy {
        ArrayPolicy::None => false,
        ArrayPolicy::Any => true,
        ArrayPolicy::IntToInt => **index == SortShape::Int && **element == SortShape::Int,
        ArrayPolicy::IntToRealOrNested => {
            **index == SortShape::Int
                && (**element == SortShape::Real
                    || array_shape_allowed(ArrayPolicy::IntToRealOrNested, element))
        }
        ArrayPolicy::BitVectorToBitVector => {
            **index == SortShape::BitVector && **element == SortShape::BitVector
        }
    }
}

fn require_arithmetic(logic: &str, policy: LogicPolicy) -> Result<()> {
    if policy.arithmetic == ArithmeticPolicy::None {
        logic_violation(logic, "arithmetic is excluded")
    } else {
        Ok(())
    }
}

fn logic_violation<T>(logic: &str, detail: &str) -> Result<T> {
    Err(ElaborateError::Unsupported(format!(
        "term is outside declared logic {logic}: {detail}"
    )))
}

fn single_numeral_index(indices: &[Index]) -> Option<&str> {
    let [Index::Numeral(value)] = indices else {
        return None;
    };
    Some(value)
}

fn validate_bv_numeral(logic: &str, value: &str, indices: &[Index]) -> Result<()> {
    let Some(width) = single_numeral_index(indices).and_then(|text| text.parse::<u64>().ok())
    else {
        return logic_violation(logic, "a bit-vector numeral has an invalid width");
    };
    if width == 0 {
        return logic_violation(logic, "zero-width bit-vectors are excluded");
    }
    let Some(value) = BigUint::parse_bytes(value.as_bytes(), 10) else {
        return logic_violation(logic, "a bit-vector numeral has an invalid value");
    };
    if value.bits() > width {
        return logic_violation(logic, "a bit-vector numeral overflows its declared width");
    }
    Ok(())
}

fn is_numeric_constant(term: &ParsedTerm) -> bool {
    match term {
        ParsedTerm::Const(Constant::Numeral(_) | Constant::Decimal(_)) => true,
        ParsedTerm::App(name, arguments) if name == "-" && arguments.len() == 1 => {
            is_numeric_constant(&arguments[0])
        }
        _ => false,
    }
}

fn is_arithmetic_root(term: &ParsedTerm) -> bool {
    matches!(
        term,
        ParsedTerm::App(name, _)
            if matches!(
                name.as_str(),
                "+" | "-" | "~" | "*" | "/" | "div" | "mod" | "rem" | "abs" | "**"
            )
    )
}

fn is_difference_atom(arguments: &[ParsedTerm]) -> bool {
    let [left, right] = arguments else {
        return false;
    };
    (is_difference_lhs(left) && is_numeric_constant(right))
        || (is_difference_lhs(right) && is_numeric_constant(left))
}

fn is_difference_lhs(term: &ParsedTerm) -> bool {
    match term {
        ParsedTerm::Symbol(_) => true,
        ParsedTerm::App(name, arguments) if name == "-" && arguments.len() == 2 => {
            arguments.iter().all(is_difference_variable)
        }
        _ => false,
    }
}

fn is_difference_variable(term: &ParsedTerm) -> bool {
    match term {
        ParsedTerm::Symbol(_) => true,
        ParsedTerm::App(name, arguments) => {
            !matches!(
                name.as_str(),
                "+" | "-" | "~" | "*" | "/" | "div" | "mod" | "rem" | "abs" | "**"
            ) && arguments.iter().all(is_difference_variable)
        }
        ParsedTerm::QualifiedApp(_, _, arguments) | ParsedTerm::IndexedApp(_, _, arguments) => {
            arguments.iter().all(is_difference_variable)
        }
        _ => false,
    }
}

fn is_array_operator(name: &str) -> bool {
    matches!(name, "select" | "store")
}

fn is_bitvector_operator(name: &str) -> bool {
    name.starts_with("bv")
        || matches!(
            name,
            "concat"
                | "extract"
                | "repeat"
                | "zero_extend"
                | "sign_extend"
                | "rotate_left"
                | "rotate_right"
        )
}

fn is_non_registry_theory_sort(name: &str) -> bool {
    matches!(
        name,
        "String"
            | "RegLan"
            | "Char"
            | "RoundingMode"
            | "Float16"
            | "Float32"
            | "Float64"
            | "Float128"
            | "FloatingPoint"
            | "Seq"
            | "Set"
            | "FiniteSet"
            | "Bag"
            | "Multiset"
            | "Map"
    )
}

fn is_non_registry_theory_operator(name: &str) -> bool {
    name.starts_with("str.")
        || name.starts_with("seq.")
        || name.starts_with("re.")
        || name.starts_with("fp.")
        || name.starts_with("set.")
        || name.starts_with("bag.")
        || name.starts_with("multiset.")
        || name.starts_with("map.")
        || matches!(name, "to_fp" | "fp" | "char")
}

#[cfg(test)]
mod tests {
    use crate::parser::parse;

    use super::*;

    fn strict_context(script: &str) -> Result<Context> {
        let mut context = Context::new();
        context.set_strict_logic_compliance(true);
        for command in
            parse(script).map_err(|error| ElaborateError::Unsupported(error.to_string()))?
        {
            context.process_command(&command)?;
        }
        Ok(context)
    }

    #[test]
    fn official_logic_restriction_witnesses_are_rejected() {
        let scripts = [
            "(set-logic QF_LIA)(assert (forall ((q Bool)) q))",
            "(set-logic QF_LIA)(declare-sort U 0)",
            "(set-logic QF_LIA)(declare-fun f (Bool) Bool)",
            "(set-logic QF_UF)(declare-const x Int)",
            "(set-logic QF_UF)(assert (= (~ true) false))",
            "(set-logic QF_LIA)(declare-const x Int)(declare-const y Int)(assert (= (* x y) 0))",
            "(set-logic QF_NIA)(assert (= (** 2 3) 8))",
            "(set-logic QF_LRA)(declare-const x Real)(declare-const y Real)(assert (= (/ x y) 1.0))",
            "(set-logic QF_IDL)(declare-const x Int)(declare-const y Int)(assert (< (+ x y) 0))",
            "(set-logic QF_ABV)(declare-const a (Array Bool Bool))",
            "(set-logic QF_BV)(declare-const x (_ BitVec 0))",
            "(set-logic QF_BV)(assert (= (_ bv256 8) #x00))",
        ];
        for script in scripts {
            assert!(strict_context(script).is_err(), "accepted {script}");
        }
    }

    #[test]
    fn official_logic_positive_witnesses_remain_accepted() {
        let scripts = [
            "(set-logic QF_UF)(declare-sort U 0)(declare-fun f (U) U)(declare-const x U)(assert (= (f x) x))",
            "(set-logic QF_LIA)(declare-const x Int)(assert (= (* 3 x) 12))",
            "(set-logic QF_LIA)(assert (= (~ 3) (- 3)))",
            "(set-logic QF_NIA)(declare-const x Int)(assert (= (* x x) 4))",
            "(set-logic QF_EIA)(assert (= (** 2 10) 1024))",
            "(set-logic QF_LRA)(declare-const x Real)(assert (= (* 3.0 x) 6.0))",
            "(set-logic QF_NRA)(declare-const x Real)(assert (= (* x x) 4.0))",
            "(set-logic QF_IDL)(declare-const x Int)(declare-const y Int)(assert (<= (- x y) 2))",
            "(set-logic QF_AUFLIA)(declare-const a (Array Int Int))(assert (= (select (store a 0 1) 0) 1))",
            "(set-logic QF_ABV)(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))",
            "(set-logic QF_BV)(assert (= (bvadd #x01 #x01) #x02))",
        ];
        for script in scripts {
            strict_context(script).unwrap_or_else(|error| panic!("rejected {script}: {error}"));
        }
    }

    #[test]
    fn strict_mode_requires_a_logic_before_assertion_commands() {
        let scripts = [
            "(declare-const x Bool)",
            "(assert true)",
            "(check-sat)",
            "(push 1)",
            "(get-assertions)",
        ];
        for script in scripts {
            assert!(strict_context(script).is_err(), "accepted {script}");
        }
    }

    #[test]
    fn strict_mode_rejects_second_logic_and_late_start_only_options() {
        let scripts = [
            "(set-logic QF_UF)(set-logic QF_LIA)",
            "(set-logic QF_UF)(set-option :produce-models true)",
            "(set-logic QF_UF)(set-option :produce-proofs true)",
            "(set-logic QF_UF)(set-option :global-declarations true)",
            "(set-logic QF_UF)(set-option :interactive-mode true)",
            "(set-logic QF_UF)(set-option :random-seed 1)",
        ];
        for script in scripts {
            assert!(strict_context(script).is_err(), "accepted {script}");
        }
    }

    #[test]
    fn strict_mode_accepts_start_commands_and_start_only_options_before_logic() {
        strict_context(
            "(set-option :produce-models true)\
             (set-option :random-seed 1)\
             (set-info :source \"state-machine-test\")\
             (echo \"ready\")\
             (set-logic QF_UF)\
             (assert true)",
        )
        .unwrap();
    }

    #[test]
    fn permissive_library_mode_and_reset_policy_are_explicit() {
        let mut permissive = Context::new();
        for command in parse("(set-logic QF_UF)(declare-const x Int)").unwrap() {
            permissive.process_command(&command).unwrap();
        }

        let mut strict = Context::new();
        strict.set_strict_logic_compliance(true);
        strict
            .process_command(&Command::SetLogic("QF_UF".to_string()))
            .unwrap();
        strict.process_command(&Command::Reset).unwrap();
        strict
            .process_command(&Command::SetLogic("QF_UF".to_string()))
            .unwrap();
        assert!(strict
            .process_command(&Command::DeclareConst(
                "x".to_string(),
                ParsedSort::Simple("Int".to_string()),
            ))
            .is_err());
    }
}
