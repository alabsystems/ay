// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB 2.7 global schematic sort parameters.
//!
//! A declared sort parameter is not an uninterpreted sort.  An assertion that
//! mentions one stands for every monomorphic instance constructible from the
//! signature at `check-sat` time.  AY materializes those instances when that
//! universe is finite and known exactly; otherwise the executor returns
//! `unknown`, never a verdict for a partial family.

use std::collections::BTreeSet;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::Sort;

use crate::command::{
    Index, MatchPattern, QualifiedIdentifier, Sort as ParsedSort, Term as ParsedTerm,
};
use crate::sexp::SExpr;

use super::{
    is_reserved_symbol, Context, ElaborateError, PolymorphicAssertion, PolymorphicDeclaration,
    PublicSort, Result,
};

/// Bound the eager Cartesian product.  Exceeding it is an honest incomplete
/// query (`unknown`), not a reason to drop required instances.
const MAX_SCHEMATIC_INSTANCES: usize = 4096;

#[derive(Clone, Copy)]
enum DefinitionFlavor {
    Plain,
    Recursive,
}

impl Context {
    /// Reject a logic whose theory signature would collide with an already
    /// declared global parameter.
    pub(crate) fn validate_logic_sort_parameter_conflicts(&self, logic: &str) -> Result<()> {
        if let Some(name) = self.sort_parameters.iter().find(|name| {
            current_logic_has_theory_sort(Some(logic), name)
                || current_logic_has_theory_function(Some(logic), name)
        }) {
            return Err(ElaborateError::SortRedeclaration(name.clone()));
        }
        Ok(())
    }

    /// Add a global schematic sort parameter to the signature.
    pub(crate) fn declare_sort_parameter(&mut self, name: &str) -> Result<()> {
        if super::commands::is_builtin_theory_sort(name)
            || current_logic_has_theory_function(self.logic.as_deref(), name)
            || current_logic_has_theory_sort(self.logic.as_deref(), name)
            || self.sort_defs.contains_key(name)
            || self.parametric_sort_defs.contains_key(name)
            || self.datatypes.contains_key(name)
            || self.parametric_datatypes.contains_key(name)
            || self.sort_parameters.contains(name)
        {
            return Err(ElaborateError::SortRedeclaration(name.to_string()));
        }
        self.sort_parameters.insert(name.to_string());
        Ok(())
    }

    /// Whether a parsed rank contains a global sort parameter.
    pub(crate) fn rank_sort_parameters(
        &self,
        arguments: &[ParsedSort],
        result: &ParsedSort,
    ) -> Vec<String> {
        let mut parameters = BTreeSet::new();
        for sort in arguments {
            self.collect_sort_parameters(sort, &mut parameters);
        }
        self.collect_sort_parameters(result, &mut parameters);
        parameters.into_iter().collect()
    }

    /// `define-sort` has its own local sort parameters, but SMT-LIB 2.7
    /// explicitly forbids global sort parameters in the alias body.
    pub(crate) fn validate_define_sort_parameters(
        &self,
        local_parameters: &[String],
        body: &ParsedSort,
    ) -> Result<()> {
        if let Some(parameter) = local_parameters.iter().find(|parameter| {
            super::commands::is_builtin_theory_sort(parameter)
                || current_logic_has_theory_sort(self.logic.as_deref(), parameter)
        }) {
            return Err(ElaborateError::SortRedeclaration(parameter.clone()));
        }
        let local: BTreeSet<_> = local_parameters.iter().map(String::as_str).collect();
        let mut globals = BTreeSet::new();
        collect_unshadowed_sort_parameters(self, body, &local, &mut globals);
        if let Some(parameter) = globals.into_iter().next() {
            return Err(ElaborateError::Unsupported(format!(
                "define-sort body cannot contain global sort parameter '{parameter}'"
            )));
        }
        Ok(())
    }

    /// Global parameters occurring anywhere in a function definition.  A
    /// monomorphic rank can still have a polymorphic defining body.
    pub(crate) fn function_definition_sort_parameters(
        &self,
        parameters: &[(String, ParsedSort)],
        result: &ParsedSort,
        body: &ParsedTerm,
    ) -> Vec<String> {
        let argument_sorts: Vec<_> = parameters.iter().map(|(_, sort)| sort.clone()).collect();
        let mut found: BTreeSet<_> = self
            .rank_sort_parameters(&argument_sorts, result)
            .into_iter()
            .collect();
        found.extend(self.term_sort_parameters(body));
        found.into_iter().collect()
    }

    /// Install a polymorphic `define-fun` as its standard declaration plus a
    /// persistent schematic defining equality.
    pub(crate) fn define_function_with_sort_parameters(
        &mut self,
        name: &str,
        parameters: &[(String, ParsedSort)],
        result: &ParsedSort,
        body: &ParsedTerm,
    ) -> Result<()> {
        self.define_function_with_sort_parameters_kind(
            name,
            parameters,
            result,
            body,
            DefinitionFlavor::Plain,
        )
    }

    /// Install a polymorphic `define-fun-rec` using the command's normative
    /// declaration-plus-assertion semantics.
    pub(crate) fn define_recursive_function_with_sort_parameters(
        &mut self,
        name: &str,
        parameters: &[(String, ParsedSort)],
        result: &ParsedSort,
        body: &ParsedTerm,
    ) -> Result<()> {
        self.define_function_with_sort_parameters_kind(
            name,
            parameters,
            result,
            body,
            DefinitionFlavor::Recursive,
        )
    }

    /// Install a polymorphic mutually recursive definition batch atomically.
    pub(crate) fn define_recursive_functions_with_sort_parameters(
        &mut self,
        declarations: &[crate::command::FuncDeclaration],
        bodies: &[ParsedTerm],
    ) -> Result<()> {
        if declarations.len() != bodies.len() {
            return Err(ElaborateError::InvalidConstant(format!(
                "define-funs-rec has {} declarations but {} bodies",
                declarations.len(),
                bodies.len()
            )));
        }

        let (mut probe, assignment) = self.synthetic_definition_probe()?;
        let concrete_declarations: Vec<_> = declarations
            .iter()
            .map(|(name, parameters, result)| {
                (
                    name.clone(),
                    substitute_bindings(parameters, &assignment),
                    substitute_sort(result, &assignment),
                )
            })
            .collect();
        let concrete_bodies: Vec<_> = bodies
            .iter()
            .map(|body| substitute_term(body, &assignment))
            .collect();
        probe.define_funs_rec(&concrete_declarations, &concrete_bodies)?;

        let mut next = self.clone();
        let global = next.global_declarations_enabled();
        for (name, parameters, result) in declarations {
            next.install_definition_declaration(name, parameters, result)?;
            next.recursive_fun_names.insert(name.clone());
        }
        for ((name, parameters, result), body) in declarations.iter().zip(bodies) {
            let assertion = definition_assertion(name, parameters, result, body);
            next.add_definition_assertion(&assertion, global)?;
        }
        *self = next;
        Ok(())
    }

    fn define_function_with_sort_parameters_kind(
        &mut self,
        name: &str,
        parameters: &[(String, ParsedSort)],
        result: &ParsedSort,
        body: &ParsedTerm,
        flavor: DefinitionFlavor,
    ) -> Result<()> {
        let (mut probe, assignment) = self.synthetic_definition_probe()?;
        let concrete_parameters = substitute_bindings(parameters, &assignment);
        let concrete_result = substitute_sort(result, &assignment);
        let concrete_body = substitute_term(body, &assignment);
        match flavor {
            DefinitionFlavor::Plain => {
                probe.define_fun(name, &concrete_parameters, &concrete_result, &concrete_body)?;
            }
            DefinitionFlavor::Recursive => {
                probe.define_fun_rec(
                    name,
                    &concrete_parameters,
                    &concrete_result,
                    &concrete_body,
                )?;
            }
        }

        let mut next = self.clone();
        let global = next.global_declarations_enabled();
        next.install_definition_declaration(name, parameters, result)?;
        if matches!(flavor, DefinitionFlavor::Recursive) {
            next.recursive_fun_names.insert(name.to_string());
        }
        let assertion = definition_assertion(name, parameters, result, body);
        next.add_definition_assertion(&assertion, global)?;
        *self = next;
        Ok(())
    }

    fn synthetic_definition_probe(&self) -> Result<(Self, HashMap<String, ParsedSort>)> {
        let mut parameters: Vec<_> = self.sort_parameters.iter().cloned().collect();
        parameters.sort();
        let (mut probe, assignment) = self.synthetic_parameter_probe(&parameters);
        let declarations = probe.polymorphic_declarations.clone();
        for declaration in declarations {
            probe.instantiate_polymorphic_declaration(&declaration, &assignment)?;
        }
        Ok((probe, assignment))
    }

    fn install_definition_declaration(
        &mut self,
        name: &str,
        parameters: &[(String, ParsedSort)],
        result: &ParsedSort,
    ) -> Result<()> {
        let arguments: Vec<_> = parameters.iter().map(|(_, sort)| sort.clone()).collect();
        if self.rank_sort_parameters(&arguments, result).is_empty() {
            self.declare_fun(name, &arguments, result)
        } else {
            self.declare_polymorphic_fun(name, &arguments, result)
        }
    }

    fn add_definition_assertion(&mut self, term: &ParsedTerm, global: bool) -> Result<()> {
        self.reject_unqualified_ambiguous_polymorphic_symbols(term)?;
        let (mut sorts, _) = self.available_monomorphic_sorts();
        self.collect_explicit_monomorphic_term_sorts(term, &mut sorts);
        let _ = self.instantiate_polymorphic_declarations_for(&sorts)?;

        let parameters = self.term_sort_parameters(term);
        if parameters.is_empty() {
            let mut probe = self.clone();
            probe.assert_polymorphic_instance(term)?;
        } else {
            self.validate_polymorphic_assertion(term, &parameters)?;
        }
        let definition = PolymorphicAssertion {
            term: term.clone(),
            parameters,
            persistent_definition: true,
        };
        if global && !self.scopes.is_empty() {
            let insertion = self.scopes[0].polymorphic_assertion_count;
            self.polymorphic_assertions.insert(insertion, definition);
            for frame in &mut self.scopes {
                frame.polymorphic_assertion_count =
                    frame.polymorphic_assertion_count.saturating_add(1);
            }
        } else {
            self.polymorphic_assertions.push(definition);
        }
        Ok(())
    }

    /// Register a schematic uninterpreted function family.  `declare-const`
    /// uses the same representation with an empty domain.
    pub(crate) fn declare_polymorphic_fun(
        &mut self,
        name: &str,
        argument_sorts: &[ParsedSort],
        result_sort: &ParsedSort,
    ) -> Result<()> {
        let parameters = self.rank_sort_parameters(argument_sorts, result_sort);
        if parameters.is_empty() {
            return Err(ElaborateError::Unsupported(
                "internal polymorphic declaration without a sort parameter".to_string(),
            ));
        }
        if is_reserved_symbol(name) {
            return Err(ElaborateError::ReservedSymbol(name.to_string()));
        }
        if self.is_datatype_member_name(name) {
            return Err(ElaborateError::DatatypeMemberCollision(name.to_string()));
        }
        if super::is_declaration_activated_op_name(name) {
            return Err(ElaborateError::Unsupported(format!(
                "declaration-activated builtin '{name}' cannot have a polymorphic rank"
            )));
        }
        if self.has_symbol_binding(name)
            || self
                .polymorphic_declarations
                .iter()
                .any(|declaration| declaration.name == name)
        {
            return Err(ElaborateError::Redefinition(format!(
                "invalid declaration, function '{name}' already declared"
            )));
        }

        self.validate_polymorphic_rank(argument_sorts, result_sort, &parameters)?;

        let global = self.global_declarations_enabled();
        self.polymorphic_declarations.push(PolymorphicDeclaration {
            name: name.to_string(),
            argument_sorts: argument_sorts.to_vec(),
            result_sort: result_sort.clone(),
            parameters,
            global,
        });
        if !global {
            if let Some(frame) = self.scopes.last_mut() {
                frame.polymorphic_declarations.push(name.to_string());
            }
        }

        // Make all currently observed ground uses available immediately.  The
        // full family is revisited whenever the signature changes and at each
        // satisfiability check.
        let (sorts, _) = self.available_monomorphic_sorts();
        let _ = self.instantiate_polymorphic_declarations_for(&sorts)?;
        Ok(())
    }

    /// Add an authored assertion, retaining schematic assertions separately
    /// until `check-sat` supplies the current sort universe.
    pub(crate) fn assert_authored(&mut self, term: &ParsedTerm) -> Result<()> {
        self.reject_unqualified_ambiguous_polymorphic_symbols(term)?;
        // A qualified identifier or binder can be the first occurrence of a
        // concrete composite sort.  Register that ground family member before
        // ordinary elaboration tries to resolve the symbol by rank.
        //
        // PERFORMANCE (#assert-polymorphic-prework): this pre-pass exists only to
        // feed `instantiate_polymorphic_declarations_for`, so it is dead work when
        // the problem declares no polymorphic symbols at all. It is NOT cheap:
        // `available_monomorphic_sorts` clones the whole assertion vector and
        // walks every accumulated assertion's subterms, so running it per-assert
        // is QUADRATIC in the assertion count. Measured on
        // `QF_UFDT/.../vlsat3_b09.smt2` (25,444 asserts, no polymorphism):
        // 18.8 s of the file's 19.7 s parse+elaborate, 0.74 ms per assert,
        // against 1.4 s total before this pre-pass existed.
        //
        // Guarding on "are there any polymorphic declarations or assertions?"
        // preserves behaviour exactly — with none, there is nothing to
        // instantiate and the call is a no-op whose only effect is the sort scan.
        if !self.polymorphic_declarations.is_empty() || !self.polymorphic_assertions.is_empty() {
            let (mut sorts, _) = self.available_monomorphic_sorts();
            self.collect_explicit_monomorphic_term_sorts(term, &mut sorts);
            let _ = self.instantiate_polymorphic_declarations_for(&sorts)?;
        }

        let parameters = self.term_sort_parameters(term);
        if parameters.is_empty() {
            let source_is_literal_false = super::authored_source_is_literal_false(term);
            self.assert(term)?;
            let asserted_index = self.assertions.len().checked_sub(1).ok_or_else(|| {
                ElaborateError::Unsupported(
                    "authored assertion produced no elaborated term".to_string(),
                )
            })?;
            let parsed_index =
                (self.assertions_parsed.len() == self.assertions.len()).then_some(asserted_index);
            self.authored_assertions
                .push(super::AuthoredAssertion::Concrete {
                    term: self.assertions[asserted_index],
                    parsed_index,
                    source_is_literal_false,
                });
            return Ok(());
        }

        self.validate_polymorphic_assertion(term, &parameters)?;
        self.polymorphic_assertions.push(PolymorphicAssertion {
            term: term.clone(),
            parameters,
            persistent_definition: false,
        });
        self.authored_assertions
            .push(super::AuthoredAssertion::Schematic(term.clone()));
        Ok(())
    }

    fn reject_unqualified_ambiguous_polymorphic_symbols(&self, term: &ParsedTerm) -> Result<()> {
        self.reject_unqualified_ambiguous_polymorphic_symbols_with_bindings(term, &mut Vec::new())
    }

    fn reject_unqualified_ambiguous_polymorphic_name(&self, name: &str) -> Result<()> {
        if self.polymorphic_declarations.iter().any(|declaration| {
            declaration.name == name && declaration_result_is_ambiguous(declaration)
        }) {
            return Err(ElaborateError::IllSorted(format!(
                "ambiguous polymorphic symbol '{name}' requires an (as {name} <sort>) qualification"
            )));
        }
        Ok(())
    }

    fn reject_unqualified_ambiguous_polymorphic_symbols_with_bindings(
        &self,
        term: &ParsedTerm,
        bound: &mut Vec<String>,
    ) -> Result<()> {
        match term {
            ParsedTerm::Const(_) => Ok(()),
            ParsedTerm::Symbol(name) if bound.iter().any(|binding| binding == name) => Ok(()),
            ParsedTerm::Symbol(name) => self.reject_unqualified_ambiguous_polymorphic_name(name),
            ParsedTerm::App(name, arguments) => {
                // Application heads are signature symbols, not term variables;
                // AY's term elaborator likewise does not resolve them in `env`.
                self.reject_unqualified_ambiguous_polymorphic_name(name)?;
                arguments.iter().try_for_each(|argument| {
                    self.reject_unqualified_ambiguous_polymorphic_symbols_with_bindings(
                        argument, bound,
                    )
                })
            }
            ParsedTerm::IndexedApp(_, _, arguments) | ParsedTerm::QualifiedApp(_, _, arguments) => {
                arguments.iter().try_for_each(|argument| {
                    self.reject_unqualified_ambiguous_polymorphic_symbols_with_bindings(
                        argument, bound,
                    )
                })
            }
            ParsedTerm::Let(bindings, body) => {
                // SMT-LIB `let` bindings are parallel: each value is checked in
                // the outer scope, and the names become visible only in `body`.
                bindings.iter().try_for_each(|(_, value)| {
                    self.reject_unqualified_ambiguous_polymorphic_symbols_with_bindings(
                        value, bound,
                    )
                })?;
                let outer_len = bound.len();
                bound.extend(
                    bindings
                        .iter()
                        .filter(|(name, _)| name != "_")
                        .map(|(name, _)| name.clone()),
                );
                let result = self
                    .reject_unqualified_ambiguous_polymorphic_symbols_with_bindings(body, bound);
                bound.truncate(outer_len);
                result
            }
            ParsedTerm::Forall(bindings, body)
            | ParsedTerm::Exists(bindings, body)
            | ParsedTerm::Lambda(bindings, body) => {
                let outer_len = bound.len();
                bound.extend(
                    bindings
                        .iter()
                        .filter(|(name, _)| name != "_")
                        .map(|(name, _)| name.clone()),
                );
                let result = self
                    .reject_unqualified_ambiguous_polymorphic_symbols_with_bindings(body, bound);
                bound.truncate(outer_len);
                result
            }
            ParsedTerm::Annotated(body, _) => {
                self.reject_unqualified_ambiguous_polymorphic_symbols_with_bindings(body, bound)
            }
            ParsedTerm::Match(scrutinee, cases) => {
                self.reject_unqualified_ambiguous_polymorphic_symbols_with_bindings(
                    scrutinee, bound,
                )?;
                for (pattern, body) in cases {
                    let outer_len = bound.len();
                    match pattern {
                        // The elaborator later disambiguates a bare symbol as a
                        // nullary constructor or whole-scrutinee binder from the
                        // scrutinee datatype. Treating it as a binder here avoids
                        // a false preflight rejection; ordinary term elaboration
                        // remains authoritative if it is actually a constructor.
                        MatchPattern::Symbol(name) if name != "_" => bound.push(name.clone()),
                        MatchPattern::Constructor(_, bindings) => bound
                            .extend(bindings.iter().filter(|name| name.as_str() != "_").cloned()),
                        MatchPattern::Symbol(_) => {}
                    }
                    let result = self
                        .reject_unqualified_ambiguous_polymorphic_symbols_with_bindings(
                            body, bound,
                        );
                    bound.truncate(outer_len);
                    result?;
                }
                Ok(())
            }
        }
    }

    /// Remove the query-local concrete instances appended by the previous
    /// check.  Mutation commands call this before touching the assertion stack.
    #[doc(hidden)]
    pub fn clear_materialized_polymorphic_assertions(&mut self) {
        if self.materialized_polymorphic_assertions == 0 {
            self.polymorphic_instantiation_complete = true;
            return;
        }
        let retained = self
            .assertions
            .len()
            .saturating_sub(self.materialized_polymorphic_assertions);
        self.assertions.truncate(retained);
        self.assertion_finite_set_metadata.truncate(retained);
        self.assertions_parsed.truncate(retained);
        self.materialized_polymorphic_assertions = 0;
        self.polymorphic_instantiation_complete = true;
    }

    /// Instantiate all authored schematic assertions for the current query.
    pub(crate) fn materialize_polymorphic_assertions(&mut self) -> Result<()> {
        self.clear_materialized_polymorphic_assertions();
        if self.polymorphic_assertions.is_empty() {
            return Ok(());
        }

        let (sorts, universe_complete) = self.available_monomorphic_sorts();
        let needs_sort_universe = self
            .polymorphic_assertions
            .iter()
            .any(|assertion| !assertion.parameters.is_empty());
        if (needs_sort_universe && !universe_complete)
            || (needs_sort_universe && !self.instantiate_polymorphic_declarations_for(&sorts)?)
            || self.polymorphic_assertions.iter().any(|assertion| {
                schematic_instance_count(sorts.len(), assertion.parameters.len()).is_none()
            })
        {
            self.polymorphic_instantiation_complete = false;
            return Ok(());
        }

        let base = self.assertions.len();
        let assertions = self.polymorphic_assertions.clone();
        for assertion in assertions {
            let assignments = sort_assignments(&assertion.parameters, &sorts)
                .ok_or_else(|| ElaborateError::Unsupported("schematic instance limit".into()))?;
            for assignment in assignments {
                let concrete = substitute_term(&assertion.term, &assignment);
                if let Err(error) = self.assert_polymorphic_instance(&concrete) {
                    self.assertions.truncate(base);
                    self.assertion_finite_set_metadata.truncate(base);
                    self.assertions_parsed.truncate(base);
                    return Err(error);
                }
            }
        }
        self.materialized_polymorphic_assertions = self.assertions.len() - base;
        Ok(())
    }

    /// Whether the most recently elaborated check contains every required
    /// schematic instance.
    #[must_use]
    pub fn polymorphic_instantiation_complete(&self) -> bool {
        self.polymorphic_instantiation_complete
    }

    /// Revisit the declaration families after a new monomorphic declaration or
    /// sort has extended the observed signature.
    pub(crate) fn refresh_polymorphic_declarations(&mut self) -> Result<()> {
        if self.polymorphic_declarations.is_empty() {
            return Ok(());
        }
        let (sorts, _) = self.available_monomorphic_sorts();
        let _ = self.instantiate_polymorphic_declarations_for(&sorts)?;
        Ok(())
    }

    pub(crate) fn has_user_polymorphic_declaration(&self, name: &str) -> bool {
        !self.instantiating_polymorphic_declaration
            && self
                .polymorphic_declarations
                .iter()
                .any(|declaration| declaration.name == name)
    }

    fn validate_polymorphic_rank(
        &self,
        arguments: &[ParsedSort],
        result: &ParsedSort,
        parameters: &[String],
    ) -> Result<()> {
        let (mut probe, assignment) = self.synthetic_parameter_probe(parameters);
        for sort in arguments.iter().chain(std::iter::once(result)) {
            probe.elaborate_sort(&substitute_sort(sort, &assignment))?;
        }
        Ok(())
    }

    fn validate_polymorphic_assertion(
        &self,
        term: &ParsedTerm,
        parameters: &[String],
    ) -> Result<()> {
        let (mut probe, assignment) = self.synthetic_parameter_probe(parameters);
        let declarations = probe.polymorphic_declarations.clone();
        for declaration in declarations {
            let mut declaration_assignment = HashMap::default();
            for parameter in &declaration.parameters {
                let replacement = assignment
                    .get(parameter)
                    .cloned()
                    .unwrap_or_else(|| ParsedSort::Simple(format!("__ay_poly_probe_{parameter}")));
                if let ParsedSort::Simple(name) = &replacement {
                    let sort = Sort::Uninterpreted(name.clone());
                    probe.sort_defs.insert(name.clone(), sort.clone());
                    probe
                        .public_sort_defs
                        .insert(name.clone(), PublicSort::Core(sort));
                }
                declaration_assignment.insert(parameter.clone(), replacement);
            }
            probe.instantiate_polymorphic_declaration(&declaration, &declaration_assignment)?;
        }
        let concrete = substitute_term(term, &assignment);
        probe.assert_polymorphic_instance(&concrete)
    }

    fn synthetic_parameter_probe(
        &self,
        parameters: &[String],
    ) -> (Self, HashMap<String, ParsedSort>) {
        let mut probe = self.clone();
        probe.clear_materialized_polymorphic_assertions();
        let mut assignment = HashMap::default();
        for (index, parameter) in parameters.iter().enumerate() {
            let name = format!("__ay_poly_probe_{index}_{parameter}");
            let sort = Sort::Uninterpreted(name.clone());
            probe.sort_defs.insert(name.clone(), sort.clone());
            probe
                .public_sort_defs
                .insert(name.clone(), PublicSort::Core(sort));
            assignment.insert(parameter.clone(), ParsedSort::Simple(name));
        }
        (probe, assignment)
    }

    fn instantiate_polymorphic_declarations_for(&mut self, sorts: &[ParsedSort]) -> Result<bool> {
        let declarations = self.polymorphic_declarations.clone();
        for declaration in declarations {
            let Some(assignments) = sort_assignments(&declaration.parameters, sorts) else {
                return Ok(false);
            };
            for assignment in assignments {
                self.instantiate_polymorphic_declaration(&declaration, &assignment)?;
            }
        }
        Ok(true)
    }

    fn assert_polymorphic_instance(&mut self, term: &ParsedTerm) -> Result<()> {
        let prior = std::mem::replace(&mut self.elaborating_polymorphic_instance, true);
        let asserted = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.assert(term)));
        self.elaborating_polymorphic_instance = prior;
        match asserted {
            Ok(result) => result,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }

    fn instantiate_polymorphic_declaration(
        &mut self,
        declaration: &PolymorphicDeclaration,
        assignment: &HashMap<String, ParsedSort>,
    ) -> Result<()> {
        let arguments: Vec<_> = declaration
            .argument_sorts
            .iter()
            .map(|sort| substitute_sort(sort, assignment))
            .collect();
        let result = substitute_sort(&declaration.result_sort, assignment);
        let argument_sorts = arguments
            .iter()
            .map(|sort| self.elaborate_sort(sort))
            .collect::<Result<Vec<_>>>()?;
        let result_sort = self.elaborate_sort(&result)?;
        if self.has_symbol_with_signature(&declaration.name, &argument_sorts, &result_sort) {
            return Ok(());
        }

        let prior = std::mem::replace(&mut self.instantiating_polymorphic_declaration, true);
        let registered = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            if declaration.global {
                self.with_native_global_declaration_tracking(|context| {
                    context.declare_fun(&declaration.name, &arguments, &result)
                })
            } else {
                self.declare_fun(&declaration.name, &arguments, &result)
            }
        }));
        self.instantiating_polymorphic_declaration = prior;
        match registered {
            Ok(result) => result,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }

    pub(crate) fn term_sort_parameters(&self, term: &ParsedTerm) -> Vec<String> {
        let mut parameters = BTreeSet::new();
        self.collect_term_sort_parameters(term, &mut parameters);
        parameters.into_iter().collect()
    }

    fn collect_sort_parameters(&self, sort: &ParsedSort, output: &mut BTreeSet<String>) {
        match sort {
            ParsedSort::Simple(name) => {
                if self.sort_parameters.contains(name) {
                    output.insert(name.clone());
                }
            }
            ParsedSort::Parameterized(_, parameters) => {
                for parameter in parameters {
                    self.collect_sort_parameters(parameter, output);
                }
            }
            ParsedSort::Indexed(_, _) => {}
        }
    }

    fn collect_term_sort_parameters(&self, term: &ParsedTerm, output: &mut BTreeSet<String>) {
        match term {
            ParsedTerm::Const(_) | ParsedTerm::Symbol(_) => {}
            ParsedTerm::App(_, arguments) | ParsedTerm::IndexedApp(_, _, arguments) => {
                for argument in arguments {
                    self.collect_term_sort_parameters(argument, output);
                }
            }
            ParsedTerm::QualifiedApp(_, sort, arguments) => {
                self.collect_sort_parameters(sort, output);
                for argument in arguments {
                    self.collect_term_sort_parameters(argument, output);
                }
            }
            ParsedTerm::Let(bindings, body) => {
                for (_, value) in bindings {
                    self.collect_term_sort_parameters(value, output);
                }
                self.collect_term_sort_parameters(body, output);
            }
            ParsedTerm::Forall(bindings, body)
            | ParsedTerm::Exists(bindings, body)
            | ParsedTerm::Lambda(bindings, body) => {
                for (_, sort) in bindings {
                    self.collect_sort_parameters(sort, output);
                }
                self.collect_term_sort_parameters(body, output);
            }
            ParsedTerm::Annotated(body, attributes) => {
                self.collect_term_sort_parameters(body, output);
                for (_, value) in attributes {
                    for sort in annotation_sorts(value) {
                        self.collect_sort_parameters(&sort, output);
                    }
                }
            }
            ParsedTerm::Match(scrutinee, cases) => {
                self.collect_term_sort_parameters(scrutinee, output);
                for (_, body) in cases {
                    self.collect_term_sort_parameters(body, output);
                }
            }
        }
    }

    fn collect_explicit_monomorphic_term_sorts(
        &self,
        term: &ParsedTerm,
        output: &mut Vec<ParsedSort>,
    ) {
        let add_sort = |sort: &ParsedSort, output: &mut Vec<ParsedSort>| {
            collect_monomorphic_sort_syntax(self, sort, output);
        };
        match term {
            ParsedTerm::Const(_) | ParsedTerm::Symbol(_) => {}
            ParsedTerm::App(_, arguments) | ParsedTerm::IndexedApp(_, _, arguments) => {
                for argument in arguments {
                    self.collect_explicit_monomorphic_term_sorts(argument, output);
                }
            }
            ParsedTerm::QualifiedApp(_, sort, arguments) => {
                add_sort(sort, output);
                for argument in arguments {
                    self.collect_explicit_monomorphic_term_sorts(argument, output);
                }
            }
            ParsedTerm::Let(bindings, body) => {
                for (_, value) in bindings {
                    self.collect_explicit_monomorphic_term_sorts(value, output);
                }
                self.collect_explicit_monomorphic_term_sorts(body, output);
            }
            ParsedTerm::Forall(bindings, body)
            | ParsedTerm::Exists(bindings, body)
            | ParsedTerm::Lambda(bindings, body) => {
                for (_, sort) in bindings {
                    add_sort(sort, output);
                }
                self.collect_explicit_monomorphic_term_sorts(body, output);
            }
            ParsedTerm::Annotated(body, attributes) => {
                self.collect_explicit_monomorphic_term_sorts(body, output);
                for (_, value) in attributes {
                    for sort in annotation_sorts(value) {
                        add_sort(&sort, output);
                    }
                }
            }
            ParsedTerm::Match(scrutinee, cases) => {
                self.collect_explicit_monomorphic_term_sorts(scrutinee, output);
                for (_, body) in cases {
                    self.collect_explicit_monomorphic_term_sorts(body, output);
                }
            }
        }
    }

    /// Return every observed monomorphic sort plus whether this is the complete
    /// closure of sort constructors in the current signature.
    fn available_monomorphic_sorts(&self) -> (Vec<ParsedSort>, bool) {
        let (base_sorts, mut complete) = logic_sort_universe(self.logic.as_deref());
        let mut sorts: BTreeSet<Sort> = base_sorts.into_iter().collect();

        for sort in self.sort_defs.values() {
            sorts.insert(sort.clone());
            if has_positive_arity_constructor(sort) {
                complete = false;
            }
        }
        for (_, info) in self.symbol_iter() {
            sorts.insert(info.sort.clone());
            sorts.extend(info.arg_sorts.iter().cloned());
            if has_positive_arity_constructor(&info.sort)
                || info.arg_sorts.iter().any(has_positive_arity_constructor)
            {
                complete = false;
            }
        }
        let mut pending = self.assertions.clone();
        pending.extend(self.objectives.iter().map(|objective| objective.term));
        pending.extend(self.soft_constraints.iter().map(|soft| soft.term));
        let mut visited = ay_core::kani_compat::DetHashSet::default();
        while let Some(term) = pending.pop() {
            if !visited.insert(term) {
                continue;
            }
            let sort = self.terms.sort(term).clone();
            if has_positive_arity_constructor(&sort) {
                complete = false;
            }
            sorts.insert(sort);
            pending.extend(self.terms.children(term));
        }
        if !self.parametric_datatypes.is_empty() {
            complete = false;
        }
        if self
            .parametric_sort_defs
            .values()
            .any(|(_, body)| parsed_sort_uses_positive_constructor(body))
        {
            complete = false;
        }

        let parsed = sorts.iter().filter_map(core_sort_to_parsed).collect();
        (parsed, complete)
    }
}

fn collect_monomorphic_sort_syntax(
    context: &Context,
    sort: &ParsedSort,
    output: &mut Vec<ParsedSort>,
) {
    if context.rank_sort_parameters(&[], sort).is_empty() && !output.contains(sort) {
        output.push(sort.clone());
    }
    if let ParsedSort::Parameterized(_, parameters) = sort {
        for parameter in parameters {
            collect_monomorphic_sort_syntax(context, parameter, output);
        }
    }
}

fn collect_unshadowed_sort_parameters(
    context: &Context,
    sort: &ParsedSort,
    local_parameters: &BTreeSet<&str>,
    output: &mut BTreeSet<String>,
) {
    match sort {
        ParsedSort::Simple(name) => {
            if !local_parameters.contains(name.as_str()) && context.sort_parameters.contains(name) {
                output.insert(name.clone());
            }
        }
        ParsedSort::Parameterized(_, parameters) => {
            for parameter in parameters {
                collect_unshadowed_sort_parameters(context, parameter, local_parameters, output);
            }
        }
        ParsedSort::Indexed(_, _) => {}
    }
}

fn definition_assertion(
    name: &str,
    parameters: &[(String, ParsedSort)],
    result: &ParsedSort,
    body: &ParsedTerm,
) -> ParsedTerm {
    let arguments = parameters
        .iter()
        .map(|(parameter, _)| ParsedTerm::Symbol(parameter.clone()))
        .collect();
    let application = ParsedTerm::QualifiedApp(
        QualifiedIdentifier::Symbol(name.to_string()),
        result.clone(),
        arguments,
    );
    let equality = ParsedTerm::App("=".to_string(), vec![application, body.clone()]);
    if parameters.is_empty() {
        equality
    } else {
        ParsedTerm::Forall(parameters.to_vec(), Box::new(equality))
    }
}

fn schematic_instance_count(sort_count: usize, parameter_count: usize) -> Option<usize> {
    let exponent = u32::try_from(parameter_count).ok()?;
    let count = sort_count.checked_pow(exponent)?;
    (count <= MAX_SCHEMATIC_INSTANCES).then_some(count)
}

fn declaration_result_is_ambiguous(declaration: &PolymorphicDeclaration) -> bool {
    let mut result_parameters = BTreeSet::new();
    collect_parameter_names(
        &declaration.result_sort,
        &declaration.parameters,
        &mut result_parameters,
    );
    let mut argument_parameters = BTreeSet::new();
    for sort in &declaration.argument_sorts {
        collect_parameter_names(sort, &declaration.parameters, &mut argument_parameters);
    }
    result_parameters
        .iter()
        .any(|parameter| !argument_parameters.contains(parameter))
}

fn collect_parameter_names(sort: &ParsedSort, declared: &[String], output: &mut BTreeSet<String>) {
    match sort {
        ParsedSort::Simple(name) => {
            if declared.contains(name) {
                output.insert(name.clone());
            }
        }
        ParsedSort::Parameterized(_, parameters) => {
            for parameter in parameters {
                collect_parameter_names(parameter, declared, output);
            }
        }
        ParsedSort::Indexed(_, _) => {}
    }
}

fn sort_assignments(
    parameters: &[String],
    sorts: &[ParsedSort],
) -> Option<Vec<HashMap<String, ParsedSort>>> {
    let count = schematic_instance_count(sorts.len(), parameters.len())?;
    let mut assignments = Vec::with_capacity(count);
    let mut current = HashMap::default();
    build_sort_assignments(parameters, sorts, 0, &mut current, &mut assignments);
    Some(assignments)
}

fn build_sort_assignments(
    parameters: &[String],
    sorts: &[ParsedSort],
    index: usize,
    current: &mut HashMap<String, ParsedSort>,
    output: &mut Vec<HashMap<String, ParsedSort>>,
) {
    if index == parameters.len() {
        output.push(current.clone());
        return;
    }
    for sort in sorts {
        current.insert(parameters[index].clone(), sort.clone());
        build_sort_assignments(parameters, sorts, index + 1, current, output);
    }
    current.remove(&parameters[index]);
}

fn substitute_sort(sort: &ParsedSort, assignment: &HashMap<String, ParsedSort>) -> ParsedSort {
    stacker::maybe_grow(
        crate::sexp::PARSE_STACK_RED_ZONE,
        crate::sexp::PARSE_STACK_SIZE,
        || match sort {
            ParsedSort::Simple(name) => assignment
                .get(name)
                .cloned()
                .unwrap_or_else(|| sort.clone()),
            ParsedSort::Parameterized(name, parameters) => ParsedSort::Parameterized(
                name.clone(),
                parameters
                    .iter()
                    .map(|parameter| substitute_sort(parameter, assignment))
                    .collect(),
            ),
            ParsedSort::Indexed(_, _) => sort.clone(),
        },
    )
}

fn substitute_term(term: &ParsedTerm, assignment: &HashMap<String, ParsedSort>) -> ParsedTerm {
    stacker::maybe_grow(
        crate::sexp::PARSE_STACK_RED_ZONE,
        crate::sexp::PARSE_STACK_SIZE,
        || match term {
            ParsedTerm::Const(constant) => ParsedTerm::Const(constant.clone()),
            ParsedTerm::Symbol(name) => ParsedTerm::Symbol(name.clone()),
            ParsedTerm::App(name, arguments) => ParsedTerm::App(
                name.clone(),
                arguments
                    .iter()
                    .map(|argument| substitute_term(argument, assignment))
                    .collect(),
            ),
            ParsedTerm::IndexedApp(name, indices, arguments) => ParsedTerm::IndexedApp(
                name.clone(),
                indices.clone(),
                arguments
                    .iter()
                    .map(|argument| substitute_term(argument, assignment))
                    .collect(),
            ),
            ParsedTerm::QualifiedApp(identifier, sort, arguments) => ParsedTerm::QualifiedApp(
                clone_qualified_identifier(identifier),
                substitute_sort(sort, assignment),
                arguments
                    .iter()
                    .map(|argument| substitute_term(argument, assignment))
                    .collect(),
            ),
            ParsedTerm::Let(bindings, body) => ParsedTerm::Let(
                bindings
                    .iter()
                    .map(|(name, value)| (name.clone(), substitute_term(value, assignment)))
                    .collect(),
                Box::new(substitute_term(body, assignment)),
            ),
            ParsedTerm::Forall(bindings, body) => ParsedTerm::Forall(
                substitute_bindings(bindings, assignment),
                Box::new(substitute_term(body, assignment)),
            ),
            ParsedTerm::Exists(bindings, body) => ParsedTerm::Exists(
                substitute_bindings(bindings, assignment),
                Box::new(substitute_term(body, assignment)),
            ),
            ParsedTerm::Lambda(bindings, body) => ParsedTerm::Lambda(
                substitute_bindings(bindings, assignment),
                Box::new(substitute_term(body, assignment)),
            ),
            ParsedTerm::Annotated(body, attributes) => ParsedTerm::Annotated(
                Box::new(substitute_term(body, assignment)),
                attributes
                    .iter()
                    .map(|(keyword, value)| {
                        (
                            keyword.clone(),
                            substitute_annotation_sexp(value, assignment),
                        )
                    })
                    .collect(),
            ),
            ParsedTerm::Match(scrutinee, cases) => ParsedTerm::Match(
                Box::new(substitute_term(scrutinee, assignment)),
                cases
                    .iter()
                    .map(|(pattern, body)| (pattern.clone(), substitute_term(body, assignment)))
                    .collect(),
            ),
        },
    )
}

fn substitute_bindings(
    bindings: &[(String, ParsedSort)],
    assignment: &HashMap<String, ParsedSort>,
) -> Vec<(String, ParsedSort)> {
    bindings
        .iter()
        .map(|(name, sort)| (name.clone(), substitute_sort(sort, assignment)))
        .collect()
}

/// Return every sort occurring in a term-shaped annotation S-expression.
///
/// SMT-LIB attributes are deliberately represented as raw S-expressions, but
/// values such as `:pattern` contain ordinary terms.  Those terms can carry
/// sorts in `(as <identifier> <sort>)` qualifications and binder declarations.
/// Treating the value as opaque loses global sort parameters that occur only in
/// a trigger and later leaves an unsubstituted schematic sort in a concrete
/// instance.  The traversal is iterative so a deeply nested attribute cannot
/// overflow the stack.
fn annotation_sorts(value: &SExpr) -> Vec<ParsedSort> {
    let mut sorts = Vec::new();
    let mut pending = vec![value];
    while let Some(current) = pending.pop() {
        let SExpr::List(items) = current else {
            continue;
        };
        if matches!(items.as_slice(), [head, _, _] if head.is_symbol("as")) {
            if let Ok(sort) = ParsedSort::from_sexp(&items[2]) {
                sorts.push(sort);
            }
            continue;
        }
        if matches!(items.first(), Some(head) if head.is_symbol("forall") || head.is_symbol("exists") || head.is_symbol("lambda"))
        {
            if let Some(bindings) = items.get(1).and_then(SExpr::as_list) {
                for binding in bindings {
                    if let Some([_, sort]) = binding.as_list() {
                        if let Ok(sort) = ParsedSort::from_sexp(sort) {
                            sorts.push(sort);
                        }
                    }
                }
            }
            pending.extend(items.iter().skip(2));
            continue;
        }
        pending.extend(items);
    }
    sorts
}

fn substitute_annotation_sexp(value: &SExpr, assignment: &HashMap<String, ParsedSort>) -> SExpr {
    stacker::maybe_grow(
        crate::sexp::PARSE_STACK_RED_ZONE,
        crate::sexp::PARSE_STACK_SIZE,
        || match value {
            SExpr::List(items) if matches!(items.as_slice(), [head, _, _] if head.is_symbol("as")) =>
            {
                let replacement = ParsedSort::from_sexp(&items[2])
                    .ok()
                    .map(|sort| parsed_sort_to_sexp(&substitute_sort(&sort, assignment)))
                    .unwrap_or_else(|| items[2].clone());
                SExpr::List(vec![items[0].clone(), items[1].clone(), replacement])
            }
            SExpr::List(items) if matches!(items.first(), Some(head) if head.is_symbol("forall") || head.is_symbol("exists") || head.is_symbol("lambda")) =>
            {
                let mut substituted = items.clone();
                if let Some(bindings) = items.get(1).and_then(SExpr::as_list) {
                    substituted[1] = SExpr::List(
                        bindings
                            .iter()
                            .map(|binding| match binding.as_list() {
                                Some([name, sort]) => {
                                    let sort = ParsedSort::from_sexp(sort)
                                        .ok()
                                        .map(|sort| {
                                            parsed_sort_to_sexp(&substitute_sort(&sort, assignment))
                                        })
                                        .unwrap_or_else(|| sort.clone());
                                    SExpr::List(vec![name.clone(), sort])
                                }
                                _ => substitute_annotation_sexp(binding, assignment),
                            })
                            .collect(),
                    );
                }
                for item in substituted.iter_mut().skip(2) {
                    *item = substitute_annotation_sexp(item, assignment);
                }
                SExpr::List(substituted)
            }
            SExpr::List(items) => SExpr::List(
                items
                    .iter()
                    .map(|item| substitute_annotation_sexp(item, assignment))
                    .collect(),
            ),
            _ => value.clone(),
        },
    )
}

fn parsed_sort_to_sexp(sort: &ParsedSort) -> SExpr {
    match sort {
        ParsedSort::Simple(name) => SExpr::Symbol(name.clone()),
        ParsedSort::Parameterized(name, parameters) => {
            let mut items = Vec::with_capacity(parameters.len() + 1);
            items.push(SExpr::Symbol(name.clone()));
            items.extend(parameters.iter().map(parsed_sort_to_sexp));
            SExpr::List(items)
        }
        ParsedSort::Indexed(name, indices) => {
            let mut items = Vec::with_capacity(indices.len() + 2);
            items.push(SExpr::Symbol("_".to_string()));
            items.push(SExpr::Symbol(name.clone()));
            items.extend(indices.iter().map(|index| match index {
                Index::Numeral(value) => SExpr::Numeral(value.clone()),
                Index::Decimal(value) => SExpr::Decimal(value.clone()),
                Index::Symbol(value) => SExpr::Symbol(value.clone()),
                Index::Hexadecimal(value) => SExpr::Hexadecimal(value.clone()),
                Index::Binary(value) => SExpr::Binary(value.clone()),
            }));
            SExpr::List(items)
        }
    }
}

fn clone_qualified_identifier(identifier: &QualifiedIdentifier) -> QualifiedIdentifier {
    match identifier {
        QualifiedIdentifier::Symbol(name) => QualifiedIdentifier::Symbol(name.clone()),
        QualifiedIdentifier::Indexed(name, indices) => {
            QualifiedIdentifier::Indexed(name.clone(), indices.clone())
        }
    }
}

fn core_sort_to_parsed(sort: &Sort) -> Option<ParsedSort> {
    match sort {
        Sort::Bool => Some(ParsedSort::Simple("Bool".to_string())),
        Sort::Int => Some(ParsedSort::Simple("Int".to_string())),
        Sort::Real => Some(ParsedSort::Simple("Real".to_string())),
        Sort::String => Some(ParsedSort::Simple("String".to_string())),
        Sort::RegLan => Some(ParsedSort::Simple("RegLan".to_string())),
        Sort::BitVec(bit_vector) => Some(ParsedSort::Indexed(
            "BitVec".to_string(),
            vec![Index::Numeral(bit_vector.width.to_string())],
        )),
        Sort::Array(array) => Some(ParsedSort::Parameterized(
            "Array".to_string(),
            vec![
                core_sort_to_parsed(&array.index_sort)?,
                core_sort_to_parsed(&array.element_sort)?,
            ],
        )),
        Sort::Seq(element) => Some(ParsedSort::Parameterized(
            "Seq".to_string(),
            vec![core_sort_to_parsed(element)?],
        )),
        Sort::FloatingPoint(exponent, significand) => Some(ParsedSort::Indexed(
            "FloatingPoint".to_string(),
            vec![
                Index::Numeral(exponent.to_string()),
                Index::Numeral(significand.to_string()),
            ],
        )),
        Sort::Uninterpreted(name) | Sort::FiniteDomain(name, _) | Sort::TypeVar(name) => {
            Some(ParsedSort::Simple(name.clone()))
        }
        Sort::Datatype(datatype) => Some(ParsedSort::Simple(datatype.name.clone())),
        Sort::Char => Some(ParsedSort::Simple("Char".to_string())),
        _ => None,
    }
}

fn has_positive_arity_constructor(sort: &Sort) -> bool {
    matches!(
        sort,
        Sort::Array(_) | Sort::Seq(_) | Sort::BitVec(_) | Sort::FloatingPoint(_, _)
    )
}

fn parsed_sort_uses_positive_constructor(sort: &ParsedSort) -> bool {
    match sort {
        ParsedSort::Simple(_) => false,
        ParsedSort::Indexed(name, _) => matches!(name.as_str(), "BitVec" | "FloatingPoint"),
        ParsedSort::Parameterized(name, parameters) => {
            matches!(
                name.as_str(),
                "Array" | "Seq" | "Set" | "FiniteSet" | "Multiset" | "Map"
            ) || parameters.iter().any(parsed_sort_uses_positive_constructor)
        }
    }
}

fn logic_sort_universe(logic: Option<&str>) -> (Vec<Sort>, bool) {
    let bool_only = || (vec![Sort::Bool], true);
    let integers = || (vec![Sort::Bool, Sort::Int], true);
    let reals = || (vec![Sort::Bool, Sort::Real], true);
    let mixed = || (vec![Sort::Bool, Sort::Int, Sort::Real], true);
    let strings = || {
        (
            vec![Sort::Bool, Sort::Int, Sort::String, Sort::RegLan],
            true,
        )
    };

    match logic {
        Some("BOOL" | "QF_BOOL" | "QF_DT" | "QF_UF" | "QF_UFDT" | "UF" | "UFDT") => bool_only(),
        Some(
            "LIA" | "NIA" | "QF_EIA" | "QF_IDL" | "QF_LIA" | "QF_NIA" | "QF_UFIDL" | "QF_UFLIA"
            | "QF_UFNIA" | "UFLIA" | "UFNIA",
        ) => integers(),
        Some(
            "LRA" | "NRA" | "QF_LRA" | "QF_NRA" | "QF_RDL" | "QF_UFLRA" | "QF_UFNRA" | "UFLRA"
            | "UFNRA",
        ) => reals(),
        Some(
            "LIRA" | "NIRA" | "QF_LIRA" | "QF_NIRA" | "QF_UFLIRA" | "QF_UFNIRA" | "UFLIRA"
            | "UFNIRA",
        ) => mixed(),
        Some("QF_S" | "QF_SLIA" | "QF_SNIA") => strings(),
        Some("AUFLIRA" | "AUFNIRA") => {
            let (sorts, _) = mixed();
            (sorts, false)
        }
        Some("AUFLIA" | "QF_AUFLIA") => {
            let (sorts, _) = integers();
            (sorts, false)
        }
        Some("QF_ABV" | "QF_AUFBV" | "QF_AX" | "QF_BV" | "QF_UFBV" | "ALL") => {
            (vec![Sort::Bool], false)
        }
        // Without an authenticated logic-to-theory signature, Bool is the only
        // certain member.  A partial family must not receive a verdict.
        _ => (vec![Sort::Bool], false),
    }
}

fn current_logic_has_theory_sort(logic: Option<&str>, name: &str) -> bool {
    if name == "Bool" {
        return true;
    }
    if matches!(logic, Some("ALL" | "ALL_SUPPORTED")) {
        return matches!(
            name,
            "Array"
                | "BitVec"
                | "Char"
                | "FloatingPoint"
                | "Int"
                | "Real"
                | "RegLan"
                | "Seq"
                | "String"
        );
    }
    let has_int = matches!(
        logic,
        Some(
            "LIA"
                | "NIA"
                | "QF_EIA"
                | "QF_IDL"
                | "QF_LIA"
                | "QF_NIA"
                | "QF_UFIDL"
                | "QF_UFLIA"
                | "QF_UFNIA"
                | "UFLIA"
                | "UFNIA"
                | "AUFLIA"
                | "QF_AUFLIA"
                | "AUFLIRA"
                | "AUFNIRA"
                | "QF_S"
                | "QF_SEQ"
                | "QF_SEQLIA"
                | "QF_SLIA"
                | "QF_SNIA"
        )
    );
    let has_real = matches!(
        logic,
        Some(
            "LRA"
                | "NRA"
                | "QF_LRA"
                | "QF_NRA"
                | "QF_RDL"
                | "QF_UFLRA"
                | "QF_UFNRA"
                | "UFLRA"
                | "UFNRA"
                | "AUFLIRA"
                | "AUFNIRA"
                | "QF_ABVFP"
                | "QF_AFPBV"
                | "QF_BVFP"
                | "QF_FP"
                | "QF_FPLRA"
        )
    );
    let has_mixed_arithmetic = matches!(
        logic,
        Some(
            "LIRA"
                | "NIRA"
                | "QF_LIRA"
                | "QF_NIRA"
                | "QF_UFLIRA"
                | "QF_UFNIRA"
                | "UFLIRA"
                | "UFNIRA"
        )
    );
    let has_array = matches!(
        logic,
        Some(
            "AUFLIA"
                | "AUFLIRA"
                | "AUFLRA"
                | "AUFNIRA"
                | "QF_ABV"
                | "QF_AUFBV"
                | "QF_AUFLIA"
                | "QF_AUFLIRA"
                | "QF_AUFLRA"
                | "QF_ABVFP"
                | "QF_AFPBV"
                | "QF_AX"
        )
    );
    let has_bit_vector = matches!(
        logic,
        Some(
            "QF_ABV"
                | "QF_ABVFP"
                | "QF_AFPBV"
                | "QF_AUFBV"
                | "QF_BV"
                | "QF_BVFP"
                | "QF_FP"
                | "QF_FPLRA"
                | "QF_UFBV"
        )
    );
    (name == "Int" && (has_int || has_mixed_arithmetic))
        || (name == "Real" && (has_real || has_mixed_arithmetic))
        || (name == "Array" && has_array)
        || (name == "BitVec" && has_bit_vector)
        || (matches!(name, "String" | "RegLan")
            && matches!(logic, Some("QF_S" | "QF_SLIA" | "QF_SNIA")))
        || (name == "Seq" && matches!(logic, Some("QF_SEQ" | "QF_SEQBV" | "QF_SEQLIA")))
        || (name == "FloatingPoint"
            && matches!(
                logic,
                Some("QF_ABVFP" | "QF_AFPBV" | "QF_BVFP" | "QF_FP" | "QF_FPLRA")
            ))
}

fn is_core_theory_symbol(name: &str) -> bool {
    matches!(
        name,
        "Bool" | "true" | "false" | "not" | "=>" | "and" | "or" | "xor" | "=" | "distinct" | "ite"
    )
}

fn current_logic_has_theory_function(logic: Option<&str>, name: &str) -> bool {
    if is_core_theory_symbol(name) {
        return true;
    }
    let has_int = current_logic_has_theory_sort(logic, "Int");
    let has_real = current_logic_has_theory_sort(logic, "Real");
    if (has_int || has_real) && matches!(name, "+" | "-" | "~" | "*" | "<=" | "<" | ">=" | ">") {
        return true;
    }
    if has_int && matches!(name, "**" | "div" | "mod" | "abs") {
        return true;
    }
    if has_real && name == "/" {
        return true;
    }
    if has_int && has_real && matches!(name, "to_real" | "to_int" | "is_int" | "divisible") {
        return true;
    }
    if current_logic_has_theory_sort(logic, "Array") && matches!(name, "select" | "store") {
        return true;
    }
    if current_logic_has_theory_sort(logic, "BitVec")
        && (name.starts_with("bv")
            || matches!(
                name,
                "concat"
                    | "extract"
                    | "repeat"
                    | "zero_extend"
                    | "sign_extend"
                    | "rotate_left"
                    | "rotate_right"
            ))
    {
        return true;
    }
    if current_logic_has_theory_sort(logic, "String")
        && (name.starts_with("str.") || name.starts_with("re.") || name == "int.to.str")
    {
        return true;
    }
    if current_logic_has_theory_sort(logic, "Seq") && name.starts_with("seq.") {
        return true;
    }
    if current_logic_has_theory_sort(logic, "FloatingPoint")
        && (name.starts_with("fp.")
            || matches!(
                name,
                "RNE"
                    | "RNA"
                    | "RTP"
                    | "RTN"
                    | "RTZ"
                    | "roundNearestTiesToEven"
                    | "roundNearestTiesToAway"
                    | "roundTowardPositive"
                    | "roundTowardNegative"
                    | "roundTowardZero"
            ))
    {
        return true;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse, Command};

    fn assertion(source: &str) -> ParsedTerm {
        let commands = parse(source).expect("fixture parses");
        let [Command::Assert(term)] = commands.as_slice() else {
            panic!("fixture must contain one assertion")
        };
        term.clone()
    }

    #[test]
    fn annotation_only_sort_parameters_are_collected() {
        let term = assertion("(assert (! true :pattern ((as c X))))");
        let mut context = Context::new();
        context.sort_parameters.insert("X".to_string());
        assert_eq!(context.term_sort_parameters(&term), vec!["X".to_string()]);
    }

    #[test]
    fn substitution_reaches_qualified_sorts_inside_pattern_sexps() {
        let term = assertion("(assert (! true :pattern ((as c X))))");
        let assignment = HashMap::from_iter([(
            "X".to_string(),
            ParsedSort::Parameterized(
                "Array".to_string(),
                vec![
                    ParsedSort::Simple("Bool".to_string()),
                    ParsedSort::Simple("Int".to_string()),
                ],
            ),
        )]);
        let concrete = substitute_term(&term, &assignment);
        let ParsedTerm::Annotated(_, attributes) = &concrete else {
            panic!("annotation must be preserved")
        };
        assert_eq!(attributes.len(), 1);
        assert_eq!(attributes[0].1.to_raw_string(), "((as c (Array Bool Int)))");
    }

    #[test]
    fn substitution_reaches_binder_sorts_inside_annotation_sexps() {
        let term = assertion("(assert (! true :custom (forall ((x X)) true)))");
        let assignment =
            HashMap::from_iter([("X".to_string(), ParsedSort::Simple("Bool".to_string()))]);
        let concrete = substitute_term(&term, &assignment);
        let ParsedTerm::Annotated(_, attributes) = &concrete else {
            panic!("annotation must be preserved")
        };
        assert_eq!(attributes[0].1.to_raw_string(), "(forall ((x Bool)) true)");
    }
}
