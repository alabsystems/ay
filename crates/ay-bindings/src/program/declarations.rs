// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! AYProgram declaration tracking — constants, functions, datatypes.

use super::AYProgram;
use crate::constraint::Constraint;
use crate::error::SortError;
use crate::expr::dt::{authenticate_definitions, Unregistered};
use crate::expr::Expr;
use crate::sort::{DatatypeSort, Sort, SortInner};

impl AYProgram {
    /// Declare a constant (symbolic variable).
    ///
    /// Returns an expression referencing the variable.
    ///
    /// # Panics
    ///
    /// Panics where [`AYProgram::try_declare_const`] refuses: a datatype in
    /// the sort that differs from the declaration registered under its name,
    /// or a dangling datatype reference.
    #[must_use]
    pub fn declare_const(&mut self, name: impl Into<String>, sort: Sort) -> Expr {
        self.try_declare_const(name, sort)
            .expect("declare_const requires the sort to agree with the declared datatypes")
    }

    /// Fallible constant declaration: the sort agrees with the datatype
    /// registry.
    ///
    /// Every datatype definition in `sort` (the sort itself, an array or
    /// sequence element, a field of an inlined sibling) must be structurally
    /// equal to the definition registered under its name; a definition whose
    /// name is not registered yet is registered here, and declared before the
    /// constant, exactly as [`AYProgram::try_declare_datatype`] would. A
    /// definition that differs from the registered one, or a datatype
    /// reference outside a declaration of its name, is refused: the checked
    /// expression API authenticates terms against the descriptor on the
    /// variable's sort, and the native lowering resolves that descriptor by
    /// name from this registry.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_declare_const(
        &mut self,
        name: impl Into<String>,
        sort: Sort,
    ) -> Result<Expr, SortError> {
        let name = name.into();
        self.register_definitions("declare_const", &sort)?;
        self.declared_vars.insert(name.clone(), sort.clone());
        self.commands
            .push(Constraint::declare_const(&name, sort.clone()));
        Ok(Expr::var(name, sort))
    }

    /// Authenticate every datatype definition in `sort` against the registry
    /// and register (and declare, in dependency order) the ones that are
    /// new. Returns whether anything was new.
    fn register_definitions(
        &mut self,
        operation: &'static str,
        sort: &Sort,
    ) -> Result<bool, SortError> {
        let new = authenticate_definitions(
            operation,
            sort,
            &self.declared_datatypes,
            Unregistered::Register,
        )?;
        let declared = !new.is_empty();
        let new: Vec<Sort> = new.into_iter().cloned().collect();
        for definition in new {
            let Some(dt) = definition.datatype_sort() else {
                continue;
            };
            self.declared_datatypes
                .insert(dt.name.clone(), definition.clone());
            self.commands.push(Constraint::declare_datatype(dt.clone()));
        }
        Ok(declared)
    }

    /// Declare a function.
    pub fn declare_fun(
        &mut self,
        name: impl Into<String>,
        arg_sorts: Vec<Sort>,
        return_sort: Sort,
    ) {
        let name = name.into();
        self.declared_funs
            .push((name.clone(), arg_sorts.clone(), return_sort.clone()));
        self.commands
            .push(Constraint::declare_fun(name, arg_sorts, return_sort));
    }

    /// Define a transparent non-recursive function.
    ///
    /// The definition is emitted as SMT-LIB `(define-fun ...)`. Applications
    /// can be built with [`Expr::func_app_with_sort`].
    pub fn define_fun(&mut self, name: impl Into<String>, params: Vec<(String, Sort)>, body: Expr) {
        let constraint = Constraint::define_fun(name.into(), params, body);
        if let Constraint::DefineFun {
            name,
            params,
            return_sort,
            body,
        } = &constraint
        {
            self.defined_funs.push((
                name.clone(),
                params.clone(),
                return_sort.clone(),
                body.clone(),
            ));
        }
        self.commands.push(constraint);
    }

    /// Declare a datatype if not already declared.
    ///
    /// Returns true if the datatype was declared, false if the same
    /// declaration already was.
    ///
    /// # Panics
    ///
    /// Panics where [`AYProgram::try_declare_datatype`] refuses: a different
    /// datatype already declared under the name, a malformed declaration, or a
    /// field reference that names no enclosing datatype.
    pub fn declare_datatype(&mut self, datatype: DatatypeSort) -> bool {
        self.try_declare_datatype(datatype)
            .expect("declare_datatype requires one well-formed datatype definition per name")
    }

    /// Fallible datatype declaration: one definition per name.
    ///
    /// Returns `Ok(true)` when the datatype is newly declared and `Ok(false)`
    /// when an equal declaration (compared structurally, with field references
    /// resolved to the declaration they name) already exists. A different
    /// declaration under the same name is refused rather than dropped: the
    /// checked expression API authenticates a term against the descriptor on
    /// its own sort, and the native lowering then resolves the descriptor by
    /// name from this registry, so those two must never disagree.
    ///
    /// The same rule holds for every datatype definition nested in the field
    /// sorts (through arrays and sequences): one named like an enclosing
    /// declaration must be that declaration unfolded, not a same-named
    /// definition shadowing it; one whose name is registered must equal the
    /// registered definition; one whose name is new is registered as a
    /// definition in its own right and declared before this datatype, so a
    /// later different definition of that name conflicts. A declaration with
    /// an empty or ambiguous constructor list, a field reference naming no
    /// enclosing datatype, or a nested definition referring back to a
    /// datatype enclosing it (mutual recursion between separately declared
    /// datatypes) is refused here, not only at execution.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_declare_datatype(&mut self, datatype: DatatypeSort) -> Result<bool, SortError> {
        let sort = Sort::from_inner(SortInner::Datatype(datatype));
        self.register_definitions("declare_datatype", &sort)
    }

    /// Check if a datatype has been declared.
    #[must_use]
    pub fn is_datatype_declared(&self, name: &str) -> bool {
        self.declared_datatypes.contains_key(name)
    }

    /// Check if any datatypes have been declared (used by execute_direct feature).
    #[must_use]
    pub fn has_datatypes(&self) -> bool {
        !self.declared_datatypes.is_empty()
    }

    /// Upgrade logic to ALL if current logic doesn't support datatypes.
    ///
    /// # Datatype Logic Policy
    ///
    /// When algebraic datatypes are declared:
    /// 1. If no logic is set, defaults to `ALL`
    /// 2. If logic is `HORN`, no upgrade (CHC semantics)
    /// 3. If logic contains `DT` or is `ALL`/`ALL_SUPPORTED`, no upgrade
    /// 4. Otherwise, upgrades to `ALL`
    ///
    /// This ensures solvers can process datatype declarations.
    ///
    /// # Rationale
    ///
    /// Many standard logics (QF_BV, QF_AUFBV) don't support algebraic datatypes.
    /// `ALL` is universally supported by modern SMT solvers. HORN logic is not
    /// upgraded as it has different semantics (CHC solving with Spacer/PDR).
    pub fn upgrade_logic_for_datatypes(&mut self) {
        if self.has_datatypes() {
            match &self.logic {
                None => {
                    // Rule 1: Set default when unset
                    self.logic = Some("ALL".to_string());
                }
                Some(logic) if logic == "HORN" => {
                    // Rule 3: Never upgrade HORN (CHC semantics)
                }
                Some(logic)
                    if logic.contains("DT") || logic == "ALL" || logic == "ALL_SUPPORTED" =>
                {
                    // Already datatype-capable, no upgrade needed
                }
                Some(_) => {
                    // Rule 2: Upgrade non-DT logics to ALL
                    self.logic = Some("ALL".to_string());
                }
            }
        }
    }

    /// Check if a variable has been declared.
    #[must_use]
    pub fn is_declared(&self, name: &str) -> bool {
        self.declared_vars.contains_key(name)
    }

    /// Get the sort of a declared variable.
    #[must_use]
    pub fn get_sort(&self, name: &str) -> Option<&Sort> {
        self.declared_vars.get(name)
    }
}
