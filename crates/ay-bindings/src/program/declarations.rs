// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! AYProgram declaration tracking — constants, functions, datatypes.

use super::AYProgram;
use crate::constraint::Constraint;
use crate::expr::Expr;
use crate::sort::{DatatypeSort, Sort};

impl AYProgram {
    /// Declare a constant (symbolic variable).
    ///
    /// Returns an expression referencing the variable.
    #[must_use]
    pub fn declare_const(&mut self, name: impl Into<String>, sort: Sort) -> Expr {
        let name = name.into();
        self.declared_vars.insert(name.clone(), sort.clone());
        self.commands
            .push(Constraint::declare_const(&name, sort.clone()));
        Expr::var(name, sort)
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
    /// Returns true if the datatype was declared, false if already declared.
    pub fn declare_datatype(&mut self, datatype: DatatypeSort) -> bool {
        if self.declared_datatypes.contains_key(&datatype.name) {
            return false;
        }
        self.declared_datatypes
            .insert(datatype.name.clone(), datatype.clone());
        self.commands.push(Constraint::declare_datatype(datatype));
        true
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
