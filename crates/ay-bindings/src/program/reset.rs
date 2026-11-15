// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! AYProgram state accessors and command-reset logic.

use super::AYProgram;
use crate::constraint::Constraint;
use crate::sort::{DatatypeSort, Sort, SortInner};

impl AYProgram {
    /// The registered datatype definitions, each after the registered
    /// definitions its fields nest (through arrays and sequences), so that
    /// re-emitting them declares every name before its first use.
    fn datatype_declarations_in_dependency_order(&self) -> Vec<DatatypeSort> {
        let mut ordered = Vec::with_capacity(self.declared_datatypes.len());
        let mut emitted = std::collections::BTreeSet::new();
        for definition in self.declared_datatypes.values() {
            let mut stack = vec![(definition, false)];
            while let Some((definition, fields_done)) = stack.pop() {
                let Some(dt) = definition.datatype_sort() else {
                    continue;
                };
                if emitted.contains(&dt.name) {
                    continue;
                }
                if fields_done {
                    emitted.insert(dt.name.clone());
                    ordered.push(dt.clone());
                    continue;
                }
                stack.push((definition, true));
                let mut fields: Vec<&Sort> = dt
                    .constructors
                    .iter()
                    .flat_map(|ctor| &ctor.fields)
                    .map(|field| &field.sort)
                    .collect();
                while let Some(sort) = fields.pop() {
                    match sort.inner() {
                        SortInner::Datatype(nested) => {
                            if let Some(registered) = self.declared_datatypes.get(&nested.name) {
                                stack.push((registered, false));
                            }
                        }
                        SortInner::Array(array) => {
                            fields.push(&array.index_sort);
                            fields.push(&array.element_sort);
                        }
                        SortInner::Seq(element) => fields.push(element),
                        _ => {}
                    }
                }
            }
        }
        ordered
    }

    /// Get program-level solver options (used by execute_direct).
    #[must_use]
    pub fn options(&self) -> &[(String, String)] {
        &self.options
    }

    /// Get all commands (used by execute_direct feature).
    #[must_use]
    pub fn commands(&self) -> &[Constraint] {
        &self.commands
    }

    /// Get the current context level.
    #[must_use]
    pub fn context_level(&self) -> u32 {
        self.context_level
    }

    /// Clear all commands but keep declarations.
    ///
    /// Removes all assertions, check-sat, push/pop, and other non-declaration
    /// commands. Re-adds all tracked declarations: datatypes, constants,
    /// functions, CHC relations, and CHC variables.
    pub fn clear_commands(&mut self) {
        self.commands.clear();
        self.context_level = 0;
        // Re-add datatype declarations first (other declarations may reference
        // these sorts), each after the definitions its fields nest.
        for dt in self.datatype_declarations_in_dependency_order() {
            self.commands.push(Constraint::declare_datatype(dt));
        }
        // Re-add constant declarations
        for (name, sort) in &self.declared_vars {
            self.commands
                .push(Constraint::declare_const(name.clone(), sort.clone()));
        }
        // Re-add function declarations
        for (name, arg_sorts, return_sort) in &self.declared_funs {
            self.commands.push(Constraint::declare_fun(
                name.clone(),
                arg_sorts.clone(),
                return_sort.clone(),
            ));
        }
        // Re-add function definitions
        for (name, params, return_sort, body) in &self.defined_funs {
            self.commands.push(Constraint::define_fun_with_sort(
                name.clone(),
                params.clone(),
                return_sort.clone(),
                body.clone(),
            ));
        }
        // Re-add CHC relation declarations
        for (name, arg_sorts) in &self.declared_rels {
            self.commands
                .push(Constraint::declare_rel(name.clone(), arg_sorts.clone()));
        }
        // Re-add CHC variable declarations
        for (name, sort) in &self.declared_chc_vars {
            self.commands
                .push(Constraint::declare_var(name.clone(), sort.clone()));
        }
    }
}
