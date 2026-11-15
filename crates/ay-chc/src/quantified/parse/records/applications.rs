// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ChcOp;

impl Parser<'_> {
    pub(in super::super) fn source_application(
        &mut self,
        head: &SExpr,
        args: Vec<Arc<ChcExpr>>,
        sorts: &[ChcSort],
    ) -> ChcResult<(Arc<ChcExpr>, ChcSort)> {
        if args.len() != sorts.len() {
            return Err(invalid("inconsistent application arguments"));
        }
        if let Some([qualifier, name, declared]) = head.as_list() {
            if qualifier.is_symbol("as") && name.is_symbol("const") {
                // Preserve the old scalar-array parser's charges and shape.
                if value::sort(declared).is_ok()
                    && sorts
                        .iter()
                        .all(crate::quantified::records::scalar_array_sort)
                {
                    return value::application(head, args, sorts);
                }
                return self.source_const_array(declared, args, sorts);
            }
            if qualifier.is_symbol("as") && !name.is_symbol("const") {
                let name = symbol(name)?;
                if self.bindings.contains_key(name) {
                    return Err(invalid(
                        "a lexical variable or let alias is not a record operation",
                    ));
                }
                let declared = self.source_sort(declared)?;
                if !matches!(declared, ChcSort::Datatype { .. }) {
                    return Err(invalid("qualified record operation requires a record sort"));
                }
                let (value, actual) = self.record_application(name, args, sorts)?;
                if actual != declared {
                    return Err(invalid("qualified record operation result sort mismatch"));
                }
                return Ok((value, actual));
            }
        }
        if let Some(name) = head.as_symbol() {
            if self.functions.contains(name) {
                return self.function_application(name, args, sorts);
            }
            if self
                .records
                .registry
                .as_ref()
                .is_some_and(|r| r.contains_term_symbol(name))
            {
                return self.record_application(name, args, sorts);
            }
        }
        if sorts
            .iter()
            .any(|sort| !crate::quantified::records::scalar_array_sort(sort))
        {
            return self.record_operation(head, args, sorts);
        }
        // The old scalar/array helper keeps its untrusted-sort preflight.
        value::application(head, args, sorts)
    }

    fn source_const_array(
        &mut self,
        declaration: &SExpr,
        mut args: Vec<Arc<ChcExpr>>,
        sorts: &[ChcSort],
    ) -> ChcResult<(Arc<ChcExpr>, ChcSort)> {
        let declared = self.source_sort(declaration)?;
        let ChcSort::Array(key, element) = &declared else {
            return Err(invalid("constant array requires an array sort"));
        };
        for sort in sorts {
            self.budget.sort_copy(sort)?;
        }
        if !matches!(sorts, [actual] if actual == element.as_ref()) {
            return Err(invalid("constant array value sort or arity mismatch"));
        }
        let value = args
            .pop()
            .ok_or_else(|| invalid("constant array needs one value"))?;
        Ok((
            Arc::new(ChcExpr::ConstArray(key.as_ref().clone(), value)),
            declared,
        ))
    }

    fn record_application(
        &mut self,
        name: &str,
        args: Vec<Arc<ChcExpr>>,
        sorts: &[ChcSort],
    ) -> ChcResult<(Arc<ChcExpr>, ChcSort)> {
        self.budget.name(name)?;
        for sort in sorts {
            self.budget.sort_copy(sort)?;
        }
        self.budget
            .charge(self.records.count + 1, self.records.max_sort_bytes)?;
        let registry = self
            .records
            .registry
            .as_ref()
            .ok_or_else(|| invalid("missing record registry"))?;
        let sort = registry.application(name, sorts)?;
        self.budget.sort_copy(&sort)?;
        Ok((
            Arc::new(ChcExpr::FuncApp(name.to_owned(), sort.clone(), args)),
            sort,
        ))
    }

    fn record_operation(
        &mut self,
        head: &SExpr,
        args: Vec<Arc<ChcExpr>>,
        sorts: &[ChcSort],
    ) -> ChcResult<(Arc<ChcExpr>, ChcSort)> {
        let empty_registry;
        let registry = match self.records.registry.as_ref() {
            Some(registry) => registry,
            None => {
                empty_registry = Registry::new(&self.declarations)?;
                &empty_registry
            }
        };
        for sort in sorts {
            self.budget.sort_copy(sort)?;
            registry.validate_sort(sort)?;
        }
        let op = match head.as_symbol() {
            Some("=") => ChcOp::Eq,
            Some("distinct") => ChcOp::Ne,
            Some("ite") => ChcOp::Ite,
            Some("select") => ChcOp::Select,
            Some("store") => ChcOp::Store,
            _ => return Err(invalid("unsupported record operation")),
        };
        // Signature equality is now bounded and every record operand agrees
        // with a declaration. Keep raw equality/ITE without constructor folds.
        let sort = crate::pdr::validate_qf_operation(op, sorts)?;
        self.budget.sort_copy(&sort)?;
        registry.validate_sort(&sort)?;
        Ok((Arc::new(ChcExpr::Op(op, args)), sort))
    }
}
