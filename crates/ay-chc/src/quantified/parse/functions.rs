// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-declared scalar functions. The vector preserves declaration order
//! and unused symbols; the map is only a parse-time exact-name lookup index.
//! No UF declaration or application is lowered to a clause-local variable.

use super::*;

#[derive(Default)]
pub(super) struct FunctionState {
    pub(super) declarations: Vec<QuantifiedChcFunction>,
    indices: BTreeMap<String, usize>,
}

impl FunctionState {
    pub(super) fn contains(&self, name: &str) -> bool {
        self.indices.contains_key(name)
    }

    fn get(&self, name: &str) -> Option<&QuantifiedChcFunction> {
        self.declarations.get(*self.indices.get(name)?)
    }
}

fn scalar(sort: &ChcSort) -> bool {
    matches!(
        sort,
        ChcSort::Bool | ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)
    )
}

fn scalar_syntax(expr: &SExpr) -> ChcResult<ChcSort> {
    // Reject composite metadata before value::sort can allocate array boxes.
    if !expr.is_symbol("Bool")
        && !matches!(expr.as_list(), Some([marker, name, _])
            if marker.is_symbol("_") && name.is_symbol("BitVec"))
    {
        return Err(invalid("function signature requires scalar Bool/BV sorts"));
    }
    value::sort(expr)
}

impl Parser<'_> {
    pub(super) fn check_declaration_limit(&self) -> ChcResult<()> {
        let count = self
            .declarations
            .predicates()
            .len()
            .checked_add(self.functions.declarations.len())
            .ok_or_else(|| invalid("term declaration count limit"))?;
        if count >= super::super::source::MAX_DECLARATIONS {
            return Err(invalid("term declaration count limit"));
        }
        Ok(())
    }

    pub(super) fn function_declaration(
        &mut self,
        name: &SExpr,
        arguments: &SExpr,
        result: &SExpr,
    ) -> ChcResult<()> {
        self.check_declaration_limit()?;
        let name = self.declaration_name(name)?;
        let arguments = list(arguments)?;
        let result = scalar_syntax(result)?;
        if !matches!(result, ChcSort::BitVec(_)) {
            return Err(invalid("ordinary function result must be a bitvector"));
        }
        // Function record + map node + both owned names and the argument
        // vector are charged before allocation. No separate arity knob: all
        // signatures share the existing parser/source work and copy ledgers.
        let bytes = arguments
            .len()
            .checked_mul(std::mem::size_of::<ChcSort>().max(128))
            .and_then(|n| n.checked_add(2 * std::mem::size_of::<QuantifiedChcFunction>() + 256))
            .and_then(|n| n.checked_add(name.len().checked_mul(2)?))
            .ok_or_else(|| invalid("function signature copy limit"))?;
        self.budget.charge(arguments.len() + 1, bytes)?;
        self.budget.sort_copy(&result)?;
        let mut sorts = Vec::new();
        sorts
            .try_reserve_exact(arguments.len())
            .map_err(|_| invalid("function signature allocation"))?;
        for argument in arguments {
            let sort = scalar_syntax(argument)?;
            self.budget.sort_copy(&sort)?;
            sorts.push(sort);
        }
        self.functions
            .declarations
            .try_reserve_exact(1)
            .map_err(|_| invalid("function declaration allocation"))?;
        self.functions
            .indices
            .insert(name.clone(), self.functions.declarations.len());
        self.functions
            .declarations
            .push(QuantifiedChcFunction::new(name, sorts, result));
        Ok(())
    }

    pub(super) fn function_application(
        &mut self,
        name: &str,
        arguments: Vec<Arc<ChcExpr>>,
        sorts: &[ChcSort],
    ) -> ChcResult<(Arc<ChcExpr>, ChcSort)> {
        self.budget.name(name)?;
        self.budget.charge(sorts.len() + 1, 256)?;
        if arguments.len() != sorts.len() || !sorts.iter().all(scalar) {
            return Err(invalid(
                "function operands must be scalar and consistently typed",
            ));
        }
        let declaration = self
            .functions
            .get(name)
            .ok_or_else(|| invalid("undeclared function"))?;
        // Both sides contain only shallow authenticated Bool/BV metadata.
        if declaration.arg_sorts() != sorts {
            return Err(invalid("function argument arity or sort mismatch"));
        }
        let sort = declaration.result_sort();
        self.budget.sort_copy(sort)?;
        self.budget.sort_copy(sort)?;
        Ok((
            Arc::new(ChcExpr::FuncApp(name.to_owned(), sort.clone(), arguments)),
            sort.clone(),
        ))
    }
}

#[cfg(test)]
mod tests;
