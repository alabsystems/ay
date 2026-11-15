// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Z3-compatible C API's de Bruijn bound variables (`Z3_mk_bound`).
//!
//! AY encodes z3's bound variable `(:var k)` as a named `Var`. z3 lets the same
//! index occur at several sorts in one context (`Var(0, IntSort())` and
//! `Var(0, BoolSort())`), but one AY name has one sort, so the variable of
//! index `k` is `__db{k}` at the first sort it is used with and
//! `__db{k}:{j}` (j = 1, 2, ...) at each further sort. Declaring `__db{k}` at
//! a second sort used to panic in `declare_const` (measured: z3py `Var(0,
//! BoolSort())` raised after a model with an `Int` symbolic `else` was
//! printed).

use ay_core::{Sort, TermId};

use super::types::{SolverError, Term};
use super::Solver;

/// The most sorts one de Bruijn index may take in a context.
const MAX_SORTS_PER_INDEX: usize = 256;

/// The de Bruijn index a variable name encodes: `__db{k}` or `__db{k}:{j}`.
#[must_use]
pub fn de_bruijn_index(name: &str) -> Option<usize> {
    let rest = name.strip_prefix("__db")?;
    let (digits, variant) = match rest.split_once(':') {
        Some((digits, variant)) => (digits, Some(variant)),
        None => (rest, None),
    };
    let numeric = |text: &str| !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit());
    if !numeric(digits) || variant.is_some_and(|variant| !numeric(variant)) {
        return None;
    }
    digits.parse().ok()
}

fn de_bruijn_name(index: usize, variant: usize) -> String {
    if variant == 0 {
        format!("__db{index}")
    } else {
        format!("__db{index}:{variant}")
    }
}

impl Solver {
    /// The de Bruijn variable of `index` at `sort` (see the module docs),
    /// declared on first use.
    ///
    /// # Errors
    ///
    /// [`SolverError::InvalidArgument`] when the sort cannot be declared, or
    /// the index already has [`MAX_SORTS_PER_INDEX`] sorts.
    pub fn try_de_bruijn_var(&mut self, index: usize, sort: Sort) -> Result<Term, SolverError> {
        let mut last_error = None;
        for variant in 0..MAX_SORTS_PER_INDEX {
            let name = de_bruijn_name(index, variant);
            let taken = self.terms().lookup(&name).is_some();
            match self.try_declare_const(&name, sort.clone()) {
                Ok(term) => return Ok(term),
                // Another sort holds this spelling: try the next one.
                Err(error) if taken => last_error = Some(error),
                Err(error) => return Err(error),
            }
        }
        Err(last_error.unwrap_or(SolverError::InvalidArgument {
            operation: "de_bruijn_var",
            message: format!("bound variable {index} is used at too many sorts"),
        }))
    }

    /// Every interned de Bruijn variable of `index`, at every sort.
    pub(crate) fn de_bruijn_vars(&self, index: usize) -> Vec<TermId> {
        (0..MAX_SORTS_PER_INDEX)
            .map_while(|variant| self.terms().lookup(&de_bruijn_name(index, variant)))
            .collect()
    }

    /// The interned de Bruijn variable of `index` whose sort is `sort`'s.
    pub(crate) fn de_bruijn_var_of_sort(&self, index: usize, sort: &Sort) -> Option<TermId> {
        self.de_bruijn_vars(index)
            .into_iter()
            .find(|&var| self.terms().sort(var) == sort)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_index_takes_one_variable_per_sort() {
        assert_eq!(de_bruijn_index("__db3"), Some(3));
        assert_eq!(de_bruijn_index("__db3:2"), Some(3));
        assert_eq!(de_bruijn_index("__db"), None);
        assert_eq!(de_bruijn_index("__db3:"), None);
        assert_eq!(de_bruijn_index("__dbx"), None);
        let mut solver = Solver::new(crate::api::Logic::All);
        let int = solver.try_de_bruijn_var(0, Sort::Int).expect("Int");
        let boolean = solver.try_de_bruijn_var(0, Sort::Bool).expect("Bool");
        assert_ne!(int, boolean);
        assert_eq!(
            solver.try_de_bruijn_var(0, Sort::Int).expect("Int again"),
            int
        );
        assert_eq!(solver.term_sort(boolean), Sort::Bool);
        assert_eq!(solver.de_bruijn_vars(0).len(), 2);
    }
}
