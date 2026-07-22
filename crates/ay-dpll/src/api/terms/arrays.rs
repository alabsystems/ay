// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Create an array select (read) operation: select(array, index).
    ///
    /// # Panics
    /// Panics if `array` is not an array sort or `index` sort does not match
    /// the array's index sort. Use [`Self::try_select`] for a fallible version.
    pub fn select(&mut self, array: Term, index: Term) -> Term {
        self.try_select(array, index)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Create an array store (write) operation: store(array, index, value).
    ///
    /// Returns a new array that is identical to `array` except at `index`,
    /// where it maps to `value`.
    ///
    /// # Panics
    /// Panics if `array` is not an array sort, `index` sort does not match
    /// the array's index sort, or `value` sort does not match the array's
    /// element sort. Use [`Self::try_store`] for a fallible version.
    pub fn store(&mut self, array: Term, index: Term, value: Term) -> Term {
        self.try_store(array, index, value)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Create a constant array where every index maps to the same value.
    ///
    /// # Panics
    /// This method cannot fail as it constructs a valid array from any index sort
    /// and value. Use [`Self::try_const_array`] for API consistency with other
    /// fallible array operations.
    pub fn const_array(&mut self, index_sort: Sort, value: Term) -> Term {
        self.try_const_array(index_sort, value)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an array select (read) operation.
    ///
    /// Fallible version of [`select`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if:
    /// - `array` is not an array sort
    /// - `index` sort does not match the array's index sort
    ///
    /// [`select`]: Solver::select
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_select(&mut self, array: Term, index: Term) -> Result<Term, SolverError> {
        let array_sort = self.terms().sort(array.0).clone();
        let index_sort = self.terms().sort(index.0).clone();

        match &array_sort {
            Sort::Array(arr) => {
                if index_sort != arr.index_sort {
                    return Err(SolverError::SortMismatch {
                        operation: "select",
                        expected: "index sort matching array index sort",
                        got: vec![index_sort],
                    });
                }
                Ok(Term(self.terms_mut().mk_select(array.0, index.0)))
            }
            _ => Err(SolverError::SortMismatch {
                operation: "select",
                expected: "Array",
                got: vec![array_sort],
            }),
        }
    }

    /// Try to create an array store (write) operation.
    ///
    /// Fallible version of [`store`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if:
    /// - `array` is not an array sort
    /// - `index` sort does not match the array's index sort
    /// - `value` sort does not match the array's element sort
    ///
    /// [`store`]: Solver::store
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_store(
        &mut self,
        array: Term,
        index: Term,
        value: Term,
    ) -> Result<Term, SolverError> {
        let array_sort = self.terms().sort(array.0).clone();
        let index_sort = self.terms().sort(index.0).clone();
        let value_sort = self.terms().sort(value.0).clone();

        match &array_sort {
            Sort::Array(arr) => {
                if index_sort != arr.index_sort {
                    return Err(SolverError::SortMismatch {
                        operation: "store",
                        expected: "index sort matching array index sort",
                        got: vec![index_sort],
                    });
                }
                if value_sort != arr.element_sort {
                    return Err(SolverError::SortMismatch {
                        operation: "store",
                        expected: "value sort matching array element sort",
                        got: vec![value_sort],
                    });
                }
                Ok(Term(self.terms_mut().mk_store(array.0, index.0, value.0)))
            }
            _ => Err(SolverError::SortMismatch {
                operation: "store",
                expected: "Array",
                got: vec![array_sort],
            }),
        }
    }

    /// Try to create a constant array.
    ///
    /// Fallible version of [`const_array`]. Returns an error instead of panicking.
    ///
    /// Note: This method cannot fail for valid inputs, but is provided for API
    /// consistency with other array operations.
    ///
    /// [`const_array`]: Solver::const_array
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_const_array(&mut self, index_sort: Sort, value: Term) -> Result<Term, SolverError> {
        Ok(Term(
            self.terms_mut()
                .mk_const_array(index_sort.as_term_sort(), value.0),
        ))
    }
}
