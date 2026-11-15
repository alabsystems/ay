// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Spelling a reconstructed array cell whose value is itself an array.

use ay_core::Sort;

use super::Executor;

impl Executor {
    /// The printed spelling of one reconstructed `ArrayInterpretation` cell
    /// value: `Ok(Some)` to print, `Ok(None)` to leave out (a non-printable
    /// datatype representative the direct-read scan already captured
    /// concretely, #model-witness-no-skolem), `Err` when the witness cannot be
    /// printed without it — an ARRAY-valued cell with no printable spelling
    /// is a cell of this array the witness would silently drop.
    pub(super) fn printable_reconstructed_cell(
        &self,
        raw: &str,
        elem_sort: &Sort,
    ) -> Result<Option<String>, ()> {
        if !raw.contains('@') {
            return Ok(Some(raw.to_string()));
        }
        match self
            .printable_uninterpreted_atom(raw, elem_sort)
            .or_else(|| self.printable_rendered_array_value(raw, elem_sort))
        {
            Some(spelled) => Ok(Some(spelled)),
            None if matches!(elem_sort, Sort::Array(_)) => Err(()),
            None => Ok(None),
        }
    }

    /// An ARRAY value the array model already rendered, when every internal
    /// atom in it is a printable uninterpreted-sort value in its sort-ascribed
    /// spelling (`(as @Elem!0 Elem)`).
    ///
    /// A nested array's cell holds an array, and the array model records that
    /// cell's value as the rendered array text, e.g. `(store ((as const (Array
    /// Index Elem)) (as @Elem!0 Elem)) (as @Index!4 Index) (as @Elem!2 Elem))`.
    /// That text carries `@` atoms, and the reconstruction below used to drop
    /// every `@`-bearing cell whose text was not ITSELF a single printable atom
    /// — so every cell of an `(Array I (Array I E))` over uninterpreted sorts
    /// was dropped, and the printed witness collapsed to a bare const array.
    /// Measured on `r3_rank4_qf_ax__nested_arrays__array_index__array_index_elem`
    /// (QF_AX, satisfiable): `(get-model)` printed `n1` and `n2` identically
    /// while assertion 2 is `(not (= n2 n1))`, falsifying 2 of the 3 assertions,
    /// and `(get-value ((select n1 i1)))` contradicted the printed `n1`. The
    /// model gate read the internal interpretation and confirmed it; only the
    /// printed witness was wrong.
    ///
    /// `None` for any other `@` atom (a nested-array name, a datatype
    /// representative): that text is not a value and must not be printed.
    pub(super) fn printable_rendered_array_value(&self, raw: &str, sort: &Sort) -> Option<String> {
        if !matches!(sort, Sort::Array(_)) {
            return None;
        }
        let mut rest = raw;
        while let Some(at) = rest.find('@') {
            // Each atom must sit exactly in `(as @S!k S)`.
            if !rest[..at].ends_with("(as ") {
                return None;
            }
            let after = &rest[at + 1..];
            let close = after.find(')')?;
            let ascription = &after[..close];
            let (atom, ascribed_sort) = ascription.split_once(' ')?;
            let (atom_sort, digits) = atom.rsplit_once('!')?;
            if atom_sort != ascribed_sort
                || digits.is_empty()
                || !digits.bytes().all(|b| b.is_ascii_digit())
            {
                return None;
            }
            let atom_sort = Sort::Uninterpreted(atom_sort.to_string());
            self.printable_uninterpreted_atom(&format!("@{atom}"), &atom_sort)?;
            rest = &after[close + 1..];
        }
        Some(raw.to_string())
    }
}
