// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed, caller-metered builtin signature checks, not UF authentication.

use super::*;

mod floating_point;
mod indexed;
mod meter;
mod named;
mod names;
#[cfg(test)]
mod tests;

use meter::App;

pub(super) fn validate_app_signature_with_progress(
    entries: &[(TermData, Sort)],
    node_index: usize,
    symbol: &Symbol,
    args: &[TermId],
    result_sort: &Sort,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mut app = App {
        entries,
        node_index,
        name: symbol.name(),
        args,
        result: result_sort,
        progress,
    };
    app.charge(0, 0)?;
    // Validate all handles, including arguments to unknown UFs. The enclosing
    // term pass separately establishes prior-child order and recorded sorts.
    for index in 0..args.len() {
        app.arg(index)?;
    }
    if matches!(symbol, Symbol::Named(_))
        && matches!(app.name, "ff.add" | "ff.mul" | "ff.neg" | "ff.bitsum")
    {
        if !matches!(app.result, Sort::FiniteField(_))
            || (if app.name == "ff.neg" {
                args.len() != 1
            } else {
                args.len() < 2
            })
        {
            return app.invalid("requires a field result and correct field operator arity");
        }
        for i in 0..args.len() {
            if app.arg(i)? != app.result {
                return app.invalid("has a mixed-field operand");
            }
        }
        return app.charge(0, 0);
    }
    match symbol {
        Symbol::Named(_) => {
            if !floating_point::named(&mut app)? {
                named::validate(&mut app)?;
            }
        }
        Symbol::Indexed(_, indices) => {
            if !floating_point::indexed(&mut app, indices)? {
                indexed::validate(&mut app, indices)?;
            }
        }
        // Preserve the legacy helper's opaque-symbol behavior. No payload is
        // copied and no uninterpreted-function signature is authenticated.
        _ => {}
    }
    app.charge(0, 0)
}
