// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded print-faithful interning of binder-free authored terms.

use ay_core::{Symbol, TermId};
use ay_frontend::command::{Index as FrontendIndex, Term as FrontendTerm};

use super::Executor;
use crate::executor::proof_surface_syntax::strip_frontend_annotations;
use crate::executor::proof_trust_surgery_provenance::surface_source_is_bounded;

impl Executor {
    /// Raw-intern a surface term so it prints exactly like the problem file
    /// even where elaboration folds it. Unsupported binders and over-budget
    /// source trees fail closed before recursive elaboration.
    pub(in crate::executor) fn raw_intern_surface(
        &mut self,
        surface: &FrontendTerm,
    ) -> Option<TermId> {
        if !surface_source_is_bounded(surface) {
            return None;
        }
        self.raw_intern_surface_prechecked(surface)
    }

    fn raw_intern_surface_prechecked(&mut self, surface: &FrontendTerm) -> Option<TermId> {
        let stripped = strip_frontend_annotations(surface);
        match stripped {
            FrontendTerm::Symbol(_) | FrontendTerm::Const(_) => {
                self.ctx.elaborate_surface_subterm(stripped)
            }
            FrontendTerm::App(head, arguments) => {
                let elaborated = self.ctx.elaborate_surface_subterm(stripped)?;
                // Source spelling is not declaration authority. If a user
                // declaration shadows a builtin-looking head (`=`, `rem`,
                // `to_int`, ...), retain the exact private core identity that
                // elaboration selected rather than rebuilding the canonical
                // builtin with the same text.
                let declared_symbol = self
                    .authenticated_surface_application_symbol(head, elaborated)
                    .ok()?;
                let raw_arguments = arguments
                    .iter()
                    .map(|argument| self.raw_intern_surface_prechecked(argument))
                    .collect::<Option<Vec<TermId>>>()?;
                let sort = self.ctx.terms.sort(elaborated).clone();
                if let Some(symbol) = declared_symbol {
                    return Some(self.ctx.terms.mk_app(symbol, raw_arguments, sort));
                }
                if head == "not" && raw_arguments.len() == 1 {
                    return Some(self.ctx.terms.mk_not_raw(raw_arguments[0]));
                }
                if head == "ite" && raw_arguments.len() == 3 {
                    return Some(self.ctx.terms.mk_ite_raw(
                        raw_arguments[0],
                        raw_arguments[1],
                        raw_arguments[2],
                    ));
                }
                Some(
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(head), raw_arguments, sort),
                )
            }
            FrontendTerm::IndexedApp(name, indices, arguments) => {
                let elaborated = self.ctx.elaborate_surface_subterm(stripped)?;
                // SMT-LIB datatype tester `((_ is C) t)`. Its index is a
                // CONSTRUCTOR SYMBOL, not a numeral, so the numeric-index path
                // below fails closed on it and the whole enclosing assertion
                // loses its raw re-intern — the #raw-intern-head-cliff failure
                // mode, one level down. That cliff is what denies a QF_DT
                // fold-to-`false` refutation any recorded argument at all
                // (`authored_conjunct_eval`): the conjunct that made the
                // assertion false IS a tester application.
                //
                // Rebuild it exactly as the elaborator names it — `is-C` from
                // the index symbol (`elaborate_indexed_app`) — and re-read the
                // result so a store that folded it fails closed. This grants
                // no new authority: the term is rebuilt node-by-node from an
                // assertion THE AUTHOR WROTE, which is the same grant every
                // other arm of this function makes.
                if name == "is" && arguments.len() == 1 {
                    let [FrontendIndex::Symbol(constructor)] = indices.as_slice() else {
                        return None;
                    };
                    let raw_argument = self.raw_intern_surface_prechecked(&arguments[0])?;
                    let sort = self.ctx.terms.sort(elaborated).clone();
                    let tester = Symbol::named(format!("is-{constructor}"));
                    let rebuilt = self
                        .ctx
                        .terms
                        .mk_app(tester.clone(), vec![raw_argument], sort);
                    return matches!(
                        self.ctx.terms.get(rebuilt),
                        ay_core::term::TermData::App(symbol, args)
                            if *symbol == tester && args.as_slice() == [raw_argument]
                    )
                    .then_some(rebuilt);
                }
                if arguments.is_empty() {
                    let [FrontendIndex::Numeral(width)] = indices.as_slice() else {
                        return None;
                    };
                    let value = name.strip_prefix("bv")?;
                    if value.is_empty()
                        || !value.bytes().all(|byte| byte.is_ascii_digit())
                        || width.parse::<u32>().ok().is_none_or(|bits| bits == 0)
                    {
                        return None;
                    }
                    return Some(elaborated);
                }
                let numeric_indices = indices
                    .iter()
                    .map(|index| match index {
                        FrontendIndex::Numeral(value) => value.parse::<u32>().ok(),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()?;
                let raw_arguments = arguments
                    .iter()
                    .map(|argument| self.raw_intern_surface_prechecked(argument))
                    .collect::<Option<Vec<_>>>()?;
                let sort = self.ctx.terms.sort(elaborated).clone();
                Some(self.ctx.terms.mk_app(
                    Symbol::indexed(name, numeric_indices),
                    raw_arguments,
                    sort,
                ))
            }
            _ => None,
        }
    }
}
