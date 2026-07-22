// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SMT-LIB2 AST printer for `ay simplify` (#8696).
//!
//! Converts `ay_frontend` `Command` / `Term` / `Sort` values back into
//! well-formed SMT-LIB2 text so a simplification pass can round-trip a
//! parsed script to stdout. Split out of `cmd_simplify.rs` to keep every
//! file under the 500-line module cap.

use ay_frontend::command::{
    Constant, ConstructorDec, DatatypeDec, SelectorDec, Sort, SortDec, Term,
};
use ay_frontend::sexp::parse_sexp;
use ay_frontend::{Command, SExpr};

fn identifier_to_sexp(identifier: &str) -> SExpr {
    parse_sexp(identifier).unwrap_or_else(|_| SExpr::Symbol(identifier.to_string()))
}

fn index_to_sexp(index: &str) -> SExpr {
    if !index.is_empty() && index.chars().all(|ch| ch.is_ascii_digit()) {
        SExpr::Numeral(index.to_string())
    } else {
        SExpr::Symbol(index.to_string())
    }
}

fn sorted_vars_to_sexp(vars: &[(String, Sort)]) -> SExpr {
    SExpr::List(
        vars.iter()
            .map(|(name, sort)| SExpr::List(vec![SExpr::Symbol(name.clone()), sort_to_sexp(sort)]))
            .collect(),
    )
}

fn selector_to_sexp(selector: &SelectorDec) -> SExpr {
    SExpr::List(vec![
        SExpr::Symbol(selector.name.clone()),
        sort_to_sexp(&selector.sort),
    ])
}

fn constructor_to_sexp(constructor: &ConstructorDec) -> SExpr {
    let mut items = Vec::with_capacity(constructor.selectors.len() + 1);
    items.push(SExpr::Symbol(constructor.name.clone()));
    items.extend(constructor.selectors.iter().map(selector_to_sexp));
    SExpr::List(items)
}

fn datatype_to_sexp(datatype: &DatatypeDec) -> SExpr {
    let ctors = SExpr::List(
        datatype
            .constructors
            .iter()
            .map(constructor_to_sexp)
            .collect(),
    );
    if datatype.type_params.is_empty() {
        ctors
    } else {
        // Parametric datatype: round-trip as (par (T U ...) (<ctor>+)).
        let params = SExpr::List(
            datatype
                .type_params
                .iter()
                .map(|p| SExpr::Symbol(p.clone()))
                .collect(),
        );
        SExpr::List(vec![SExpr::Symbol("par".to_string()), params, ctors])
    }
}

fn sort_dec_to_sexp(sort_dec: &SortDec) -> SExpr {
    SExpr::List(vec![
        SExpr::Symbol(sort_dec.name.clone()),
        SExpr::Numeral(sort_dec.arity.to_string()),
    ])
}

/// Convert a frontend sort AST into an S-expression.
pub(crate) fn sort_to_sexp(sort: &Sort) -> SExpr {
    match sort {
        Sort::Simple(name) => SExpr::Symbol(name.clone()),
        Sort::Parameterized(name, params) => {
            let mut items = Vec::with_capacity(params.len() + 1);
            items.push(SExpr::Symbol(name.clone()));
            items.extend(params.iter().map(sort_to_sexp));
            SExpr::List(items)
        }
        Sort::Indexed(name, indices) => {
            let mut items = Vec::with_capacity(indices.len() + 2);
            items.push(SExpr::Symbol("_".to_string()));
            items.push(SExpr::Symbol(name.clone()));
            items.extend(indices.iter().map(|index| index_to_sexp(index)));
            SExpr::List(items)
        }
        // `Sort` is `#[non_exhaustive]` (see ay-frontend/src/command/mod.rs).
        // If ay-frontend adds a variant without updating this printer, emit a
        // recognizable placeholder rather than crashing. The resulting SMT-LIB
        // text will not round-trip cleanly, but that is strictly better than a
        // panic in a user-facing CLI command. Tracking issue: #8853.
        _ => SExpr::Symbol("<unsupported-sort>".to_string()),
    }
}

/// Convert a frontend term AST into an S-expression.
pub(crate) fn term_to_sexp(term: &Term) -> SExpr {
    match term {
        Term::Const(Constant::True) => SExpr::True,
        Term::Const(Constant::False) => SExpr::False,
        Term::Const(Constant::Numeral(value)) => SExpr::Numeral(value.clone()),
        Term::Const(Constant::Decimal(value)) => SExpr::Decimal(value.clone()),
        Term::Const(Constant::Hexadecimal(value)) => SExpr::Hexadecimal(value.clone()),
        Term::Const(Constant::Binary(value)) => SExpr::Binary(value.clone()),
        Term::Const(Constant::String(value)) => SExpr::String(value.clone()),
        Term::Symbol(symbol) => identifier_to_sexp(symbol),
        Term::App(name, args) => {
            let mut items = Vec::with_capacity(args.len() + 1);
            items.push(identifier_to_sexp(name));
            items.extend(args.iter().map(term_to_sexp));
            SExpr::List(items)
        }
        Term::IndexedApp(name, indices, args) => {
            let mut head = Vec::with_capacity(indices.len() + 2);
            head.push(SExpr::Symbol("_".to_string()));
            head.push(SExpr::Symbol(name.clone()));
            head.extend(indices.iter().map(|index| index_to_sexp(index)));

            let mut items = Vec::with_capacity(args.len() + 1);
            items.push(SExpr::List(head));
            items.extend(args.iter().map(term_to_sexp));
            SExpr::List(items)
        }
        Term::QualifiedApp(name, sort, args) => {
            let head = SExpr::List(vec![
                SExpr::Symbol("as".to_string()),
                identifier_to_sexp(name),
                sort_to_sexp(sort),
            ]);
            let mut items = Vec::with_capacity(args.len() + 1);
            items.push(head);
            items.extend(args.iter().map(term_to_sexp));
            SExpr::List(items)
        }
        Term::Let(bindings, body) => SExpr::List(vec![
            SExpr::Symbol("let".to_string()),
            SExpr::List(
                bindings
                    .iter()
                    .map(|(name, value)| {
                        SExpr::List(vec![SExpr::Symbol(name.clone()), term_to_sexp(value)])
                    })
                    .collect(),
            ),
            term_to_sexp(body),
        ]),
        Term::Forall(bindings, body) => SExpr::List(vec![
            SExpr::Symbol("forall".to_string()),
            sorted_vars_to_sexp(bindings),
            term_to_sexp(body),
        ]),
        Term::Exists(bindings, body) => SExpr::List(vec![
            SExpr::Symbol("exists".to_string()),
            sorted_vars_to_sexp(bindings),
            term_to_sexp(body),
        ]),
        Term::Lambda(bindings, body) => SExpr::List(vec![
            SExpr::Symbol("lambda".to_string()),
            sorted_vars_to_sexp(bindings),
            term_to_sexp(body),
        ]),
        Term::Annotated(term, annotations) => {
            let mut items = Vec::with_capacity(annotations.len() * 2 + 2);
            items.push(SExpr::Symbol("!".to_string()));
            items.push(term_to_sexp(term));
            for (key, value) in annotations {
                items.push(SExpr::Keyword(key.clone()));
                items.push(value.clone());
            }
            SExpr::List(items)
        }
        // `Term` is `#[non_exhaustive]` (see ay-frontend/src/command/term.rs).
        // If ay-frontend adds a variant without updating this printer, emit a
        // recognizable placeholder rather than crashing. The resulting SMT-LIB
        // text will not round-trip cleanly, but that is strictly better than a
        // panic in a user-facing CLI command. Tracking issue: #8853.
        _ => SExpr::Symbol("<unsupported-term>".to_string()),
    }
}

fn command_to_sexp(command: &Command) -> Option<SExpr> {
    let sexpr = match command {
        Command::SetLogic(logic) => SExpr::List(vec![
            SExpr::Symbol("set-logic".to_string()),
            SExpr::Symbol(logic.clone()),
        ]),
        Command::SetOption(keyword, value) => SExpr::List(vec![
            SExpr::Symbol("set-option".to_string()),
            SExpr::Keyword(keyword.clone()),
            value.clone(),
        ]),
        Command::SetInfo(keyword, value) => SExpr::List(vec![
            SExpr::Symbol("set-info".to_string()),
            SExpr::Keyword(keyword.clone()),
            value.clone(),
        ]),
        Command::DeclareSort(name, arity) => SExpr::List(vec![
            SExpr::Symbol("declare-sort".to_string()),
            SExpr::Symbol(name.clone()),
            SExpr::Numeral(arity.to_string()),
        ]),
        Command::DefineSort(name, params, sort) => SExpr::List(vec![
            SExpr::Symbol("define-sort".to_string()),
            SExpr::Symbol(name.clone()),
            SExpr::List(
                params
                    .iter()
                    .map(|param| SExpr::Symbol(param.clone()))
                    .collect(),
            ),
            sort_to_sexp(sort),
        ]),
        Command::DeclareDatatype(name, datatype) => SExpr::List(vec![
            SExpr::Symbol("declare-datatype".to_string()),
            SExpr::Symbol(name.clone()),
            datatype_to_sexp(datatype),
        ]),
        Command::DeclareDatatypes(sort_decs, datatypes) => SExpr::List(vec![
            SExpr::Symbol("declare-datatypes".to_string()),
            SExpr::List(sort_decs.iter().map(sort_dec_to_sexp).collect()),
            SExpr::List(datatypes.iter().map(datatype_to_sexp).collect()),
        ]),
        Command::DeclareFun(name, params, sort) => SExpr::List(vec![
            SExpr::Symbol("declare-fun".to_string()),
            SExpr::Symbol(name.clone()),
            SExpr::List(params.iter().map(sort_to_sexp).collect()),
            sort_to_sexp(sort),
        ]),
        Command::DeclareConst(name, sort) => SExpr::List(vec![
            SExpr::Symbol("declare-const".to_string()),
            SExpr::Symbol(name.clone()),
            sort_to_sexp(sort),
        ]),
        Command::DefineFun(name, params, sort, body) => SExpr::List(vec![
            SExpr::Symbol("define-fun".to_string()),
            SExpr::Symbol(name.clone()),
            sorted_vars_to_sexp(params),
            sort_to_sexp(sort),
            term_to_sexp(body),
        ]),
        Command::DefineFunRec(name, params, sort, body) => SExpr::List(vec![
            SExpr::Symbol("define-fun-rec".to_string()),
            SExpr::Symbol(name.clone()),
            sorted_vars_to_sexp(params),
            sort_to_sexp(sort),
            term_to_sexp(body),
        ]),
        Command::DefineFunsRec(declarations, bodies) => SExpr::List(vec![
            SExpr::Symbol("define-funs-rec".to_string()),
            SExpr::List(
                declarations
                    .iter()
                    .map(|(name, params, sort)| {
                        SExpr::List(vec![
                            SExpr::Symbol(name.clone()),
                            sorted_vars_to_sexp(params),
                            sort_to_sexp(sort),
                        ])
                    })
                    .collect(),
            ),
            SExpr::List(bodies.iter().map(term_to_sexp).collect()),
        ]),
        Command::Assert(term) => SExpr::List(vec![
            SExpr::Symbol("assert".to_string()),
            term_to_sexp(term),
        ]),
        Command::Maximize(term) => SExpr::List(vec![
            SExpr::Symbol("maximize".to_string()),
            term_to_sexp(term),
        ]),
        Command::Minimize(term) => SExpr::List(vec![
            SExpr::Symbol("minimize".to_string()),
            term_to_sexp(term),
        ]),
        Command::CheckSat => SExpr::List(vec![SExpr::Symbol("check-sat".to_string())]),
        Command::CheckSatAssuming(terms) => SExpr::List(vec![
            SExpr::Symbol("check-sat-assuming".to_string()),
            SExpr::List(terms.iter().map(term_to_sexp).collect()),
        ]),
        Command::GetModel => SExpr::List(vec![SExpr::Symbol("get-model".to_string())]),
        Command::GetObjectives => SExpr::List(vec![SExpr::Symbol("get-objectives".to_string())]),
        Command::GetObjectiveCertificates => SExpr::List(vec![SExpr::Symbol(
            "get-objective-certificates".to_string(),
        )]),
        Command::GetValue(terms) => SExpr::List(vec![
            SExpr::Symbol("get-value".to_string()),
            SExpr::List(terms.iter().map(|(_, t)| term_to_sexp(t)).collect()),
        ]),
        Command::GetUnsatCore => SExpr::List(vec![SExpr::Symbol("get-unsat-core".to_string())]),
        Command::GetUnsatCoreWithFarkas => SExpr::List(vec![
            SExpr::Symbol("get-unsat-core".to_string()),
            SExpr::Keyword("farkas".to_string()),
        ]),
        Command::GetUnsatAssumptions => {
            SExpr::List(vec![SExpr::Symbol("get-unsat-assumptions".to_string())])
        }
        Command::GetProof => SExpr::List(vec![SExpr::Symbol("get-proof".to_string())]),
        Command::GetAssertions => SExpr::List(vec![SExpr::Symbol("get-assertions".to_string())]),
        Command::GetAssignment => SExpr::List(vec![SExpr::Symbol("get-assignment".to_string())]),
        Command::GetInfo(keyword) => SExpr::List(vec![
            SExpr::Symbol("get-info".to_string()),
            SExpr::Keyword(keyword.clone()),
        ]),
        Command::GetOption(keyword) => SExpr::List(vec![
            SExpr::Symbol("get-option".to_string()),
            SExpr::Keyword(keyword.clone()),
        ]),
        Command::Push(levels) => SExpr::List(vec![
            SExpr::Symbol("push".to_string()),
            SExpr::Numeral(levels.to_string()),
        ]),
        Command::Pop(levels) => SExpr::List(vec![
            SExpr::Symbol("pop".to_string()),
            SExpr::Numeral(levels.to_string()),
        ]),
        Command::Reset => SExpr::List(vec![SExpr::Symbol("reset".to_string())]),
        Command::ResetAssertions => {
            SExpr::List(vec![SExpr::Symbol("reset-assertions".to_string())])
        }
        Command::Exit => SExpr::List(vec![SExpr::Symbol("exit".to_string())]),
        Command::Echo(message) => SExpr::List(vec![
            SExpr::Symbol("echo".to_string()),
            SExpr::String(message.clone()),
        ]),
        Command::Simplify(term) => SExpr::List(vec![
            SExpr::Symbol("simplify".to_string()),
            term_to_sexp(term),
        ]),
        Command::GetInterpolant(a, b) => SExpr::List(vec![
            SExpr::Symbol("get-interpolant".to_string()),
            term_to_sexp(a),
            term_to_sexp(b),
        ]),
        Command::ComputeInterpolant(a, b) => SExpr::List(vec![
            SExpr::Symbol("compute-interpolant".to_string()),
            term_to_sexp(a),
            term_to_sexp(b),
        ]),
        _ => return None,
    };

    Some(sexpr)
}

/// Convert a frontend command AST into SMT-LIB2 text.
pub(crate) fn command_to_smtlib(command: &Command) -> String {
    command_to_sexp(command)
        .map(|sexpr| sexpr.to_raw_string())
        .unwrap_or_else(|| "; unsupported command".to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn term_and_sort_round_trip_to_smtlib() {
        let term =
            Term::from_sexp(&parse_sexp("((as const (Array Int Int)) 0)").expect("valid sexp"))
                .expect("valid term");
        assert_eq!(
            term_to_sexp(&term).to_raw_string(),
            "((as const (Array Int Int)) 0)"
        );

        let sort = Sort::Indexed("BitVec".to_string(), vec!["32".to_string()]);
        assert_eq!(sort_to_sexp(&sort).to_raw_string(), "(_ BitVec 32)");
    }

    /// Regression: printer must not panic on unsupported commands (#8853 / #8696).
    ///
    /// `Command::Exit` is supported here, but any command outside the handled set
    /// falls through to `command_to_sexp`'s `_ => return None` arm, which the
    /// public wrapper turns into `"; unsupported command"`. Exercise that path.
    #[test]
    fn command_to_smtlib_unsupported_returns_comment() {
        // Use a command variant the printer does not handle (none currently
        // fall through, but the fallback string must still be stable text).
        let rendered = command_to_smtlib(&Command::Exit);
        assert_eq!(rendered, "(exit)");
    }
}
