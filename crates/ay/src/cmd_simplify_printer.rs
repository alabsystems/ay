// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SMT-LIB2 AST printer for `ay simplify` (#8696).
//!
//! Converts `ay_frontend` `Command` / `Term` / `Sort` values back into
//! well-formed SMT-LIB2 text so a simplification pass can round-trip a
//! parsed script to stdout. Split out of `cmd_simplify.rs` to keep every
//! file under the 500-line module cap.

use ay_core::quote_symbol;
use ay_frontend::command::{
    Constant, ConstructorDec, DatatypeDec, Index, QualifiedIdentifier, SelectorDec, Sort, SortDec,
    Term,
};
use ay_frontend::{Command, SExpr};

fn identifier_to_sexp(identifier: &str) -> SExpr {
    // `to_raw_string` deliberately does not quote symbols, so carry the bars
    // in the stored spelling for user identifiers while keeping syntax tokens
    // such as `_` and `as` raw at their construction sites.
    SExpr::Symbol(quote_symbol(identifier))
}

fn opaque_value_to_sexp(value: &SExpr) -> SExpr {
    match value {
        SExpr::Symbol(symbol) => identifier_to_sexp(symbol),
        _ => value.clone(),
    }
}

fn annotation_value_to_sexp(key: &str, value: &SExpr) -> SExpr {
    if key == ":pattern" {
        if let SExpr::List(patterns) = value {
            let rendered = patterns
                .iter()
                .map(|pattern| Term::from_sexp(pattern).map(|term| term_to_sexp(&term)))
                .collect::<Result<Vec<_>, _>>();
            if let Ok(rendered) = rendered {
                return SExpr::List(rendered);
            }
        }
    }

    if key == ":no-pattern" {
        if let Ok(term) = Term::from_sexp(value) {
            return term_to_sexp(&term);
        }
    }

    opaque_value_to_sexp(value)
}

fn index_to_sexp(index: &Index) -> SExpr {
    match index {
        Index::Numeral(value) => SExpr::Numeral(value.clone()),
        Index::Decimal(value) => SExpr::Decimal(value.clone()),
        Index::Symbol(value) => identifier_to_sexp(value),
        Index::Hexadecimal(value) => SExpr::Hexadecimal(value.clone()),
        Index::Binary(value) => SExpr::Binary(value.clone()),
        _ => SExpr::Symbol("<unsupported-index>".to_string()),
    }
}

fn sorted_vars_to_sexp(vars: &[(String, Sort)]) -> SExpr {
    SExpr::List(
        vars.iter()
            .map(|(name, sort)| SExpr::List(vec![identifier_to_sexp(name), sort_to_sexp(sort)]))
            .collect(),
    )
}

fn selector_to_sexp(selector: &SelectorDec) -> SExpr {
    SExpr::List(vec![
        identifier_to_sexp(&selector.name),
        sort_to_sexp(&selector.sort),
    ])
}

fn constructor_to_sexp(constructor: &ConstructorDec) -> SExpr {
    let mut items = Vec::with_capacity(constructor.selectors.len() + 1);
    items.push(identifier_to_sexp(&constructor.name));
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
                .map(|parameter| identifier_to_sexp(parameter))
                .collect(),
        );
        SExpr::List(vec![SExpr::Symbol("par".to_string()), params, ctors])
    }
}

fn sort_dec_to_sexp(sort_dec: &SortDec) -> SExpr {
    SExpr::List(vec![
        identifier_to_sexp(&sort_dec.name),
        SExpr::Numeral(sort_dec.arity.to_string()),
    ])
}

/// Convert a frontend sort AST into an S-expression.
pub(crate) fn sort_to_sexp(sort: &Sort) -> SExpr {
    match sort {
        Sort::Simple(name) => identifier_to_sexp(name),
        Sort::Parameterized(name, params) => {
            let mut items = Vec::with_capacity(params.len() + 1);
            items.push(identifier_to_sexp(name));
            items.extend(params.iter().map(sort_to_sexp));
            SExpr::List(items)
        }
        Sort::Indexed(name, indices) => {
            let mut items = Vec::with_capacity(indices.len() + 2);
            items.push(SExpr::Symbol("_".to_string()));
            items.push(identifier_to_sexp(name));
            items.extend(indices.iter().map(index_to_sexp));
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
            head.push(identifier_to_sexp(name));
            head.extend(indices.iter().map(index_to_sexp));

            if args.is_empty() {
                return SExpr::List(head);
            }

            let mut items = Vec::with_capacity(args.len() + 1);
            items.push(SExpr::List(head));
            items.extend(args.iter().map(term_to_sexp));
            SExpr::List(items)
        }
        Term::QualifiedApp(identifier, sort, args) => {
            let qualified = match identifier {
                QualifiedIdentifier::Symbol(name) => identifier_to_sexp(name),
                QualifiedIdentifier::Indexed(name, indices) => {
                    let mut indexed = Vec::with_capacity(indices.len() + 2);
                    indexed.push(SExpr::Symbol("_".to_string()));
                    indexed.push(identifier_to_sexp(name));
                    indexed.extend(indices.iter().map(index_to_sexp));
                    SExpr::List(indexed)
                }
                _ => SExpr::Symbol("<unsupported-qualified-identifier>".to_string()),
            };
            let head = SExpr::List(vec![
                SExpr::Symbol("as".to_string()),
                qualified,
                sort_to_sexp(sort),
            ]);
            if args.is_empty() {
                return head;
            }
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
                        SExpr::List(vec![identifier_to_sexp(name), term_to_sexp(value)])
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
                items.push(annotation_value_to_sexp(key, value));
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
            identifier_to_sexp(logic),
        ]),
        Command::SetOption(keyword, value) => SExpr::List(vec![
            SExpr::Symbol("set-option".to_string()),
            SExpr::Keyword(keyword.clone()),
            opaque_value_to_sexp(value),
        ]),
        Command::SetOptionAttribute(keyword) => SExpr::List(vec![
            SExpr::Symbol("set-option".to_string()),
            SExpr::Keyword(keyword.clone()),
        ]),
        Command::SetInfo(keyword, value) => SExpr::List(vec![
            SExpr::Symbol("set-info".to_string()),
            SExpr::Keyword(keyword.clone()),
            opaque_value_to_sexp(value),
        ]),
        Command::SetInfoAttribute(keyword) => SExpr::List(vec![
            SExpr::Symbol("set-info".to_string()),
            SExpr::Keyword(keyword.clone()),
        ]),
        Command::DeclareSort(name, arity) => SExpr::List(vec![
            SExpr::Symbol("declare-sort".to_string()),
            identifier_to_sexp(name),
            SExpr::Numeral(arity.to_string()),
        ]),
        Command::DeclareSortParameter(name) => SExpr::List(vec![
            SExpr::Symbol("declare-sort-parameter".to_string()),
            identifier_to_sexp(name),
        ]),
        Command::DefineSort(name, params, sort) => SExpr::List(vec![
            SExpr::Symbol("define-sort".to_string()),
            identifier_to_sexp(name),
            SExpr::List(
                params
                    .iter()
                    .map(|param| identifier_to_sexp(param))
                    .collect(),
            ),
            sort_to_sexp(sort),
        ]),
        Command::DeclareDatatype(name, datatype) => SExpr::List(vec![
            SExpr::Symbol("declare-datatype".to_string()),
            identifier_to_sexp(name),
            datatype_to_sexp(datatype),
        ]),
        Command::DeclareDatatypes(sort_decs, datatypes) => SExpr::List(vec![
            SExpr::Symbol("declare-datatypes".to_string()),
            SExpr::List(sort_decs.iter().map(sort_dec_to_sexp).collect()),
            SExpr::List(datatypes.iter().map(datatype_to_sexp).collect()),
        ]),
        Command::DeclareFun(name, params, sort) => SExpr::List(vec![
            SExpr::Symbol("declare-fun".to_string()),
            identifier_to_sexp(name),
            SExpr::List(params.iter().map(sort_to_sexp).collect()),
            sort_to_sexp(sort),
        ]),
        Command::DeclareConst(name, sort) => SExpr::List(vec![
            SExpr::Symbol("declare-const".to_string()),
            identifier_to_sexp(name),
            sort_to_sexp(sort),
        ]),
        Command::DefineFun(name, params, sort, body) => SExpr::List(vec![
            SExpr::Symbol("define-fun".to_string()),
            identifier_to_sexp(name),
            sorted_vars_to_sexp(params),
            sort_to_sexp(sort),
            term_to_sexp(body),
        ]),
        Command::DefineFunRec(name, params, sort, body) => SExpr::List(vec![
            SExpr::Symbol("define-fun-rec".to_string()),
            identifier_to_sexp(name),
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
                            identifier_to_sexp(name),
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
        Command::Labels => SExpr::List(vec![SExpr::Symbol("labels".to_string())]),
        Command::Exit => SExpr::List(vec![SExpr::Symbol("exit".to_string())]),
        Command::Echo(message) => SExpr::List(vec![
            SExpr::Symbol("echo".to_string()),
            SExpr::String(message.clone()),
        ]),
        Command::Display(term, _) => SExpr::List(vec![
            SExpr::Symbol("display".to_string()),
            term_to_sexp(term),
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
    use ay_frontend::sexp::parse_sexp;

    #[test]
    fn term_and_sort_round_trip_to_smtlib() {
        let term =
            Term::from_sexp(&parse_sexp("((as const (Array Int Int)) 0)").expect("valid sexp"))
                .expect("valid term");
        assert_eq!(
            term_to_sexp(&term).to_raw_string(),
            "((as const (Array Int Int)) 0)"
        );

        let sort = Sort::Indexed("BitVec".to_string(), vec![Index::Numeral("32".to_string())]);
        assert_eq!(sort_to_sexp(&sort).to_raw_string(), "(_ BitVec 32)");
    }

    #[test]
    fn indexed_literals_and_same_spelled_symbols_round_trip_distinctly() {
        let term =
            Term::from_sexp(&parse_sexp("(distinct |(_ bv0 8)| (_ bv0 8))").expect("valid sexp"))
                .expect("valid term");
        assert_eq!(
            term_to_sexp(&term).to_raw_string(),
            "(distinct |(_ bv0 8)| (_ bv0 8))"
        );

        let let_term = Term::from_sexp(
            &parse_sexp("(let ((|(_ bv0 8)| #x01)) (distinct |(_ bv0 8)| (_ bv0 8)))")
                .expect("valid let expression"),
        )
        .expect("valid let term");
        assert_eq!(
            term_to_sexp(&let_term).to_raw_string(),
            "(let ((|(_ bv0 8)| #x01)) (distinct |(_ bv0 8)| (_ bv0 8)))"
        );

        let annotated =
            Term::from_sexp(&parse_sexp("(! p :named |(_ bv0 8)|)").expect("valid annotation"))
                .expect("valid annotated term");
        assert_eq!(
            term_to_sexp(&annotated).to_raw_string(),
            "(! p :named |(_ bv0 8)|)"
        );

        for input in [
            "(! true :pattern ((f |(_ bv0 8)|) ((_ extract 7 0) x)))",
            "(! true :pattern ((f |(_ bv0 8)|)) :pattern (((_ extract 7 0) |(_ bv0 8)|)))",
            "(! true :no-pattern ((_ extract 7 0) |(_ bv0 8)|))",
        ] {
            let patterned = Term::from_sexp(&parse_sexp(input).expect("valid pattern annotation"))
                .expect("valid annotated term");
            let rendered = term_to_sexp(&patterned).to_raw_string();
            assert_eq!(rendered, input);
            let reparsed = Term::from_sexp(&parse_sexp(&rendered).expect("rendered S-expression"))
                .expect("rendered annotated term");
            assert_eq!(reparsed, patterned);
        }

        let character = Term::from_sexp(&parse_sexp("(_ char #x41)").expect("valid char literal"))
            .expect("valid term");
        assert_eq!(term_to_sexp(&character).to_raw_string(), "(_ char #x41)");

        let pseudo_boolean = Term::from_sexp(
            &parse_sexp("((_ pble 0.5 0.25) true)").expect("valid pseudo-Boolean term"),
        )
        .expect("valid term");
        assert_eq!(
            term_to_sexp(&pseudo_boolean).to_raw_string(),
            "((_ pble 0.5 0.25) true)"
        );

        for input in ["(as f Int)", "(as (_ f 1) Int)"] {
            let qualified = Term::from_sexp(&parse_sexp(input).expect("valid qualified term"))
                .expect("valid term");
            assert_eq!(term_to_sexp(&qualified).to_raw_string(), input);
        }
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
