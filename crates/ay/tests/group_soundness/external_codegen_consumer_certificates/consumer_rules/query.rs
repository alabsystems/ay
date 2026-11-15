// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The problem script as the one query a certificate refutes, read by AY's
//! own SMT-LIB front end: `ay_frontend::parse` lexes it (string literals,
//! quoted symbols and comments exactly) and `ay_frontend::Context`, the
//! elaborator AY solves with, applies every command before the query. The
//! live signature and the live assertion stack are the elaborator's at that
//! point: `push`/`pop` scope declarations and assertions alike, `reset`
//! and `reset-assertions` clear them, and a script the elaborator refuses
//! is not read as a query at all.
//!
//! REGRESSION (measured 2026-10-07 on a4b66eeff): a hand-rolled reader took
//! the problem apart. A string literal `"a) (assert false) (b"` injected an
//! assertion, the quoted symbol `|#b1|` was read as the literal `#b1`, a
//! declaration popped with its scope kept its sort for a later `x`, and a
//! user function named `bvf` was given its argument's width; each made a
//! refutation of a satisfiable problem count as checked.
//!
//! REGRESSION (measured 2026-10-07 on 7ae4f642c): AY's front end, like z3,
//! accepts a declaration of a Core connective's name at a new signature
//! (`(declare-fun ite (Bool Int) Int)`, `(declare-fun = (Int) Bool)`, …), and
//! the mirror's rules, which dispatch on a head's name, read the user's
//! function as the connective. A problem that declares any name the front
//! end's operator tables hold ([`ay_frontend::is_builtin_operator_name`]) is
//! therefore not read as a query; and, independently of that list, the
//! document never reports a problem symbol as an application's operator (see
//! `Document::head`).

use std::collections::{HashMap, HashSet};

use ay_frontend::{
    Command as Script, Constant, Context, Index, MatchPattern, QualifiedIdentifier, Sort, Term,
};

use super::reader::{from_frontend, symbol, unread, Sexp};

/// A live symbol's elaborated signature.
#[derive(Clone, Debug)]
pub(super) struct Signature {
    pub(super) arity: usize,
    /// The result sort.
    pub(super) sort: ay_core::Sort,
}

/// The problem script read as one SMT-LIB query.
#[derive(Default)]
pub(super) struct Query {
    /// Every live symbol by its spelling, unless it is overloaded.
    pub(super) signatures: HashMap<String, Signature>,
    /// Every live symbol's spelling, overloaded or not.
    pub(super) symbols: HashSet<String>,
    pub(super) assertions: Vec<Sexp>,
    pub(super) defects: Vec<String>,
}

/// Names the consumer's reader takes for its own syntax however they are
/// quoted (the front end's s-expressions drop a symbol's bars).
const SYNTAX: &[&str] = &[
    "!", "_", "as", "let", "forall", "exists", "match", "par", "lambda", "choice", "cl",
];

/// The assertions live at the problem's query: its first `check-sat`,
/// `check-sat-assuming` (its assumptions added) or `exit`, or the end of the
/// script, after the elaborator has applied every command before it.
pub(super) fn live_query(problem: &str) -> Query {
    let mut query = Query::default();
    let commands = match ay_frontend::parse(problem) {
        Ok(commands) => commands,
        Err(error) => {
            query
                .defects
                .push(format!("AY's SMT-LIB front end does not parse it: {error}"));
            return query;
        }
    };
    let mut context = Context::new();
    context.set_retain_parsed_assertions(true);
    let mut assumed: &[Term] = &[];
    for (index, command) in commands.iter().enumerate() {
        match command {
            Script::CheckSat | Script::Exit => break,
            Script::CheckSatAssuming(terms) => {
                assumed = terms;
                break;
            }
            _ => {}
        }
        if let Err(error) = context.process_command(command) {
            query.defects.push(format!(
                "AY's elaborator refuses command {index} of the problem: {error}"
            ));
            return query;
        }
    }
    let parsed = context.assertions_parsed();
    let aligned = context
        .concrete_authored_assertion_terms_aligned_bounded(usize::MAX)
        .is_some_and(|terms| terms.len() == parsed.len())
        && context.authored_assertions_for_display().len() == parsed.len();
    if !aligned {
        query.defects.push(
            "the elaborator's live assertions are not each one authored source term".to_string(),
        );
        return query;
    }
    query.assertions = parsed.iter().chain(assumed).map(term).collect();
    for (name, info) in context.symbols_iter() {
        if context.is_internal_symbol(name) {
            continue;
        }
        let spelled = symbol(name);
        if name.starts_with('@') || SYNTAX.contains(&name.as_str()) {
            query.defects.push(format!(
                "the problem declares {spelled}, a name the consumer's reader takes for syntax"
            ));
        }
        if ay_frontend::is_builtin_operator_name(name) && !query.symbols.contains(&spelled) {
            query.defects.push(format!(
                "the problem declares {spelled}, a name a theory operator is spelled with: \
                 the consumer's rules read an application of it as that operator"
            ));
        }
        let signature = Signature {
            arity: info.arg_sorts.len(),
            sort: info.sort.clone(),
        };
        if query.symbols.insert(spelled.clone()) {
            query.signatures.insert(spelled, signature);
        } else {
            // Overloaded: no one signature answers for the name.
            query.signatures.remove(&spelled);
        }
    }
    query
}

/// A parsed term as the s-expression it was written as.
fn term(term: &Term) -> Sexp {
    let atom = |text: &str| Sexp::Atom(text.to_string());
    let list = |head: Sexp, args: &[Term]| {
        if args.is_empty() {
            head
        } else {
            let mut items = vec![head];
            items.extend(args.iter().map(self::term));
            Sexp::List(items)
        }
    };
    let binders = |kind: &str, bound: &[(String, Sort)], body: &Term| {
        let bound = bound
            .iter()
            .map(|(name, sort)| Sexp::List(vec![Sexp::Atom(symbol(name)), self::sort(sort)]))
            .collect();
        Sexp::List(vec![atom(kind), Sexp::List(bound), self::term(body)])
    };
    match term {
        Term::Const(constant) => Sexp::Atom(match constant {
            Constant::True => "true".to_string(),
            Constant::False => "false".to_string(),
            Constant::Numeral(text)
            | Constant::Decimal(text)
            | Constant::Hexadecimal(text)
            | Constant::Binary(text) => text.clone(),
            Constant::String(contents) => ay_core::string_literal(contents),
            other => unread(other),
        }),
        Term::Symbol(name) => Sexp::Atom(symbol(name)),
        Term::App(head, args) => {
            let mut items = vec![Sexp::Atom(symbol(head))];
            items.extend(args.iter().map(self::term));
            Sexp::List(items)
        }
        Term::IndexedApp(name, indices, args) => list(indexed(name, indices), args),
        Term::QualifiedApp(identifier, sort, args) => {
            let identifier = match identifier {
                QualifiedIdentifier::Symbol(name) => Sexp::Atom(symbol(name)),
                QualifiedIdentifier::Indexed(name, indices) => indexed(name, indices),
                other => Sexp::Atom(unread(other)),
            };
            list(
                Sexp::List(vec![atom("as"), identifier, self::sort(sort)]),
                args,
            )
        }
        Term::Let(bindings, body) => {
            let bindings = bindings
                .iter()
                .map(|(name, value)| Sexp::List(vec![Sexp::Atom(symbol(name)), self::term(value)]))
                .collect();
            Sexp::List(vec![atom("let"), Sexp::List(bindings), self::term(body)])
        }
        Term::Forall(bound, body) => binders("forall", bound, body),
        Term::Exists(bound, body) => binders("exists", bound, body),
        Term::Lambda(bound, body) => binders("lambda", bound, body),
        Term::Annotated(inner, attributes) => {
            let mut items = vec![atom("!"), self::term(inner)];
            for (key, value) in attributes {
                items.push(Sexp::Atom(key.clone()));
                items.push(from_frontend(value));
            }
            Sexp::List(items)
        }
        Term::Match(scrutinee, cases) => {
            let cases = cases
                .iter()
                .map(|(pattern, body)| {
                    let pattern = match pattern {
                        MatchPattern::Symbol(name) => Sexp::Atom(symbol(name)),
                        MatchPattern::Constructor(name, fields) => Sexp::List(
                            std::iter::once(name)
                                .chain(fields)
                                .map(|name| Sexp::Atom(symbol(name)))
                                .collect(),
                        ),
                        other => Sexp::Atom(unread(other)),
                    };
                    Sexp::List(vec![pattern, self::term(body)])
                })
                .collect();
            Sexp::List(vec![
                atom("match"),
                self::term(scrutinee),
                Sexp::List(cases),
            ])
        }
        other => Sexp::Atom(unread(other)),
    }
}

/// `(_ name indices…)`.
fn indexed(name: &str, indices: &[Index]) -> Sexp {
    let mut items = vec![Sexp::Atom("_".to_string()), Sexp::Atom(symbol(name))];
    items.extend(indices.iter().map(index));
    Sexp::List(items)
}

fn index(index: &Index) -> Sexp {
    Sexp::Atom(match index {
        Index::Symbol(name) => symbol(name),
        Index::Numeral(text)
        | Index::Decimal(text)
        | Index::Hexadecimal(text)
        | Index::Binary(text) => text.clone(),
        other => unread(other),
    })
}

fn sort(sort: &Sort) -> Sexp {
    match sort {
        Sort::Simple(name) => Sexp::Atom(symbol(name)),
        Sort::Parameterized(name, args) => Sexp::List(
            std::iter::once(Sexp::Atom(symbol(name)))
                .chain(args.iter().map(self::sort))
                .collect(),
        ),
        Sort::Indexed(name, indices) => indexed(name, indices),
        other => Sexp::Atom(unread(other)),
    }
}

/// Every atom of `term`.
pub(super) fn atoms(term: &Sexp, into: &mut HashSet<String>) {
    match term {
        Sexp::Atom(atom) => {
            into.insert(atom.clone());
        }
        Sexp::List(items) => items.iter().for_each(|item| atoms(item, into)),
    }
}
