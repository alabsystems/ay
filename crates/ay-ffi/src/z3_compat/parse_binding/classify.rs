// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Classifying the commands of a text for a bound parse (see the parent
//! module): what the parse runs, what the text declares, and the rewrite of
//! its recursive definitions.

use std::collections::{HashMap, HashSet};

use ay_frontend::{Command, CommandStream, CommandStreamItem};

use super::super::ObjectiveSense;
use super::{sexp_items, HELPER_PREFIX};

/// One recursive definition of the text, rewritten into a declaration and a
/// marker assertion `(marker (f a0 ...) body)` over fresh parameter constants.
pub(super) struct RecDefinition {
    pub(super) name: String,
    pub(super) arity: usize,
    /// Display names of the parameters, in order.
    pub(super) params: Vec<String>,
    /// The defining command, whitespace-normalized: the same definition in
    /// another text denotes the same function.
    pub(super) source: String,
}

/// One kept command of the text, classified.
enum Piece {
    /// Kept verbatim in the parse.
    Keep(String),
    /// A recursive definition, rewritten.
    Rec(RecDefinition),
}

/// The classified text: what the parse runs, and what it declares.
#[derive(Default)]
pub(super) struct Classified {
    /// The text the parse runs, after the prelude.
    pub(super) body: String,
    /// Surface names the text declares (constants, functions, recursive
    /// functions and their parameter helpers).
    pub(super) declared: HashSet<String>,
    /// Sort names the text declares.
    pub(super) sorts: Vec<String>,
    /// The text's datatype declarations, verbatim.
    pub(super) datatypes: Vec<String>,
    /// The sort names they declare.
    pub(super) datatype_sorts: Vec<String>,
    /// Each declared datatype, by sort name.
    pub(super) datatype_decs: Vec<(String, ay_frontend::command::DatatypeDec)>,
    /// `define-fun` / `define-sort` commands, verbatim.
    pub(super) definitions: Vec<String>,
    /// Recursive definitions in text order; their markers are the
    /// assertions at `rec_markers`.
    pub(super) recs: Vec<RecDefinition>,
    /// Index of each recursive definition's marker among the parsed
    /// assertions.
    pub(super) rec_markers: Vec<usize>,
    /// Helper name of each recursive-definition parameter -> its display name.
    pub(super) rec_params: HashMap<String, String>,
    /// Recursive definitions rewritten so far (numbers their markers).
    pub(super) recs_seen: usize,
    /// Soft constraints: weight and group, in text order.
    pub(super) softs: Vec<(u64, Option<String>)>,
    /// Objective directions, in text order.
    pub(super) objectives: Vec<ObjectiveSense>,
}

/// The commands of `input` with their source text.
pub(super) fn split_commands(input: &str) -> Result<Vec<(Command, String)>, String> {
    let mut stream = CommandStream::new(input);
    let mut pieces = Vec::new();
    loop {
        let start = stream.position();
        let Some(item) = stream.next_command() else {
            break;
        };
        let end = stream.position();
        match item {
            CommandStreamItem::Command(command) => {
                let text = input.get(start..end).unwrap_or_default().to_string();
                pieces.push((*command, text));
            }
            CommandStreamItem::Error(error) => return Err(error.to_string()),
        }
    }
    Ok(pieces)
}

/// Rewrite one `define-fun-rec` (items `name`, `params`, `range`, `body`)
/// into a declaration and its marker assertion.
fn rec_piece(
    name: &str,
    params: &str,
    range: &str,
    body: &str,
    classified: &mut Classified,
    pieces: &mut Vec<Piece>,
) -> Result<(), String> {
    let source = format!("(define-fun-rec {name} {params} {range} {body})")
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    let params = sexp_items::list_items(params)
        .ok_or_else(|| "malformed recursive-definition parameters".to_string())?;
    if params.is_empty() {
        return Err("a recursive definition of a constant".to_string());
    }
    let mut sorts = Vec::new();
    let mut names = Vec::new();
    let mut bindings = Vec::new();
    let mut helpers = Vec::new();
    for param in &params {
        let pair = sexp_items::list_items(param)
            .filter(|pair| pair.len() == 2)
            .ok_or_else(|| "malformed recursive-definition parameter".to_string())?;
        let helper = format!("{HELPER_PREFIX}rec-arg!{}", classified.rec_params.len());
        classified
            .rec_params
            .insert(helper.clone(), sexp_items::symbol_name(pair[0]));
        classified.declared.insert(helper.clone());
        helpers.push(format!("(declare-fun |{helper}| () {})", pair[1]));
        bindings.push(format!("({} |{helper}|)", pair[0]));
        names.push(pair[0].to_string());
        sorts.push(pair[1].to_string());
    }
    let surface = sexp_items::symbol_name(name);
    classified.declared.insert(surface.clone());
    let mut text = format!("(declare-fun {name} ({}) {range})", sorts.join(" "));
    for helper in helpers {
        text.push_str(&helper);
    }
    // The marker applies a predicate of the parse's own to the application
    // and the body: an equation could be rewritten at construction (an `ite`
    // body lifted over it), an uninterpreted application is not.
    let marker = format!("{HELPER_PREFIX}rec!{}", classified.recs_seen);
    classified.recs_seen += 1;
    text.push_str(&format!("(declare-fun |{marker}| ({range} {range}) Bool)"));
    text.push_str(&format!(
        "(assert (let ({}) (|{marker}| ({name} {}) {body})))",
        bindings.join(" "),
        names.join(" ")
    ));
    pieces.push(Piece::Keep(text));
    pieces.push(Piece::Rec(RecDefinition {
        name: surface,
        arity: params.len(),
        params: names.iter().map(|n| sexp_items::symbol_name(n)).collect(),
        source,
    }));
    Ok(())
}

/// Classify the commands of a text; `Err` names the first command outside
/// the rebinding fragment.
pub(super) fn classify(
    pieces_in: Vec<(Command, String)>,
    objectives: bool,
) -> Result<Classified, String> {
    let mut classified = Classified::default();
    let mut pieces: Vec<Piece> = Vec::new();
    for (command, text) in pieces_in {
        match &command {
            Command::DeclareFun(name, _, _) | Command::DeclareConst(name, _) => {
                classified.declared.insert(name.clone());
                pieces.push(Piece::Keep(text));
            }
            Command::DeclareSort(name, 0) => classified.sorts.push(name.clone()),
            // A datatype the text declares is the context's datatype of that
            // name from then on (z3 identifies sorts by name): it is declared
            // globally before the scoped parse.
            Command::DeclareDatatype(name, datatype) => {
                classified.datatype_sorts.push(name.clone());
                classified
                    .datatype_decs
                    .push((name.clone(), datatype.clone()));
                classified.datatypes.push(text);
            }
            Command::DeclareDatatypes(sorts, datatypes) => {
                classified
                    .datatype_sorts
                    .extend(sorts.iter().map(|sort| sort.name.clone()));
                classified.datatype_decs.extend(
                    sorts
                        .iter()
                        .map(|sort| sort.name.clone())
                        .zip(datatypes.iter().cloned()),
                );
                classified.datatypes.push(text);
            }
            Command::DefineFun(..) | Command::DefineSort(..) => {
                classified.definitions.push(text.clone());
                pieces.push(Piece::Keep(text));
            }
            Command::DefineFunRec(..) => {
                let items = sexp_items::list_items(&text)
                    .filter(|items| items.len() == 5)
                    .ok_or_else(|| "malformed define-fun-rec".to_string())?;
                rec_piece(
                    items[1],
                    items[2],
                    items[3],
                    items[4],
                    &mut classified,
                    &mut pieces,
                )?;
            }
            Command::DefineFunsRec(..) => funs_rec_pieces(&text, &mut classified, &mut pieces)?,
            Command::Assert(_) => pieces.push(Piece::Keep(text)),
            Command::AssertSoft { weight, id, .. } if objectives => {
                classified.softs.push((*weight, id.clone()));
                pieces.push(Piece::Keep(text));
            }
            Command::Maximize(_) if objectives => {
                classified.objectives.push(ObjectiveSense::Maximize);
                pieces.push(Piece::Keep(text));
            }
            Command::Minimize(_) if objectives => {
                classified.objectives.push(ObjectiveSense::Minimize);
                pieces.push(Piece::Keep(text));
            }
            // An Optimize text's options configure the optimization (z3
            // applies `(set-option :opt.priority box)` to it).
            Command::SetOption(..) if objectives => pieces.push(Piece::Keep(text)),
            // z3 applies these to the text's own command context; none of
            // them changes the formulas the text contributes.
            Command::SetLogic(_)
            | Command::SetOption(..)
            | Command::SetOptionAttribute(_)
            | Command::SetInfo(..)
            | Command::SetInfoAttribute(_)
            | Command::CheckSat
            | Command::CheckSatAssuming(_)
            | Command::GetModel
            | Command::GetValue(_)
            | Command::Eval(_)
            | Command::GetUnsatCore
            | Command::GetUnsatAssumptions
            | Command::GetProof
            | Command::GetAssertions
            | Command::GetAssignment
            | Command::GetInfo(_)
            | Command::GetOption(_)
            | Command::GetObjectives
            | Command::Echo(_)
            | Command::Exit => {}
            other => return Err(format!("{other:?}").chars().take(60).collect()),
        }
    }
    number_markers(pieces, &mut classified);
    Ok(classified)
}

/// The pieces of one `define-funs-rec`: every function is declared before
/// any body mentions it, so mutual recursion parses.
fn funs_rec_pieces(
    text: &str,
    classified: &mut Classified,
    pieces: &mut Vec<Piece>,
) -> Result<(), String> {
    let items = sexp_items::list_items(text)
        .filter(|items| items.len() == 3)
        .ok_or_else(|| "malformed define-funs-rec".to_string())?;
    let declarations =
        sexp_items::list_items(items[1]).ok_or_else(|| "malformed define-funs-rec".to_string())?;
    let bodies = sexp_items::list_items(items[2])
        .filter(|bodies| bodies.len() == declarations.len())
        .ok_or_else(|| "malformed define-funs-rec".to_string())?;
    // Every function is declared before any body mentions it.
    let mut parts = Vec::new();
    for declaration in &declarations {
        let parts_of = sexp_items::list_items(declaration)
            .filter(|parts| parts.len() == 3)
            .ok_or_else(|| "malformed define-funs-rec".to_string())?;
        parts.push(parts_of);
    }
    for (parts_of, body) in parts.iter().zip(&bodies) {
        rec_piece(
            parts_of[0],
            parts_of[1],
            parts_of[2],
            body,
            classified,
            pieces,
        )?;
    }
    // `rec_piece` declares each function right before its
    // marker; hoist the declarations so mutual recursion parses.
    let mut hoisted = Vec::new();
    let mut rest = Vec::new();
    let start = pieces.len() - 2 * parts.len();
    for piece in pieces.drain(start..) {
        match piece {
            Piece::Keep(text) => {
                let (declaration, marker) = text
                    .split_once("(assert ")
                    .map(|(d, m)| (d.to_string(), format!("(assert {m}")))
                    .unwrap_or((text, String::new()));
                hoisted.push(Piece::Keep(declaration));
                rest.push(Piece::Keep(marker));
            }
            rec @ Piece::Rec(_) => rest.push(rec),
        }
    }
    pieces.extend(hoisted);
    pieces.extend(rest);
    Ok(())
}

/// Join the kept pieces into the parsed body, numbering the markers: each
/// recursive definition's marker assertion is the `assert` right before its
/// `Rec` piece.
fn number_markers(pieces: Vec<Piece>, classified: &mut Classified) {
    let mut assertion_index = 0usize;
    for piece in pieces {
        match piece {
            Piece::Keep(text) => {
                assertion_index += sexp_items::count_asserts(&text);
                classified.body.push_str(&text);
                classified.body.push('\n');
            }
            Piece::Rec(rec) => {
                classified.rec_markers.push(assertion_index - 1);
                classified.recs.push(rec);
            }
        }
    }
}
