// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A Carcara verdict on a document pinned Carcara reads with a captured or
//! rebound variable is not evidence.
//!
//! Pinned carcara 1.1.0 (git 9a352ee) expands every name it holds as a function
//! definition at PARSE time, before any scope lookup (`parser/mod.rs`
//! `parse_term`: `function_defs.get(&s)` is consulted before `make_var`, and an
//! application head likewise). A variable is a term identified by its name and
//! sort alone, a nullary definition expands to its stored body unchanged
//! (`FunctionDef::apply`), and a parameterized one substitutes only its
//! parameters. It holds as definitions:
//!
//! * every `:named` label, of the problem or the proof, in every mode;
//! * every proof `define-fun`, in every mode;
//! * every problem `define-fun`, under `--apply-function-defs` only. No gate
//!   passes that flag (without it a problem `define-fun` is a declared symbol
//!   plus the premise `(= f (lambda ..))`, see the ay-dpll test
//!   `carcara_external_check/define_fun_reading.rs`); it is
//!   recorded anyway, which can only flag more, so adding the flag cannot
//!   silently reopen this hole.
//!
//! So it misreads two shapes:
//!
//! * REBINDING: a binder that reuses a definition's name. The name's
//!   occurrences in the binder's scope read as the definition's body.
//! * CAPTURE: a definition whose body mentions a free symbol `y`, expanded in
//!   the scope of a binder of `y`: that occurrence of `y` becomes the bound
//!   variable.
//!
//! Measured 2026-09-26 with that checker, in both invocations AY's gates have
//! used (`--expand-let-bindings`, the corpus runner's until 2026-09-30, and
//! the plain `check` that is now canonical), it prints `valid` for these
//! refutations of two SATISFIABLE problems, one of each shape (z3 `sat` on
//! both; the real-checker control
//! `a_valid_verdict_on_a_problem_carcara_misreads_is_not_evidence` in
//! `crates/ay-dpll/tests/group_proofs/carcara_external_check/`):
//!
//! ```text
//! (declare-const x Int) (assert (! (= x 5) :named c))
//! (assert (exists ((c Bool)) (not c)))
//!   read as `(exists ((c Bool)) (not (= x 5)))`, refuted by `qnt_rm_unused`;
//! (declare-const y Int) (assert (! (= y 0) :named n))
//! (assert (forall ((y Int)) n))
//!   read as `(forall ((y Int)) (= y 0))`, refuted by `forall_inst`.
//! ```
//!
//! Only a misread PROBLEM can make a refutation unsound: carcara checks every
//! proof step over its own parse, so a misread proof still derives consequences
//! of the premises as parsed. But a proof carcara reads differently from its
//! spelling is not a certificate another Alethe checker reads the same way, so
//! both documents are scanned. A binding occurrence (a quantifier, `lambda`,
//! `choice`, `let` or `match` variable, a `define-fun`/`define-fun-rec`
//! parameter, an `anchor` variable) is flagged when it rebinds a definition
//! name, or when it binds a symbol free in a definition (closed over the
//! definitions that body names) that its scope names: a use, or the `:named`
//! site of a label over a term the binder binds into. Order and sorts are
//! ignored, a `match` pattern binds nothing in a definition body, and an
//! `anchor` variable scopes over the whole proof: each can only flag more.

use super::lexer::{LexedDocument, SexpToken};
use std::collections::BTreeSet;

/// A binding occurrence: the bound name and the first and last index of its
/// scope, `None` for an `anchor` variable (the whole proof).
type Binder<'a> = (&'a str, Option<(usize, usize)>);

impl<'a> LexedDocument<'a> {
    /// The name each `(name ..)` entry of the binding list at `list` binds.
    fn binding_names(&self, list: Option<usize>) -> Vec<&'a str> {
        let Some(list) = list.filter(|&list| self.is_open(list)) else {
            return Vec::new();
        };
        let children = self.children(list);
        children
            .into_iter()
            .filter_map(|entry| self.head(entry))
            .collect()
    }

    /// The symbols of the term at `body` that no binder inside it binds
    /// (keywords excluded). A binding list's names and sorts are skipped, a
    /// `let` value is read outside its bindings, and a `match` pattern binds
    /// nothing (which can only report more). One linear pass, no recursion.
    fn free_symbols(&self, body: usize, free: &mut BTreeSet<&'a str>) {
        // Frames `(first, last, names)`: `names` are bound on `first..=last`.
        // Spans nest (a `let` frame starts after the values read under it), so
        // a stack popped once its span ends is exact.
        let mut frames: Vec<(usize, usize, Vec<&'a str>)> = Vec::new();
        let mut let_names = BTreeSet::new();
        let mut position = body;
        while position <= self.last[body] {
            while frames.last().is_some_and(|frame| frame.1 < position) {
                frames.pop();
            }
            match self.tokens[position] {
                SexpToken::Open => match self.head(position) {
                    Some(binder @ ("forall" | "exists" | "lambda" | "choice" | "let"))
                        if self.is_open(position + 2) =>
                    {
                        let list = position + 2;
                        let names = self.binding_names(Some(list));
                        frames.push((self.last[list] + 1, self.last[position], names));
                        position = if binder == "let" {
                            // Read the values in the outer scope; each
                            // entry's own name is a binding, not a use.
                            let entries = self.children(list).into_iter();
                            let_names.extend(entries.filter(|&e| self.is_open(e)).map(|e| e + 1));
                            list + 1
                        } else {
                            self.last[list] + 1
                        };
                        continue;
                    }
                    _ => {}
                },
                SexpToken::Atom(_) if !let_names.contains(&position) => {
                    let name = self.symbol(position).unwrap_or_default();
                    let bound = frames.iter().any(|(first, last, names)| {
                        (*first..=*last).contains(&position) && names.contains(&name)
                    });
                    if !bound && !name.starts_with(':') {
                        free.insert(name);
                    }
                }
                SexpToken::Atom(_) | SexpToken::Close => {}
            }
            position += 1;
        }
    }

    /// Every definition pinned Carcara may expand that this document
    /// introduces: `(name, parameters, body)`.
    fn definitions(&self) -> Vec<(&'a str, Vec<&'a str>, usize)> {
        let mut definitions = Vec::new();
        for position in 0..self.tokens.len() {
            match self.head(position) {
                Some("define-fun") => {
                    let fields = self.children(position);
                    if let (Some(name), Some(&body)) =
                        (fields.get(1).and_then(|&f| self.symbol(f)), fields.get(4))
                    {
                        let params = self.binding_names(fields.get(2).copied());
                        definitions.push((name, params, body));
                    }
                }
                Some("!") => {
                    let fields = self.children(position);
                    let Some(&term) = fields.get(1) else { continue };
                    for pair in fields.windows(2).skip(1) {
                        if self.symbol(pair[0]) == Some(":named") {
                            if let Some(label) = self.symbol(pair[1]) {
                                definitions.push((label, Vec::new(), term));
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        definitions
    }

    /// Every binding occurrence: `(bound name, first and last index of its
    /// scope)`, with `None` for an `anchor` variable (the whole proof).
    fn binders(&self) -> Vec<Binder<'a>> {
        let mut binders = Vec::new();
        for position in 0..self.tokens.len() {
            let Some(head) = self.head(position) else {
                continue;
            };
            let scope = Some((position, self.last[position]));
            let fields = self.children(position);
            let mut bind = |names: Vec<&'a str>, scope| {
                binders.extend(names.into_iter().map(|name| (name, scope)));
            };
            match head {
                "forall" | "exists" | "lambda" | "choice" | "let" => {
                    bind(self.binding_names(fields.get(1).copied()), scope);
                }
                "define-fun" | "define-fun-rec" => {
                    bind(self.binding_names(fields.get(2).copied()), scope);
                }
                "define-funs-rec" => {
                    let declarations = fields.get(1).map(|&d| self.children(d));
                    for declaration in declarations.unwrap_or_default() {
                        let parameters = self.children(declaration).get(1).copied();
                        bind(self.binding_names(parameters), scope);
                    }
                }
                "match" => {
                    for case in fields.iter().skip(2) {
                        let Some(&pattern) = self.children(*case).first() else {
                            continue;
                        };
                        let variables = if self.is_open(pattern) {
                            let parts = self.children(pattern).into_iter().skip(1);
                            parts.filter_map(|part| self.symbol(part)).collect()
                        } else {
                            self.symbol(pattern).into_iter().collect()
                        };
                        bind(variables, scope);
                    }
                }
                "anchor" => {
                    let arguments = fields
                        .windows(2)
                        .find(|pair| self.symbol(pair[0]) == Some(":args"))
                        .map(|pair| pair[1]);
                    for argument in arguments.map(|a| self.children(a)).unwrap_or_default() {
                        let parts = self.children(argument);
                        let variable = match parts.as_slice() {
                            [assign, variable, ..] if self.symbol(*assign) == Some(":=") => {
                                self.head(*variable).or_else(|| self.symbol(*variable))
                            }
                            [variable, ..] => self.symbol(*variable),
                            [] => None,
                        };
                        bind(variable.into_iter().collect(), None);
                    }
                }
                _ => {}
            }
        }
        binders
    }
}

/// Every definition's free symbols (its parameters excluded), and which
/// definitions name which.
struct DefinitionGraph<'a> {
    free: std::collections::BTreeMap<&'a str, BTreeSet<&'a str>>,
    /// `named_by[d]`: the definitions whose body names definition `d`.
    named_by: std::collections::BTreeMap<&'a str, Vec<&'a str>>,
}

impl<'a> DefinitionGraph<'a> {
    fn new(documents: &[LexedDocument<'a>]) -> Self {
        let mut free: std::collections::BTreeMap<&'a str, BTreeSet<&'a str>> =
            std::collections::BTreeMap::new();
        for document in documents {
            for (name, params, body) in document.definitions() {
                let mut symbols = BTreeSet::new();
                document.free_symbols(body, &mut symbols);
                symbols.retain(|symbol| !params.contains(symbol));
                free.entry(name).or_default().extend(symbols);
            }
        }
        let mut named_by: std::collections::BTreeMap<&'a str, Vec<&'a str>> =
            std::collections::BTreeMap::new();
        for (&name, symbols) in &free {
            for &symbol in symbols.iter().filter(|symbol| free.contains_key(*symbol)) {
                named_by.entry(symbol).or_default().push(name);
            }
        }
        Self { free, named_by }
    }

    fn is_definition(&self, name: &str) -> bool {
        self.free.contains_key(name)
    }

    /// The definitions whose expansion, closed over the definitions they
    /// name, mentions `bound` free. Linear in the graph.
    fn expanding_to(&self, bound: &str) -> BTreeSet<&'a str> {
        let mut reached: BTreeSet<&'a str> = (self.free.iter())
            .filter(|(_, symbols)| symbols.contains(bound))
            .map(|(&name, _)| name)
            .collect();
        let mut pending: Vec<&'a str> = reached.iter().copied().collect();
        while let Some(definition) = pending.pop() {
            for &outer in self.named_by.get(definition).into_iter().flatten() {
                if reached.insert(outer) {
                    pending.push(outer);
                }
            }
        }
        reached
    }
}

/// The binding occurrences of `problem` and `proof` that pinned Carcara reads
/// with a rebound or captured variable (see the module comment), as
/// `(bound name, definition)` pairs, sorted; for a rebinding the definition
/// is the bound name itself. Empty means no such binder.
///
/// Linear in the documents plus, per distinct bound name, the definition
/// graph: a printed proof can carry thousands of chained definitions.
pub fn binders_pinned_carcara_misreads(problem: &str, proof: &str) -> Vec<(String, String)> {
    // Cheap exit: with no definition there is nothing to expand.
    if ![problem, proof]
        .iter()
        .any(|document| document.contains(":named") || document.contains("define-fun"))
    {
        return Vec::new();
    }
    let documents = [LexedDocument::new(problem), LexedDocument::new(proof)];
    let binders: Vec<Vec<Binder<'_>>> = documents.iter().map(LexedDocument::binders).collect();
    if binders.iter().all(Vec::is_empty) {
        return Vec::new();
    }
    let graph = DefinitionGraph::new(&documents);
    let mut reaching = std::collections::BTreeMap::new();
    let mut proof_symbols: Option<BTreeSet<&str>> = None;
    let mut misread = BTreeSet::new();
    for (document, binders) in documents.iter().zip(&binders) {
        for &(bound, scope) in binders {
            if graph.is_definition(bound) {
                misread.insert((bound.to_string(), bound.to_string()));
                continue;
            }
            let definitions: &BTreeSet<&str> = reaching
                .entry(bound)
                .or_insert_with(|| graph.expanding_to(bound));
            if definitions.is_empty() {
                continue;
            }
            let named_in_scope: BTreeSet<&str>;
            let named = match scope {
                Some((first, last)) => {
                    named_in_scope = (first..=last)
                        .filter_map(|position| document.symbol(position))
                        .collect();
                    &named_in_scope
                }
                None => proof_symbols.get_or_insert_with(|| {
                    (0..documents[1].tokens.len())
                        .filter_map(|position| documents[1].symbol(position))
                        .collect()
                }),
            };
            for definition in definitions.intersection(named) {
                misread.insert((bound.to_string(), definition.to_string()));
            }
        }
    }
    misread.into_iter().collect()
}
