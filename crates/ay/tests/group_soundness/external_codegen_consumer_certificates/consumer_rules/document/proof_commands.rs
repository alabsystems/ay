// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expand proof commands in document order before interning terms.

use super::super::query::atoms;
use super::super::reader::{keyword, read_sexps, read_step, Command, Sexp};
use super::{Document, HashSet};

impl Document {
    /// The proof's commands, read in document order as Carcara reads them:
    /// a nullary `define-fun` is expanded as it is read, and a term is
    /// expanded through the definitions before it only. A definition the
    /// mirror does not read that way (with parameters, after a command that
    /// uses its name, or a second one of a name) is recorded in
    /// `proof_defects` and not applied; a definition of a name the problem
    /// uses is recorded in `redefined`.
    ///
    /// REGRESSION (reasoned from source on a4b66eeff): a `define-fun`'s
    /// parameters were dropped and its body expanded over the whole document,
    /// steps before the definition included.
    pub(super) fn read_proof(&mut self, proof: &str) {
        let document = self;
        let commands = match read_sexps(proof) {
            Ok(commands) => commands,
            Err(error) => {
                document.proof_defects.push(format!(
                    "AY's SMT-LIB front end does not read the proof: {error}"
                ));
                return;
            }
        };
        // Every atom of the commands read so far.
        let mut seen = HashSet::new();
        let mut defined = HashSet::new();
        for command in commands {
            match command.head() {
                Some("define-fun") => {
                    let [Sexp::Atom(name), parameters, _sort, body] = command.args() else {
                        document
                            .proof_defects
                            .push(format!("a malformed define-fun: {command:?}"));
                        continue;
                    };
                    if document.problem_symbols.contains(name) {
                        document.redefined.push(name.clone());
                    }
                    let defect = if !matches!(parameters, Sexp::List(items) if items.is_empty()) {
                        Some("with parameters")
                    } else if !defined.insert(name.clone()) {
                        Some("a second time")
                    } else if seen.contains(name) {
                        Some("after a command that uses it")
                    } else {
                        None
                    };
                    if let Some(defect) = defect {
                        document
                            .proof_defects
                            .push(format!("the proof defines {name} {defect}"));
                    } else {
                        // Printed in dependency order: expanding each as it is
                        // read keeps the recursion as shallow as one body.
                        let id = document.expand(body);
                        document.expanded_names.insert(name.clone(), id);
                    }
                }
                Some("assume") => match command.args() {
                    [Sexp::Atom(id), term] => {
                        document
                            .commands
                            .push(Command::Assume(id.clone(), term.clone()));
                    }
                    other => panic!("malformed assume: {other:?}"),
                },
                Some("step") => document.commands.push(Command::Step(read_step(&command))),
                Some("anchor") => {
                    let end = match keyword(command.args(), ":step") {
                        Some(Sexp::Atom(end)) => end.clone(),
                        _ => String::new(),
                    };
                    let context = keyword(command.args(), ":args").is_some();
                    document.commands.push(Command::Anchor(end, context));
                }
                _ => {}
            }
            atoms(&command, &mut seen);
        }
    }
}
