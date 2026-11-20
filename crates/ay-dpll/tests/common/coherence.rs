// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Check that a run's `(get-value)` answers and its printed `(get-model)`
//! describe one model of the run's assertions (#get-value-published-model).
//!
//! [`assert_published_values_coherent`] runs a script through [`super::solve_vec`]
//! and replays what it printed:
//!
//! 1. the `(get-model)` define-funs, without those named by a datatype
//!    constructor, selector or `is-<constructor>` tester;
//! 2. the `(get-value)` pairs; an `(error ...)` in place of a `(get-model)` or
//!    `(get-value)` output yields nothing and is allowed only under
//!    [`Expect::AllowBatchError`];
//! 3. every abstract value `(as A S)` whose `A` starts with `@`, the spelling
//!    the printer gives abstract values, and is not a declared symbol or a
//!    constructor of the script is renamed to a fresh constant of sort `S`,
//!    and the fresh constants of one sort are asserted pairwise distinct;
//!    other qualified identifiers, such as `(as const S)`, are kept;
//! 4. the script's declarations (less those the model defines), the renamed
//!    define-funs, the script's assertions and one `(assert (= t v))` per pair
//!    go to a fresh solve, which must answer `sat`;
//! 5. the same replay goes to the z3 oracle when one is usable (required under
//!    `Z3_DIFFERENTIAL_REQUIRED`), which must answer `sat`;
//! 6. [`Expect::Literal`] also requires that no abstract value was renamed at a
//!    datatype sort. Abstract values of a `declare-sort` sort are renamed in
//!    every mode: z3 rejects `(as @U!0 U)` as input, so the literal text of
//!    such a model cannot be replayed in z3 as printed.

use std::collections::{BTreeMap, HashSet};

use ay_frontend::sexp::{parse_sexps, SExpr};

use super::solve_vec;
use super::z3::{solve_with_z3, z3_oracle};

/// What a script's printed values must satisfy beyond coherence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Expect {
    /// Every output is a value; the replay is `sat`.
    Coherent,
    /// [`Expect::Coherent`], and no abstract value appears at a datatype sort.
    Literal,
    /// [`Expect::Coherent`], except that a `(get-model)` or `(get-value)`
    /// output may be an `(error ...)`.
    AllowBatchError,
}

/// What one run printed, as the helper read it.
#[derive(Debug, Default)]
pub(crate) struct PublishedRun {
    /// The run's output lines.
    pub(crate) outputs: Vec<String>,
    /// The printed define-funs by name, as raw text.
    pub(crate) definitions: BTreeMap<String, String>,
    /// The `(get-value)` pairs as `(term, value)` raw texts, in output order.
    pub(crate) pairs: Vec<(String, String)>,
    /// The `(error ...)` outputs.
    pub(crate) errors: Vec<String>,
}

impl PublishedRun {
    /// The value printed for `term`, matched on its raw text.
    pub(crate) fn value(&self, term: &str) -> Option<&str> {
        self.pairs
            .iter()
            .find(|(t, _)| t == term)
            .map(|(_, v)| v.as_str())
    }

    /// The value printed for `term`; panics with the run's outputs when the run
    /// printed none.
    pub(crate) fn expect_value(&self, term: &str) -> &str {
        self.value(term).unwrap_or_else(|| {
            panic!(
                "no value printed for {term}; outputs:\n{}",
                self.outputs.join("\n")
            )
        })
    }
}

/// The declarations a script makes, as the helper needs them.
#[derive(Default)]
struct Declarations {
    /// Declared and defined symbols.
    symbols: HashSet<String>,
    /// Constructor, selector and tester names, which the model does not define
    /// as functions of the script.
    datatype_internal: HashSet<String>,
    /// Constructor names.
    constructors: HashSet<String>,
    /// Datatype sort names.
    datatype_sorts: HashSet<String>,
}

fn sym(expr: &SExpr) -> Option<&str> {
    expr.as_symbol()
}

fn head(expr: &SExpr) -> Option<&str> {
    expr.as_list()?.first()?.as_symbol()
}

impl Declarations {
    fn of(script: &[SExpr]) -> Self {
        let mut d = Declarations::default();
        for command in script {
            let Some(items) = command.as_list() else {
                continue;
            };
            match head(command) {
                Some("declare-fun" | "declare-const" | "define-fun" | "define-const") => {
                    if let Some(name) = items.get(1).and_then(sym) {
                        d.symbols.insert(name.to_owned());
                    }
                }
                Some("declare-datatype") => {
                    if let (Some(name), Some(body)) = (items.get(1).and_then(sym), items.get(2)) {
                        d.datatype_sorts.insert(name.to_owned());
                        d.add_constructors(body);
                    }
                }
                Some("declare-datatypes") => {
                    if let Some(sorts) = items.get(1).and_then(SExpr::as_list) {
                        for sort in sorts {
                            if let Some(name) = sort.as_list().and_then(|s| s.first()).and_then(sym)
                            {
                                d.datatype_sorts.insert(name.to_owned());
                            }
                        }
                    }
                    if let Some(bodies) = items.get(2).and_then(SExpr::as_list) {
                        for body in bodies {
                            d.add_constructors(body);
                        }
                    }
                }
                _ => {}
            }
        }
        d
    }

    /// Records the constructors and selectors of one datatype body, which is
    /// a list of constructor declarations, possibly under `(par (..) ..)`.
    fn add_constructors(&mut self, body: &SExpr) {
        let body = match body.as_list() {
            Some([par, _, inner]) if par.is_symbol("par") => inner,
            _ => body,
        };
        let Some(constructors) = body.as_list() else {
            return;
        };
        for constructor in constructors {
            let (name, selectors) = match constructor {
                SExpr::Symbol(name) => (name.as_str(), &[][..]),
                SExpr::List(items) => match items.split_first() {
                    Some((SExpr::Symbol(name), selectors)) => (name.as_str(), selectors),
                    _ => continue,
                },
                _ => continue,
            };
            self.constructors.insert(name.to_owned());
            self.datatype_internal.insert(name.to_owned());
            self.datatype_internal.insert(format!("is-{name}"));
            for selector in selectors {
                if let Some(selector) = selector.as_list().and_then(|s| s.first()).and_then(sym) {
                    self.datatype_internal.insert(selector.to_owned());
                }
            }
        }
    }

    fn is_datatype_sort(&self, sort: &SExpr) -> bool {
        let name = match sort {
            SExpr::Symbol(name) => Some(name.as_str()),
            SExpr::List(items) => items.first().and_then(sym),
            _ => None,
        };
        name.is_some_and(|name| self.datatype_sorts.contains(name))
    }
}

/// Renames abstract values to fresh constants (step 3).
struct Renamer<'a> {
    declarations: &'a Declarations,
    /// Fresh constant by `(as A S)` text, with its sort.
    fresh: BTreeMap<String, (String, SExpr)>,
}

impl Renamer<'_> {
    fn rename(&mut self, expr: &SExpr) -> SExpr {
        if let Some([as_, SExpr::Symbol(value), sort]) = expr.as_list() {
            if as_.is_symbol("as")
                && value.starts_with('@')
                && !self.declarations.symbols.contains(value)
                && !self.declarations.constructors.contains(value)
            {
                let next = self.fresh.len();
                let (name, _) = self
                    .fresh
                    .entry(expr.to_raw_string())
                    .or_insert_with(|| (format!("__abstract{next}"), sort.clone()));
                return SExpr::Symbol(name.clone());
            }
        }
        match expr.as_list() {
            Some(items) => SExpr::List(items.iter().map(|item| self.rename(item)).collect()),
            None => expr.clone(),
        }
    }
}

fn parse_output(line: &str) -> Vec<SExpr> {
    parse_sexps(line).unwrap_or_else(|e| panic!("unparseable output {line:?}: {e}"))
}

fn first_status(outputs: &[String]) -> Option<&str> {
    outputs
        .iter()
        .map(|line| line.trim())
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}

/// Runs `script` and checks its printed values as the module documentation
/// states; returns what the run printed.
pub(crate) fn assert_published_values_coherent(script: &str, expect: Expect) -> PublishedRun {
    let commands = parse_sexps(script).unwrap_or_else(|e| panic!("script does not parse: {e}"));
    let declarations = Declarations::of(&commands);
    let mut run = PublishedRun {
        outputs: solve_vec(script),
        ..PublishedRun::default()
    };
    let shown = run.outputs.join("\n");
    assert_eq!(
        first_status(&run.outputs),
        Some("sat"),
        "the script must be sat:\n{shown}"
    );

    // Steps 1 and 2: every output after the status answers one query.
    let mut renamer = Renamer {
        declarations: &declarations,
        fresh: BTreeMap::new(),
    };
    let mut definitions = Vec::new();
    let mut pair_asserts = Vec::new();
    let status_at = run
        .outputs
        .iter()
        .position(|line| line.trim() == "sat")
        .expect("status checked above");
    for line in &run.outputs[status_at + 1..] {
        for response in parse_output(line) {
            let Some(items) = response.as_list() else {
                panic!("unexpected output {response}:\n{shown}");
            };
            if head(&response) == Some("error") {
                run.errors.push(response.to_raw_string());
                continue;
            }
            if items
                .iter()
                .all(|item| matches!(item.as_list(), Some([_, _])))
                && !items.is_empty()
            {
                for pair in items {
                    let [term, value] = pair.as_list().expect("checked above") else {
                        unreachable!("pairs have two elements");
                    };
                    run.pairs
                        .push((term.to_raw_string(), value.to_raw_string()));
                    pair_asserts.push(format!(
                        "(assert (= {} {}))",
                        term.to_raw_string(),
                        renamer.rename(value).to_raw_string()
                    ));
                }
                continue;
            }
            // The model, with or without the `model` keyword the printer puts
            // first.
            let entries = match items.split_first() {
                Some((first, rest)) if first.is_symbol("model") => rest,
                _ => items,
            };
            for definition in entries {
                assert_eq!(
                    head(definition),
                    Some("define-fun"),
                    "unexpected model entry {definition}:\n{shown}"
                );
                let name = definition.as_list().and_then(|d| d.get(1)).and_then(sym);
                let name = name.unwrap_or_else(|| panic!("unnamed definition {definition}"));
                if declarations.datatype_internal.contains(name) {
                    continue;
                }
                run.definitions
                    .insert(name.to_owned(), definition.to_raw_string());
                definitions.push(renamer.rename(definition).to_raw_string());
            }
        }
    }
    if expect != Expect::AllowBatchError {
        assert!(run.errors.is_empty(), "the run printed an error:\n{shown}");
    }
    if expect == Expect::Literal {
        let at_datatype: Vec<&String> = renamer
            .fresh
            .iter()
            .filter(|(_, (_, sort))| declarations.is_datatype_sort(sort))
            .map(|(value, _)| value)
            .collect();
        assert!(
            at_datatype.is_empty(),
            "abstract values printed at a datatype sort: {at_datatype:?}\n{shown}"
        );
    }

    // Step 4: the replay.
    let mut replay = vec!["(set-logic ALL)".to_owned()];
    for command in &commands {
        match head(command) {
            Some("set-logic" | "check-sat" | "get-model" | "get-value" | "assert" | "exit") => {}
            Some("declare-fun" | "declare-const")
                if command
                    .as_list()
                    .and_then(|c| c.get(1))
                    .and_then(sym)
                    .is_some_and(|name| run.definitions.contains_key(name)) => {}
            _ => replay.push(command.to_raw_string()),
        }
    }
    let mut by_sort: BTreeMap<String, Vec<&str>> = BTreeMap::new();
    for (name, sort) in renamer.fresh.values() {
        replay.push(format!("(declare-const {name} {})", sort.to_raw_string()));
        by_sort.entry(sort.to_raw_string()).or_default().push(name);
    }
    for names in by_sort.values().filter(|names| names.len() > 1) {
        replay.push(format!("(assert (distinct {}))", names.join(" ")));
    }
    replay.extend(definitions);
    for command in &commands {
        if head(command) == Some("assert") {
            replay.push(command.to_raw_string());
        }
    }
    replay.extend(pair_asserts);
    replay.push("(check-sat)".to_owned());
    let replay = replay.join("\n");

    let replayed = solve_vec(&replay);
    assert_eq!(
        first_status(&replayed),
        Some("sat"),
        "ay replay of the printed values is not sat ({replayed:?}):\n{replay}\n-- run output:\n{shown}"
    );

    // Step 5: the z3 leg.
    if z3_oracle().is_some() {
        let z3 = solve_with_z3(&replay).unwrap_or_else(|e| panic!("z3 failed: {e}\n{replay}"));
        let z3_lines: Vec<String> = z3.lines().map(str::to_owned).collect();
        assert!(
            !z3_lines.iter().any(|line| line.starts_with("(error")),
            "z3 rejected the replay:\n{z3}\n{replay}"
        );
        assert_eq!(
            first_status(&z3_lines),
            Some("sat"),
            "z3 replay of the printed values is not sat:\n{z3}\n{replay}\n-- run output:\n{shown}"
        );
    }
    run
}
