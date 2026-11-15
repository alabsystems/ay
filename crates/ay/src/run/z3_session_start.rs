// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `run` to preserve private helper paths and behavior.

/// What one command does to z3's session start.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Z3StartEffect {
    None,
    Starts,
    Unsure,
}

impl Z3SessionStart {
    fn after(self, effect: Z3StartEffect) -> Self {
        match (self, effect) {
            (Self::Started, _) | (_, Z3StartEffect::Starts) => Self::Started,
            (Self::Unsure, _) | (_, Z3StartEffect::Unsure) => Self::Unsure,
            (Self::Fresh, Z3StartEffect::None) => Self::Fresh,
        }
    }
}

/// Commands whose parsing never touches z3's term manager, whatever their
/// arguments.
const Z3_NEVER_STARTING_COMMANDS: &[&str] = &[
    "set-option",
    "set-info",
    "set-logic",
    "echo",
    "get-option",
    "reset",
    "reset-assertions",
    "exit",
    "labels",
    "get-model",
    "get-assignment",
    "get-unsat-core",
    "get-proof",
    "get-proof-graph",
    "get-assertions",
    "get-unsat-assumptions",
    "dbg-params",
    "get-user-tactics",
    "dbg-sexpr",
    "dbg-pp-var",
    "pop",
];

/// Commands that start the session however they are written.
const Z3_ALWAYS_STARTING_COMMANDS: &[&str] = &[
    "get-value",
    "check-sat",
    "check-sat-assuming",
    "define-fun-rec",
    "define-funs-rec",
    "query",
    "declare-var",
    "declare-rel",
];

/// Commands that start the session once their first argument parses as a
/// term: anything but a keyword, `()` or a list headed by a numeral.
const Z3_TERM_FIRST_COMMANDS: &[&str] = &[
    "assert",
    "assert-soft",
    "assert-not",
    "maximize",
    "minimize",
    "rule",
    "eval",
    "simplify",
    "display",
    "get-interpolant",
    "dbg-size",
    "dbg-lt",
    "dbg-translator",
    "dbg-used-vars",
    "dbg-elim-unused-vars",
    "dbg-instantiate",
    "dbg-th-rewriter",
    "dbg-bool-rewriter",
    "dbg-bool-flat-rewriter",
    "dbg-elim-and",
    "dbg-instantiate-nested",
    "eufi",
    "mbi",
    "mbp",
];

/// Commands that start the session once their first argument is a symbol.
const Z3_NAME_FIRST_COMMANDS: &[&str] = &[
    "declare-const",
    "declare-fun",
    "define-fun",
    "define-const",
    "declare-datatype",
    "model-add",
];

/// Commands that start the session as soon as they have any argument.
const Z3_ANY_ARGUMENT_COMMANDS: &[&str] = &[
    "get-consequences",
    "dbg-some-value",
    "euf-project",
    "mbp-qel",
    "qe-lite",
    "qel",
];

/// Commands z3 4.12.5 knows whose effect on the session start depends on
/// more than the forms measured above.
const Z3_UNCLASSIFIED_COMMANDS: &[&str] = &[
    "check-sat-using",
    "apply",
    "declare-codatatypes",
    "declare-tactic",
    "set-simplifier",
    "display-dimacs",
    "dbg-subst",
    "dbg-shift-vars",
    "infer",
    "include",
];

fn is_symbol_like(item: &SExpr) -> bool {
    matches!(item, SExpr::Symbol(_) | SExpr::True | SExpr::False)
}

/// Whether z3 reaches its term manager while parsing `item` as a term.
fn z3_term_argument_starts(item: Option<&SExpr>) -> Z3StartEffect {
    match item {
        None | Some(SExpr::Keyword(_)) => Z3StartEffect::None,
        Some(SExpr::List(items)) => match items.first() {
            None | Some(SExpr::Numeral(_)) => Z3StartEffect::None,
            Some(SExpr::Symbol(_) | SExpr::True | SExpr::False | SExpr::List(_)) => {
                Z3StartEffect::Starts
            }
            Some(_) => Z3StartEffect::Unsure,
        },
        Some(_) => Z3StartEffect::Starts,
    }
}

fn starts_if(condition: bool) -> Z3StartEffect {
    if condition {
        Z3StartEffect::Starts
    } else {
        Z3StartEffect::None
    }
}

/// z3 4.12.5's session start for one command form, from its head and
/// arguments. Measured against z3 on every head with valid and malformed
/// arguments; heads z3 does not know are answered `unsupported` and start
/// nothing.
fn z3_form_start_effect(items: &[SExpr]) -> Z3StartEffect {
    let Some(head) = items.first().and_then(SExpr::as_symbol) else {
        return Z3StartEffect::None;
    };
    let args = &items[1..];
    let first = args.first();
    let first_is_name = first.is_some_and(is_symbol_like);
    if Z3_NEVER_STARTING_COMMANDS.contains(&head) {
        return Z3StartEffect::None;
    }
    if Z3_ALWAYS_STARTING_COMMANDS.contains(&head) {
        return Z3StartEffect::Starts;
    }
    if Z3_TERM_FIRST_COMMANDS.contains(&head) {
        return z3_term_argument_starts(first);
    }
    if Z3_NAME_FIRST_COMMANDS.contains(&head) {
        return starts_if(first_is_name);
    }
    if Z3_ANY_ARGUMENT_COMMANDS.contains(&head) {
        return starts_if(first.is_some());
    }
    if Z3_UNCLASSIFIED_COMMANDS.contains(&head) {
        return Z3StartEffect::Unsure;
    }
    match head {
        "get-info" => starts_if(matches!(
            first,
            Some(SExpr::Keyword(keyword))
                if matches!(keyword_key(keyword), "all-statistics" | "rlimit")
        )),
        "help" | "help-tactic" | "help-simplifier" | "get-objectives" => starts_if(args.is_empty()),
        "push" => match first {
            None => Z3StartEffect::Starts,
            // z3 refuses `(push -1)` ("value is negative"), so it starts nothing.
            Some(SExpr::Numeral(levels)) if levels.starts_with('-') => Z3StartEffect::None,
            Some(SExpr::Numeral(levels)) => starts_if(levels.trim_start_matches('0') != ""),
            Some(_) => Z3StartEffect::None,
        },
        "declare-map" => starts_if(first_is_name && args.len() >= 2),
        "declare-sort" => {
            starts_if(first_is_name && matches!(args.get(1), None | Some(SExpr::Numeral(_))))
        }
        "define-sort" => match args.get(1) {
            Some(SExpr::List(parameters)) if first_is_name => {
                if parameters.iter().all(is_symbol_like) {
                    Z3StartEffect::Starts
                } else {
                    Z3StartEffect::Unsure
                }
            }
            _ => Z3StartEffect::None,
        },
        "declare-datatypes" => match first {
            Some(SExpr::List(declarations)) if declarations.iter().all(is_symbol_like) => {
                Z3StartEffect::Starts
            }
            Some(SExpr::List(_)) => Z3StartEffect::Unsure,
            _ => Z3StartEffect::None,
        },
        "del" | "assume" => match first {
            None => Z3StartEffect::Starts,
            other => z3_term_argument_starts(other),
        },
        "dbg-set" | "dbg-get-qbody" if first_is_name => z3_term_argument_starts(args.get(1)),
        "dbg-set" | "dbg-get-qbody" => Z3StartEffect::None,
        "dbg-set-next-id" => starts_if(matches!(first, Some(SExpr::Numeral(_)))),
        _ => Z3StartEffect::None,
    }
}

/// The session-start effect of one command's source text.
fn z3_source_start_effect(text: &str) -> Z3StartEffect {
    match parse_sexp(text) {
        Ok(sexpr) => sexpr
            .as_list()
            .map_or(Z3StartEffect::Unsure, z3_form_start_effect),
        Err(_) => Z3StartEffect::Unsure,
    }
}

/// The session-start effect of source text ay could not parse: every
/// top-level form in it, as z3 would run each.
fn z3_text_start_effect(text: &str) -> Z3StartEffect {
    let forms = collect_command_sources(text);
    if forms.is_empty() {
        return if skip_smt_trivia(text).is_empty() {
            Z3StartEffect::None
        } else {
            Z3StartEffect::Unsure
        };
    }
    let mut effect = Z3StartEffect::None;
    for form in &forms {
        let form_effect = z3_source_start_effect(&form.text);
        match form_effect {
            Z3StartEffect::Starts => return Z3StartEffect::Starts,
            Z3StartEffect::Unsure => effect = Z3StartEffect::Unsure,
            Z3StartEffect::None => {}
        }
    }
    effect
}

/// The session-start effect of a parsed command. The parser folds several
/// z3 commands into one variant (`help` into `echo`, the `dbg-*` term
/// commands into `display`, `check-sat-using` into `check-sat`), so the
/// command's source text decides where that matters.
fn z3_command_start_effect(cmd: &Command, source: Option<&CommandSource>) -> Z3StartEffect {
    match cmd {
        Command::Push(levels) => starts_if(*levels > 0),
        Command::GetInfo(keyword) => {
            starts_if(matches!(keyword_key(keyword), "all-statistics" | "rlimit"))
        }
        Command::Echo(_) => source.map_or(Z3StartEffect::Unsure, |source| {
            z3_source_start_effect(&source.text)
        }),
        Command::SetLogic(_)
        | Command::SetOption(..)
        | Command::SetOptionAttribute(_)
        | Command::SetInfo(..)
        | Command::SetInfoAttribute(_)
        | Command::GetOption(_)
        | Command::Reset
        | Command::ResetAssertions
        | Command::Exit
        | Command::Labels
        | Command::GetModel
        | Command::GetAssignment
        | Command::GetUnsatCore
        | Command::GetUnsatCoreWithFarkas
        | Command::GetUnsatAssumptions
        | Command::GetProof
        | Command::GetAssertions
        | Command::Pop(_)
        | Command::DebugPpVar(_)
        | Command::GetObjectiveCertificates
        | Command::GetAbduct(..)
        | Command::ComputeInterpolant(..)
        | Command::DeclareSortParameter(_)
        | Command::SynthFun(..)
        | Command::SynthInv(..)
        | Command::SygusConstraint(_)
        | Command::InvConstraint(..)
        | Command::CheckSynth => Z3StartEffect::None,
        _ => Z3StartEffect::Starts,
    }
}

fn note_z3_session_command(state: &mut SmtTranscriptState, cmd: &Command) {
    let effect = z3_command_start_effect(cmd, state.current_source.as_ref());
    state.z3_scope.start = state.z3_scope.start.after(effect);
}

/// Tell the frontend, before a command runs, once z3's session has started
/// or may have: z3 reads `:smtlib2_compliant` only as it starts. Mutable
/// access to the context discards the last check's result, so it is taken
/// only the first time; a check-sat starts the session, so no result exists
/// before then.
fn note_z3_session_start_in_context(executor: &mut Executor, state: &SmtTranscriptState) {
    if z3_mode_enabled()
        && state.z3_scope.start != Z3SessionStart::Fresh
        && !executor.context().z3_session_start_noted()
    {
        executor.context_mut().note_z3_session_started();
    }
}

/// Record the session-start effect of source text that failed to parse.
fn note_z3_session_failed_source(state: &mut SmtTranscriptState, text: &str) {
    state.z3_scope.start = state.z3_scope.start.after(z3_text_start_effect(text));
}

/// How a failed assertion's `:named` labels ended, when z3's session state
/// after it is what `--z3-mode` answers for. Outside z3 mode a label's
/// rejection drops the assertion like any other refused assertion, which
/// withholds a later `sat`.
fn z3_assertion_label_failure(
    executor: &mut Executor,
    cmd: &Command,
) -> Option<ay_frontend::LabelFailure> {
    if z3_mode_enabled() && matches!(cmd, Command::Assert(_)) {
        executor.context_mut().take_label_failure()
    } else {
        None
    }
}

/// Withhold later verdicts once z3's names and this session's differ.
///
/// An assertion whose label outcome leaves the session in another state
/// from z3's ([`ay_frontend::LabelFailure::Diverged`]) withholds every later
/// verdict, in both modes; so does, under `--z3-mode`, a label z3 binds and
/// this session left unbound ([`ay_frontend::LabelFailure::Unbound`]) or a
/// label outside an assertion. Otherwise the session differs from z3's only
/// in the names of the command's labels: under `--z3-mode` a label this
/// session binds and z3 may not reach
/// ([`ay_frontend::LabelFailure::Unvouched`]), and outside it a label it
/// left unbound or a label outside an assertion. Those names are recorded
/// (a name with a character outside the simple-symbol set withholds every
/// later verdict instead), and a later command withholds verdicts only when
/// it mentions one ([`withhold_before_label_mention`]): an unsat-core script
/// whose labels are never mentioned again keeps its answers, and a
/// `(check-sat-assuming ((! l :named h)))` stays a strict certificate for
/// `l`.
fn withhold_after_labels_z3_binds(
    executor: &mut Executor,
    transcript: &mut SmtTranscriptState,
    cmd: &Command,
) {
    let failure = if matches!(cmd, Command::Assert(_)) {
        executor.context_mut().take_label_failure()
    } else {
        None
    };
    let labels_outside_assert = command_has_named_label_outside_assert(cmd);
    let names_only = match failure {
        None | Some(ay_frontend::LabelFailure::Exact) => false,
        Some(ay_frontend::LabelFailure::Unvouched) => true,
        Some(ay_frontend::LabelFailure::Unbound) if !z3_mode_enabled() => true,
        Some(_) => {
            mark_problem_incomplete(executor, transcript);
            return;
        }
    };
    if z3_mode_enabled() && labels_outside_assert {
        mark_problem_incomplete(executor, transcript);
        return;
    }
    if names_only || labels_outside_assert {
        let names = command_label_names(cmd);
        // The mention scan follows names made of simple-symbol characters;
        // any other name withholds every later answer.
        if !names
            .iter()
            .all(|name| name.chars().all(is_simple_symbol_char))
        {
            mark_problem_incomplete(executor, transcript);
            return;
        }
        transcript.labels_bound_unlike_z3.extend(names);
    }
}

/// Withhold verdicts from the first command that mentions a label name whose
/// binding here may differ from z3's ([`withhold_after_labels_z3_binds`]):
/// the name may resolve to something else here, or be declared here where z3
/// refuses it. Checked before the command runs, so a query that mentions one
/// answers `unknown`.
fn withhold_before_label_mention(executor: &mut Executor, transcript: &mut SmtTranscriptState) {
    if transcript.labels_bound_unlike_z3.is_empty() {
        return;
    }
    let mentioned = transcript.current_source.as_ref().map_or(true, |source| {
        source_mentions_any_symbol(&source.text, &transcript.labels_bound_unlike_z3)
    });
    if mentioned {
        mark_problem_incomplete(executor, transcript);
    }
}

/// The `:named` label names written in `cmd`'s terms.
fn command_label_names(cmd: &Command) -> Vec<String> {
    let mut names = Vec::new();
    let mut terms = command_terms(cmd);
    while let Some(term) = terms.pop() {
        match term {
            Term::App(_, arguments)
            | Term::IndexedApp(_, _, arguments)
            | Term::QualifiedApp(_, _, arguments) => terms.extend(arguments),
            Term::Let(bindings, body) => {
                terms.extend(bindings.iter().map(|(_, value)| value));
                terms.push(body);
            }
            Term::Forall(_, body) | Term::Exists(_, body) | Term::Lambda(_, body) => {
                terms.push(body);
            }
            Term::Annotated(body, attributes) => {
                for (keyword, value) in attributes {
                    if keyword != ":named" {
                        continue;
                    }
                    match value {
                        SExpr::Symbol(name) => names.push(name.clone()),
                        SExpr::True => names.push("true".to_string()),
                        SExpr::False => names.push("false".to_string()),
                        _ => {}
                    }
                }
                terms.push(body);
            }
            Term::Match(scrutinee, cases) => {
                terms.push(scrutinee);
                terms.extend(cases.iter().map(|(_, body)| body));
            }
            _ => {}
        }
    }
    names
}

/// Characters of an SMT-LIB simple symbol. Every lexer reads at least these
/// as symbol characters.
fn is_simple_symbol_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || "~!@$%^&*_-+=<>.?/".contains(c)
}

/// Whether `text` may mention any of `names`, each made of simple-symbol
/// characters ([`withhold_after_labels_z3_binds`]), however its strings,
/// comments and quoted symbols are read. Nothing is skipped:
///
/// - a plain mention is a run of simple-symbol characters with none on
///   either side, which a `"`, `;` or `|` before it cannot hide, so every
///   such run is a candidate;
/// - a `|quoted|` mention holds no `|`, so it is the text between two
///   consecutive `|`, and every such stretch is a candidate, also with `\`
///   removed, for a lexer that reads `\` as an escape.
///
/// So the scan can only report more mentions than a lexer would. A name it
/// cannot follow, one holding `|` or `\` (which a quoted symbol spells only
/// with escapes) or the empty name, counts as mentioned by every command.
fn source_mentions_any_symbol(text: &str, names: &std::collections::HashSet<String>) -> bool {
    if names
        .iter()
        .any(|name| name.is_empty() || name.contains(['|', '\\']))
    {
        return true;
    }
    let plain = text.split(|c: char| !is_simple_symbol_char(c));
    let mut quoted = text.split('|').skip(1);
    if plain
        .chain(quoted.clone())
        .any(|token| names.contains(token))
    {
        return true;
    }
    text.contains('\\') && quoted.any(|token| names.contains(&token.replace('\\', "")))
}
