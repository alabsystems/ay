// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `run` to preserve private helper paths and behavior.

/// Whether z3 would have created its term manager by now. From then on it
/// refuses to change `:global-declarations`.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
enum Z3SessionStart {
    #[default]
    Fresh,
    Started,
    /// A command ay could not parse may or may not have started it.
    Unsure,
}

/// z3's assertion-level bookkeeping that the executor does not model, kept for
/// `--z3-mode`.
#[derive(Debug, Default)]
struct Z3ScopeState {
    start: Z3SessionStart,
    /// Per open assertion level, innermost last: whether a scoped declaration
    /// was made at that level.
    declaring_levels: Vec<bool>,
    /// The innermost assertion level (counted from 1) holding scoped
    /// declarations that a `(reset-assertions)` made permanent in the
    /// executor, where z3 still removes them when the level is popped.
    stale_declaration_level: Option<u32>,
}

/// Commands that make a declaration or definition, which a `(pop)` removes
/// when declarations are scoped. An assertion's `:named` labels are
/// definitions.
fn command_declares(cmd: &Command) -> bool {
    if let Command::Assert(term) = cmd {
        return ay_frontend::term_has_named_label(term);
    }
    matches!(
        cmd,
        Command::DeclareConst(..)
            | Command::DeclareFun(..)
            | Command::DeclareVar(..)
            | Command::DeclareRel(..)
            | Command::DeclareSort(..)
            | Command::DeclareSortParameter(..)
            | Command::DefineSort(..)
            | Command::DeclareDatatype(..)
            | Command::DeclareDatatypes(..)
            | Command::DefineFun(..)
            | Command::DefineFunRec(..)
            | Command::DefineFunsRec(..)
            | Command::SynthFun(..)
            | Command::SynthInv(..)
    )
}

/// z3's refusal of a `:global-declarations` (alias `:global-decls`) value:
/// non-symbols by their kind, and a symbol once the session has started or
/// when it is not `true` or `false`. The option decides the scope of each
/// declaration when it is made, so changing it while declarations are live
/// would give declarations of one session different lifetimes. `true` when
/// the command was refused.
fn reject_z3_fixed_option(
    executor: &mut Executor,
    state: &mut SmtTranscriptState,
    cmd: &Command,
) -> bool {
    let Command::SetOption(keyword, value) = cmd else {
        return false;
    };
    if !z3_mode_enabled() || !is_global_decls_option(keyword_key(keyword)) {
        return false;
    }
    const AFTER_START: &str =
        "error setting ':global-decls', option value cannot be modified after initialization";
    const NOT_BOOLEAN: &str = "invalid option value, true/false expected";
    let requested = sexpr_bool(value);
    let (message, diverges) = match value {
        SExpr::String(_) => ("option value is not a string", false),
        SExpr::Numeral(_) | SExpr::Decimal(_) | SExpr::Hexadecimal(_) | SExpr::Binary(_) => {
            ("option value is not a numeral", false)
        }
        SExpr::List(_) => ("invalid option value", false),
        _ => match (state.z3_scope.start, requested) {
            (Z3SessionStart::Started, _) => (AFTER_START, false),
            (_, None) => (NOT_BOOLEAN, false),
            (Z3SessionStart::Fresh, Some(_)) => return false,
            (Z3SessionStart::Unsure, Some(enabled)) if enabled == state.global_decls => {
                return false;
            }
            // z3 may or may not have taken the new value; neither choice
            // is known to match it.
            (Z3SessionStart::Unsure, Some(_)) => (AFTER_START, true),
        },
    };
    let error = set_option_error(state, keyword, message);
    print_regular_line(state, &error);
    state.note_recoverable_error();
    if diverges {
        mark_problem_incomplete(executor, state);
    }
    true
}

/// Withhold later verdicts outside `--z3-mode` when a `:global-declarations`
/// change comes after z3's session may have started. This mode takes the
/// change at any point; z3 refuses it then (SMT-LIB allows the option only
/// in start mode), so a name defined in a popped level would mean another
/// definition there.
fn withhold_after_late_global_declarations(
    executor: &mut Executor,
    state: &mut SmtTranscriptState,
    cmd: &Command,
) {
    let Command::SetOption(keyword, value) = cmd else {
        return;
    };
    if z3_mode_enabled()
        || !is_global_decls_option(keyword_key(keyword))
        || state.z3_scope.start == Z3SessionStart::Fresh
    {
        return;
    }
    if sexpr_bool(value).is_some_and(|enabled| enabled != state.global_decls) {
        mark_problem_incomplete(executor, state);
    }
}

/// Track the assertion levels of an accepted command. Runs after the
/// transcript's stack depth has been updated for `cmd`.
///
/// z3 keeps its assertion levels across `(reset-assertions)`, and a scoped
/// declaration made in one of them is removed when that level is popped. The
/// executor's frontend drops the frames instead, which makes those
/// declarations permanent. Once such a level is popped, the two solvers
/// disagree on which names exist, so every later verdict is withheld.
fn note_z3_scope_command(state: &mut SmtTranscriptState, cmd: &Command) {
    let depth = state.assertion_stack_depth as usize;
    let scoped_declaration = z3_mode_enabled() && command_declares(cmd) && !state.global_decls;
    let scope = &mut state.z3_scope;
    match cmd {
        Command::Reset => *scope = Z3ScopeState::default(),
        Command::ResetAssertions if z3_mode_enabled() => {
            if let Some(index) = scope
                .declaring_levels
                .iter()
                .rposition(|declared| *declared)
            {
                let level = index as u32 + 1;
                scope.stale_declaration_level = Some(
                    scope
                        .stale_declaration_level
                        .map_or(level, |stale| stale.max(level)),
                );
            }
            scope.declaring_levels.fill(false);
        }
        _ if scoped_declaration => {
            if let Some(level) = scope.declaring_levels.last_mut() {
                *level = true;
            }
        }
        _ => {}
    }
    scope.declaring_levels.resize(depth, false);
    if scope
        .stale_declaration_level
        .is_some_and(|level| level as usize > depth)
    {
        scope.stale_declaration_level = None;
        state.mark_incomplete();
    }
}

/// Bring the executor in line with z3 after an accepted `(reset)` or
/// `(reset-assertions)` under `--z3-mode`.
///
/// z3 keeps its assertion levels across `(reset-assertions)`, and what is
/// asserted or declared afterwards belongs to them: a later `(pop)` removes
/// it. The executor empties its stack, so the same number of empty levels is
/// opened in it again. z3 also keeps `:global-declarations` across `(reset)`,
/// which the executor's frontend returns to its default.
fn restore_z3_session_after_reset(
    executor: &mut Executor,
    transcript: &mut SmtTranscriptState,
    cmd: &Command,
) {
    if !z3_mode_enabled() {
        return;
    }
    let restored = match cmd {
        Command::ResetAssertions if transcript.assertion_stack_depth > 0 => {
            let levels = transcript.assertion_stack_depth;
            let global = global_declarations_in_force(executor);
            let opened = executor.execute_authored(&Command::Push(levels)).is_ok();
            if opened {
                transcript.executor_assertion_stack_depth = levels;
                record_opened_levels(transcript, levels, global);
            }
            opened
        }
        Command::Reset if transcript.global_decls => {
            let set = executor
                .execute_authored(&Command::SetOption(
                    ":global-declarations".to_string(),
                    SExpr::True,
                ))
                .is_ok();
            if set {
                record_session_option(transcript, "(set-option :global-declarations true)");
            }
            set
        }
        _ => true,
    };
    if !restored {
        transcript.replay_log = None;
        mark_problem_incomplete(executor, transcript);
    }
}

/// Pop more levels than the executor holds, which happens only when it could
/// not reopen the levels z3 keeps across `(reset-assertions)`. The executor's
/// own levels are the innermost ones and are popped; the rest cannot be
/// modelled, so the problem is marked incomplete.
fn pop_beyond_executor_levels(executor: &mut Executor, state: &mut SmtTranscriptState) {
    let held = state.executor_assertion_stack_depth;
    if held > 0 {
        let pop = Command::Pop(held);
        if executor.execute_authored(&pop).is_ok() {
            let global = global_declarations_in_force(executor);
            record_accepted_command(state, &pop, global);
        } else {
            state.replay_log = None;
        }
    }
    mark_problem_incomplete(executor, state);
}
