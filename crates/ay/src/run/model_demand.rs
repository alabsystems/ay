// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `run` to preserve private helper paths and behavior.

/// Command names whose execution READS the model of the preceding `check-sat`.
///
/// `(include "f")` is here because AY does not implement it: the spliced file's
/// commands are invisible to this scan, so any script mentioning it must be
/// treated as possibly reading a model.
const MODEL_READING_COMMANDS: &[&str] = &[
    "check-synth",
    "eval",
    "get-assignment",
    "get-model",
    "get-objective-certificates",
    "get-objectives",
    "get-value",
    "include",
];

/// The leading symbol of a top-level command source, e.g. `get-model` for
/// `(get-model)`. `None` when the text does not open with `(` followed by a
/// symbol — every such case is treated as demand by the caller.
fn command_head_symbol(text: &str) -> Option<&str> {
    let after_paren = text.strip_prefix('(')?.trim_start();
    // A QUOTED head is the same command. `|get-model|` is SMT-LIB quoting, not
    // part of the name, and AY's parser normalizes the bars away before
    // dispatch — so AY really does execute `(|get-model|)` and print a model,
    // as does z3. Comparing the raw head against unquoted spellings answered
    // "no reader" for a command that consumes one. Verdict-safe (the model is
    // still built, validated and gate-checked; only the cosmetic polish was
    // skipped) but it contradicts this function's contract.
    //
    // Stripped as a PAIR: a lone `|` opens a quoted symbol the chunker only
    // closes at the matching bar, so a head keeping exactly one bar is not a
    // symbol at all. Returning `None` there makes the lookup miss, which the
    // caller already treats as demand.
    if let Some(rest) = after_paren.strip_prefix('|') {
        let end = rest.find('|')?;
        return (end > 0).then(|| &rest[..end]);
    }
    let end = after_paren
        .find(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .unwrap_or(after_paren.len());
    let head = &after_paren[..end];
    (!head.is_empty()).then_some(head)
}

/// Whether any command in this script could read a model.
///
/// Reads the ALREADY-CHUNKED command list rather than rescanning the source.
/// This matters: an earlier revision matched each of the eight names against
/// the raw text with a sliding window, i.e. eight extra passes over the whole
/// file. On `incremental/QF_LRA/hybrid_networks/fisher_star_20_3` — 198 MB,
/// 202 `(check-sat)` — that scan cost 3.7s on top of a 0.9s solve, a 5x
/// REGRESSION that swamped everything the gate saves. `collect_command_sources`
/// already walks the input exactly once (comment-, string- and
/// quoted-symbol-aware) before the command loop starts, so consulting its
/// output is free.
///
/// Still conservative in the direction that matters: a command whose head
/// symbol cannot be read counts as demand. Over-approximating costs a little
/// wasted witness polish; under-approximating would silently drop the polish
/// from a model someone then prints.
///
/// An UNTERMINATED trailing form is absent from `sources` — the chunker only
/// emits a command when its parens close. That is not a hole, because the
/// executor never sees such a form either: `CommandStream` cannot parse an
/// unclosed s-expression into a command, so it can never run. Pinned by
/// `unterminated_trailing_get_model_never_runs`.
///
/// Soundness of the NEGATIVE answer rests on one fact: an SMT-LIB command name
/// is literal source text. There is no macro, no runtime construction of a
/// command, and no `include` AY honors — the spelling is in the list above
/// precisely so a script mentioning it is never shed.
fn commands_may_consume_a_model(sources: &[CommandSource]) -> bool {
    sources.iter().any(|source| {
        command_head_symbol(&source.text).is_none_or(|head| MODEL_READING_COMMANDS.contains(&head))
    })
}
