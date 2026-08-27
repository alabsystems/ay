// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `run` to preserve private CLI item and test DefPaths.

// SMT-LIB 2.6 standard options. All 14 verified accepted by the oracle.
const SMTLIB_OPTIONS: &[&str] = &[
    "diagnostic-output-channel",
    "global-declarations",
    "interactive-mode",
    "print-success",
    "produce-assertions",
    "produce-assignments",
    "produce-models",
    "produce-proofs",
    "produce-unsat-assumptions",
    "produce-unsat-cores",
    "random-seed",
    "regular-output-channel",
    "reproducible-resource-limit",
    "verbosity",
];

// Options z3 accepts that are neither SMT-LIB standard names nor global
// parameters, so neither lookup below finds them. Each is dispatched by AY's
// own `set-option` handling (`keyword_key(keyword) == ...` arms, and
// `is_global_decls_option` for the `global-decls` alias), and each was measured
// accepted by the oracle. Reporting them unknown REJECTED VALID OPTIONS --
// `:global-decls` is z3's own alias for `:global-declarations`, and rejecting
// it broke global-declaration scope semantics outright.
const DISPATCHED_OPTIONS: &[&str] = &[
    "error-behavior",
    "global-decls",
    "int-real-coercions",
    "print-warning",
];

// AY's OWN options -- keys z3 has never had, that AY reads back through
// `Context::get_option` inside the executor. The two lists above are the z3
// surface; this one is the AY surface, and it is deliberately NOT a conformance
// claim: z3 rejects every key here.
//
// They were rejected as unknown until 2026-08-20, which meant the CLI PRINTED
// an error and RETURNED BEFORE `executor.execute_authored(cmd)` -- so the key
// never reached `ctx.options` and every reader fell back to its default. Every
// AY-specific option was therefore dead through the binary while working
// through the library API (which is why the in-crate
// `:minimize-counterexamples` regressions all pass). Measured on
// ABVFPLRA/inv_Newton: `(set-option :minimize-counterexamples false)` left
// `minimize_model_sat_preserving` running and the wall clock unchanged, and
// run.rs's own comment about a script enabling strict proofs with `(set-option
// :check-proofs-strict true)` described something the binary could not do.
//
// Divergence accepted knowingly: a script written for z3 cannot contain these
// keys, so accepting them changes no z3-authored transcript, whereas rejecting
// them makes AY ignore options AY itself documents. An unknown key that is
// neither z3's nor AY's still reports exactly as before.
const NATIVE_OPTIONS: &[&str] = &[
    "ay-diff-logic",
    "ay-eq-diffvar",
    "ay-maxsmt-engine",
    "ay-proof-no-varsubst",
    "ay-unit-prop",
    "check-proofs-strict",
    "minimize-counterexamples",
];

fn z3_unknown_module_option_error(
    state: &SmtTranscriptState,
    keyword: &str,
    module: &str,
    parameter: &str,
) -> Option<String> {
    let module = module.replace('-', "_").to_ascii_lowercase();
    let parameter = parameter.replace('-', "_").to_ascii_lowercase();

    if !crate::z3_parameter_help::is_known_module(&module) {
        return Some(set_option_error(
            state,
            keyword,
            &format!("invalid parameter, unknown module '{module}'"),
        ));
    }
    if crate::z3_parameter_help::is_known_module_parameter(&module, &parameter) {
        return None;
    }

    let mut body = String::new();
    body.push_str(&format!(
        "unknown parameter '{parameter}' at module '{module}'\nLegal parameters are:"
    ));
    for line in crate::z3_parameter_help::legal_module_parameter_report_lines(&module)
        .expect("module was just verified known")
    {
        body.push('\n');
        body.push_str(&line);
    }
    Some(set_option_error(state, keyword, &body))
}
