// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{sat_result, Executor};
use ay_frontend::parse;

/// Regression (#str-replace-authority): `str.replace` combined with a
/// regex-membership constraint must not panic the proof-authority ledger.
///
/// This reduces the SMT-COMP QF_S 2019-Jiang slog cases. Proof-enabled pass
/// escalation rebuilds the SLIA SAT solver, which restarts original-clause IDs.
/// Each rebuild must therefore clear the proof ledgers indexed by those IDs.
/// z3 5.0.0 answers `sat`; `unknown` remains a sound incomplete verdict.
#[test]
fn test_str_replace_regex_authority_no_panic_slog_1622_reduced() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x_4 () String)
(declare-fun x_9 () String)
(declare-fun sigmaStar_12 () String)
(declare-fun x_16 () String)
(assert (= x_9 (str.replace x_4 "/.(\u{5c}d+)./" "_$1.")))
(assert (= x_16 (str.++ "    " sigmaStar_12)))
(assert (str.in_re x_16 (re.++ (re.* re.allchar) (re.++ (str.to_re "\u{5c}<SCRIPT") (re.* re.allchar)))))
(check-sat)
"#;
    let commands = parse(smt).expect("parse failed");
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let outputs = exec.execute_all(&commands).expect("execute_all failed");
    let result = outputs.join("\n");
    let verdict = sat_result(&result);
    assert!(
        matches!(verdict, Some("sat") | Some("unknown")),
        "str.replace + regex must return sat or unknown, never panic or claim \
         unsat against z3 5.0.0; got: {result}"
    );
}
