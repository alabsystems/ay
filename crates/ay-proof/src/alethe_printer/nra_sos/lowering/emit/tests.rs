// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn rows(literals: &[&str]) -> Vec<(String, BigRational)> {
    literals
        .iter()
        .map(|literal| (literal.to_string(), BigRational::one()))
        .collect()
}

/// NEGATIVE TWIN of the real-contradiction guard: pinned carcara accepts
/// `(cl (not (> x 0.0)) (not (< x 1.0))) :args (1 1)` (measured: `valid`
/// against the SATISFIABLE `0 < x < 1`), only because its `la_generic`
/// strengthens `Real` rows as if they were integral. The emitter writes
/// nothing for it; the real theorem beside it is written.
#[test]
fn a_step_only_integer_strengthening_accepts_is_never_written() {
    let strengthened = ["(not (> x 0.0))", "(not (< x 1.0))"];
    assert!(printed_la_generic_holds(&strengthened, &["1", "1"]));
    let mut emitter = Emitter::new("t0.sos".to_string(), true);
    assert!(emitter.la_generic(rows(&strengthened)).is_none());
    assert!(emitter.finish().is_empty());

    let mut emitter = Emitter::new("t0.sos".to_string(), true);
    let written = emitter
        .la_generic(rows(&["(not (> x 0.0))", "(not (< x 0.0))"]))
        .expect("a real contradiction is written");
    assert_eq!(written.name, "t0.sos.g0");
    assert_eq!(
        emitter.finish(),
        "(step t0.sos.g0 (cl (not (> x 0.0)) (not (< x 0.0))) :rule la_generic :args (1 1))\n"
    );
}
