// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One macro body bridge per authored `assume` bridge, however often the
//! macro occurs in it.
//!
//! AY's frontend expands a nullary macro at every use, so each occurrence of
//! `saved` in `(concat (select saved i) (select saved j))` is the SAME
//! canonical subterm, and its definition leaf needs the same equality
//! `(= body canonical)` each time. Derived again at every occurrence, the
//! bridge grew with the TREE expansion of the macro DAG and spent the
//! per-bridge node allowance on repeats. MEASURED at 4373bc24b on the
//! source-bound frame macros (`saved` a 16-store chain over
//! `frame` = `(bvsub sp (_ bv16 64))`) read by an N-byte `concat` of
//! `(select saved (bvadd frame (_ bvK 64)))` under `distinct`: N = 4 planned
//! in 218 of the 256 nodes and published carcara `valid`; N = 5 needed 263,
//! the definition schema declined, and the query published the expanded
//! `assume` under `foreign_assumes=yes`, which pinned carcara 1.1.0 refused
//! ("could not match term to any of the original problem premises").
//!
//! A later occurrence therefore still `assume`s its own definition premise,
//! but joins it by `trans` to the body step the bridge ALREADY emitted. The
//! allowance is unchanged and every visited node is still charged; only the
//! re-derivation is gone. The cited line is looked up in the bridge's own
//! `output` by its exact conclusion text, so it is present when cited (an
//! abandoned attempt truncates its lines, and with them every later line that
//! could cite them) and concludes byte for byte the equality `trans` needs.

/// The id of the first `(step ID (cl (= {left} {right})) :rule ..)` line of
/// `output`, or `None`. Declines outright once `output` opens a subproof,
/// whose steps are out of scope after it closes (no bridge emits one today).
pub(super) fn earlier_equality_step(output: &[String], left: &str, right: &str) -> Option<String> {
    if output.iter().any(|line| line.starts_with("(anchor ")) {
        return None;
    }
    output.iter().find_map(|line| {
        let (id, conclusion) = line.strip_prefix("(step ")?.split_once(' ')?;
        conclusion
            .strip_prefix("(cl (= ")?
            .strip_prefix(left)?
            .strip_prefix(' ')?
            .strip_prefix(right)?
            .starts_with(")) :rule ")
            .then(|| id.to_string())
    })
}
