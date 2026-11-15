// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

// Textually included by `elaborate::tests::finite_sets_z3_500` to preserve test FQNs.

/// One assertion of `depth` nested `let`s over plain Int terms, the shape of
/// `QF_UFIDL/UCLID-pred/ibm_cache_full7` (554 nested `let`s, one assertion,
/// no set anywhere), which the strict retention-shape scan used to walk in
/// `O(n · d²)` — past a 12 s deadline in `--z3-mode` while the default
/// posture decided it in 0.4 s.
fn nested_let_assertion(depth: usize, leaf: &str) -> String {
    let mut script = String::from("(declare-const x Int) (declare-const y Int) (assert ");
    for i in 0..depth {
        script.push_str(&format!("(let ((v{i} (+ x {i}))) (and (< v{i} y) "));
    }
    script.push_str(leaf);
    for _ in 0..depth {
        script.push_str("))");
    }
    script.push_str(")");
    script
}

/// Elaborate `script` under `Z3_5Strict` on a worker thread, or `None` if the
/// retention-shape scan has not finished within `bound`.
///
/// The bound each caller passes is generous on purpose: a linear scan of 1,500
/// nested `let`s takes well under a second even unoptimised, and the pre-memo
/// cost at this depth was measured in minutes, so these tests cannot pass by
/// machine luck. The unwrapping is left to the `#[test]` functions: free
/// helpers in this `include!` reach are scanned as production code by the
/// construct gate, and nothing under it carries a production construct site.
fn elaborate_strict_within(script: String, bound: std::time::Duration) -> Option<Result<Context>> {
    let (send, recv) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let _ = send.send(elaborate_strict(&script));
    });
    recv.recv_timeout(bound).ok()
}

/// What every caller says when `elaborate_strict_within` times out.
const SCAN_OVERRAN: &str = "strict retention-shape scan did not finish within its bound";

#[test]
fn z3_500_strict_retention_scan_is_linear_in_nested_let_depth() {
    let script = nested_let_assertion(1_500, "(> x 0)");
    let strict = elaborate_strict_within(script.clone(), std::time::Duration::from_secs(20))
        .expect(SCAN_OVERRAN)
        .expect("plain-logic nested lets pass the strict retention-shape check");
    let legacy = elaborate(&script);
    assert_eq!(strict.assertion_finite_set_metadata().len(), 1);
    assert_eq!(
        strict.assertion_finite_set_metadata().len(),
        legacy.assertion_finite_set_metadata().len()
    );
    assert!(
        !strict.assertion_finite_set_metadata()[0]
            .finite_sets
            .uses_finite_set
    );
    assert!(strict.assertion_finite_set_metadata()[0].root.is_none());
}

#[test]
fn z3_500_strict_retention_check_still_fires_under_deep_lets() {
    // The memo must not turn a rejection into an acceptance: an occurrence at
    // the very bottom of the chain is still a `let` whose FiniteSet identity
    // cannot be retained, and the diagnostic names the `let`.
    for leaf in [
        "(set.in x s)",
        "(= (let ((t s)) t) s)",
        "(forall ((z Int)) (set.in z s))",
    ] {
        let script = format!(
            "(declare-const s (FiniteSet Int)) {}",
            nested_let_assertion(300, leaf)
        );
        let error = elaborate_strict_within(script, std::time::Duration::from_secs(20))
            .expect(SCAN_OVERRAN)
            .err()
            .expect("a FiniteSet occurrence under a `let` fails closed");
        assert!(
            error
                .to_string()
                .contains("Z3 5.0.0 FiniteSet public AST retention for let is not yet available"),
            "unexpected diagnostic for leaf {leaf}: {error}"
        );
    }
    // A set used outside any `let`/binder after the deep chain still keeps
    // its public identity: the scan of the first assertion must leave nothing
    // behind that changes the second.
    let script = format!(
        "(declare-const s (FiniteSet Int)) {} (assert (set.in x s))",
        nested_let_assertion(300, "(> x 0)")
    );
    let strict = elaborate_strict_within(script, std::time::Duration::from_secs(20))
        .expect(SCAN_OVERRAN)
        .expect("a set occurrence with no let/binder is retained");
    assert_eq!(strict.assertion_finite_set_metadata().len(), 2);
    assert!(strict.assertion_finite_set_metadata()[0].root.is_none());
    assert!(
        strict.assertion_finite_set_metadata()[1]
            .finite_sets
            .uses_finite_set
    );
    assert!(strict.assertion_finite_set_metadata()[1].root.is_some());
}

/// One assertion whose `let`s nest in BODY position — `(let ((v0 ..)) (let
/// ((v1 ..)) ..))`, the Tseitin/CSE printer shape of
/// `QF_LRA/hybrid_networks/*.inter.{bmc,ind}_k100` (8,550 levels) — with
/// `outer` (an open `let` prefix, or empty) wrapped around the chain and
/// `leaf` as the chain's final body.
fn body_position_let_chain(depth: usize, outer: &str, leaf: &str) -> String {
    let mut script = String::from("(declare-const x Int) (declare-const y Int) (assert ");
    script.push_str(outer);
    for i in 0..depth {
        let previous = if i == 0 {
            "x".to_string()
        } else {
            format!("v{}", i - 1)
        };
        script.push_str(&format!("(let ((v{i} (+ {previous} 1))) "));
    }
    script.push_str(leaf);
    script.push_str(&")".repeat(depth));
    if !outer.is_empty() {
        script.push(')');
    }
    script.push(')');
    script
}

#[test]
fn z3_500_public_sorts_accept_deep_body_position_let_chains_in_both_postures() {
    // The public-sort pass (every posture) and the strict retention-shape
    // scan (`--z3-mode`) cloned their binder environment once per level and
    // held every clone down the recursion: O(d²) memory, 4.2 GB RSS for 8,000
    // levels. They now walk the chain under one environment; the memory
    // bound itself is pinned end to end by the CLI test
    // `group_lra::deep_let_chain_memory` (a 256 MB `--memory` budget). This
    // pins that the chain walk decides a deep plain chain identically in both
    // postures and leaves no FiniteSet provenance behind.
    let script = body_position_let_chain(5_000, "", "(< v4999 y)");
    let strict = elaborate_strict_within(script.clone(), std::time::Duration::from_secs(60))
        .expect(SCAN_OVERRAN)
        .expect("a plain body-position let chain passes the strict retention-shape check");
    let legacy = elaborate(&script);
    for context in [&strict, &legacy] {
        let metadata = context.assertion_finite_set_metadata();
        assert_eq!(metadata.len(), 1);
        assert!(!metadata[0].finite_sets.uses_finite_set);
        assert!(metadata[0].root.is_none());
    }
}

#[test]
fn z3_500_body_position_let_chains_keep_finite_set_provenance_and_rejections() {
    // A set bound ABOVE a deep chain and used at its bottom is still a set
    // occurrence: legacy metadata records it, strict posture rejects the
    // `let` that would erase its public identity.
    let script = format!(
        "(declare-const s (FiniteSet Int)) {}",
        body_position_let_chain(2_000, "(let ((t s)) ", "(set.in v1999 t)")
    );
    let legacy = elaborate(&script);
    assert!(
        legacy.assertion_finite_set_metadata()[0]
            .finite_sets
            .uses_finite_set
    );
    let error = elaborate_strict_within(script, std::time::Duration::from_secs(60))
        .expect(SCAN_OVERRAN)
        .err()
        .expect("a FiniteSet occurrence under a body-position let chain fails closed");
    assert!(
        error
            .to_string()
            .contains("Z3 5.0.0 FiniteSet public AST retention for let is not yet available"),
        "unexpected diagnostic: {error}"
    );
    // A set occurrence ONLY at the bottom of the chain is found too.
    let script = format!(
        "(declare-const s (FiniteSet Int)) {}",
        body_position_let_chain(2_000, "", "(set.in v1999 s)")
    );
    let error = elaborate_strict_within(script, std::time::Duration::from_secs(60))
        .expect(SCAN_OVERRAN)
        .err()
        .expect("a FiniteSet occurrence at the chain's bottom fails closed");
    assert!(error.to_string().contains("retention for let"), "{error}");
}

#[test]
fn z3_500_public_sorts_bind_each_chained_let_level_in_parallel() {
    // `let` binds in parallel: a sibling reference resolves OUTWARD. Walking
    // a chain level by level under one environment must keep that: `b` below
    // is the OUTER `a` (a set, so `set.in` is well sorted) ...
    let accepted = elaborate(
        "(declare-const s (FiniteSet Int)) \
         (assert (let ((a s)) (let ((a 0) (b a)) (let ((c 1)) (set.in c b)))))",
    );
    assert!(
        accepted.assertion_finite_set_metadata()[0]
            .finite_sets
            .uses_finite_set
    );
    // ... and here `b` is the outer Int `a`, so `set.in` is ill sorted.
    let commands = parse(
        "(declare-const s (FiniteSet Int)) \
         (assert (let ((a 0)) (let ((a s) (b a)) (let ((c 1)) (set.in c b)))))",
    )
    .expect("parallel-let script parses");
    let mut context = Context::new();
    let rejected = commands
        .iter()
        .try_for_each(|command| context.process_command(command).map(|_| ()));
    assert!(
        rejected.is_err(),
        "an Int bound in parallel beside a set must not type as that set"
    );
}
