// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_dpll::Executor;
use ay_frontend::parse;

fn publish_original(name: &str, input: &str) {
    let query = input.trim_end().strip_suffix("(exit)").unwrap();
    let commands = parse(&format!("{query}(get-proof)\n")).unwrap();
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let outputs = executor.execute_all(&commands).unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    let proof = outputs.get(1).expect("published proof");
    assert!(proof.contains(":rule poly_simp"), "{proof}");
    assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
    let path = std::env::temp_dir().join(format!(
        "ay-affine-original-{name}-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":input,"proof":proof})).unwrap()).unwrap();
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn original_subtractor_relocation_has_a_checked_source_proof() {
    publish_original(
        "subtractor",
        include_str!("fixtures/affine_subtractor.smt2"),
    );
}

#[test]
fn original_page_cancellation_has_a_checked_source_proof() {
    publish_original("page", include_str!("fixtures/affine_page.smt2"));
}

#[test]
fn original_section_rebase_has_a_checked_source_proof() {
    publish_original("section", include_str!("fixtures/affine_section.smt2"));
}

#[test]
fn changed_subtraction_sign_is_refuted() {
    let input = include_str!("fixtures/affine_subtractor.smt2")
        .replace("(bvsub ADDEND B)", "(bvadd ADDEND B)");
    assert_ne!(input, include_str!("fixtures/affine_subtractor.smt2"));
    let mut executor = Executor::new();
    let outputs = executor.execute_all(&parse(&input).unwrap()).unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
}

/// ExternalCodegen's Faulhaber step (`ay` `group_bv::bv_performance_diagnostic`):
/// sums of 64-bit operands with small constant multipliers. Carcara's
/// `poly_simp` distributes `bvmul` over a constant; while the affine checker
/// kept such a product opaque, no lane could state this identity and the
/// certificate carried a trust step.
#[test]
fn original_constant_multiples_have_a_checked_source_proof() {
    publish_original(
        "constant-multiples",
        include_str!("fixtures/affine_constant_multiples.smt2"),
    );
}

/// The CLI's stdin posture retains no parsed surface and prints no proof, so
/// only elaboration's shift/add form of the multipliers exists. The verdict
/// must still stand on a checked theorem: before, every lane re-ran a
/// bit-blast that exhausted its three-second deadline on this reassociated
/// adder network, and only the deferred-trust fallback (a fresh re-solve)
/// admitted the answer, twelve seconds later.
#[test]
fn elaborated_constant_multiples_certify_without_a_parsed_surface() {
    let input = include_str!("fixtures/affine_constant_multiples.smt2");
    let mut executor = Executor::new();
    executor.set_retain_parsed_assertions(false);
    let outputs = executor.execute_all(&parse(input).unwrap()).unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    assert_eq!(
        executor.last_command_unsat_admission_tag(),
        Some("strict-proof")
    );
}

/// The same elaborated identity where a hole-free document is owed: under a
/// bare self-check and under `:check-proofs-strict`, the wire-gap screen asks
/// the complete bit-blast, which cannot lower this 64-bit identity in time.
/// That question polls the query's own stop: it used to run the sweep's
/// 120 s wall and then a monolithic refutation that polled nothing, past
/// 100 s on a 20 s timeout. `unknown` is an honest answer here; a hang is
/// not. The bound is twenty times the timeout, for a loaded host.
#[test]
fn elaborated_constant_multiples_honour_the_timeout_where_a_document_is_owed() {
    let input = include_str!("fixtures/affine_constant_multiples.smt2");
    let timeout = std::time::Duration::from_secs(3);
    for strict in [false, true] {
        let mut executor = Executor::new();
        executor.set_retain_parsed_assertions(false);
        executor.set_timeout(Some(timeout));
        let script = if strict {
            format!("(set-option :check-proofs-strict true)\n{input}")
        } else {
            executor.set_self_check(true);
            input.to_string()
        };
        let start = std::time::Instant::now();
        let outputs = executor.execute_all(&parse(&script).unwrap()).unwrap();
        let elapsed = start.elapsed();
        let verdict = outputs.first().map(String::as_str);
        assert!(
            matches!(verdict, Some("unsat" | "unknown")),
            "strict={strict}: {outputs:?}"
        );
        if verdict == Some("unsat") {
            assert_eq!(
                executor.last_command_unsat_admission_tag(),
                Some("strict-proof"),
                "strict={strict}"
            );
        }
        assert!(
            elapsed < timeout * 20,
            "strict={strict}: answered {verdict:?} after {elapsed:?} on a {timeout:?} timeout"
        );
    }
}

#[test]
fn changed_constant_multiplier_is_refuted() {
    let original = include_str!("fixtures/affine_constant_multiples.smt2");
    let input = original.replace("(bvmul (_ bv5 64) a2)", "(bvmul (_ bv6 64) a2)");
    assert_ne!(input, original);
    let mut executor = Executor::new();
    let outputs = executor.execute_all(&parse(&input).unwrap()).unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
}

/// Carcara's `poly_simp` keeps a monomial whose coefficient wraps to zero, so
/// `x + x = 0` over one bit is not a `poly_simp` theorem there (carcara 1.1.0
/// reports `invalid`). AY used to print exactly that step and call the
/// certificate checkable; the identity must take a lowering that replays.
#[test]
fn a_wrapping_coefficient_is_not_printed_as_poly_simp() {
    let commands = parse(
        "(set-logic QF_BV)(declare-const x (_ BitVec 1))\
         (assert (not (= (bvadd x x) #b0)))(check-sat)(get-proof)\n",
    )
    .unwrap();
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let outputs = executor.execute_all(&commands).unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    let proof = outputs.get(1).expect("published proof");
    assert!(!proof.contains(":rule poly_simp"), "{proof}");
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "the identity must take a lowering that replays, not a gap: {proof}"
    );
}
