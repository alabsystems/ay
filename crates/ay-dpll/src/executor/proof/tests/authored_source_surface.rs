// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The certificate's surface verdict covers the AUTHORED problem, not only
//! AY's elaborated signature and the proof.
//!
//! `benchmarks/smt/model_checker_consumer_quantified_counterexample/typed_vec_pins_cell64_unsat.smt2`
//! writes `((as mkVec Vec) ...)`. Pinned Carcara 9a352ee stops parsing that
//! problem (`not a valid qualified operator: 'mkVec'`), yet AY 938ec0327
//! disclosed `carcara_surface=supported`: the qualification is gone once AY
//! elaborates the term, and the verdict read only the elaborated signature.
//! Each fixture here refutes on two integer bounds, so its proof never
//! mentions the authored construct and is inside Carcara's grammar on its own.

use super::*;
use ay_proof::CarcaraSurface;

const QUALIFIED_CONSTRUCTOR_BESIDE_INT_REFUTATION: &str = "(set-logic ALL)
(declare-datatype E ((A) (B)))
(declare-const e E)
(declare-const x Int)
(assert (= e (as A E)))
(assert (> x 0))
(assert (< x 0))
(check-sat)
";

/// Positive control: the same problem with the constructor unqualified, which
/// pinned Carcara parses.
const PLAIN_CONSTRUCTOR_BESIDE_INT_REFUTATION: &str = "(set-logic ALL)
(declare-datatype E ((A) (B)))
(declare-const e E)
(declare-const x Int)
(assert (= e A))
(assert (> x 0))
(assert (< x 0))
(check-sat)
";

fn solve(options: &str, script: &str) -> (Executor, Vec<String>) {
    let commands = parse(&format!("{options}{script}")).expect("fixture parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("fixture solves");
    (exec, outputs)
}

fn names(surface: Option<&CarcaraSurface>, fragment: &str) -> bool {
    surface
        .and_then(CarcaraSurface::unsupported_reason)
        .is_some_and(|reason| reason.contains(fragment))
}

/// The verdict the CLI discloses beside the certificate it streams.
fn streamed(exec: &Executor) -> Option<CarcaraSurface> {
    exec.try_export_last_proof_alethe_for_problem_scope_to_with_carcara_surface(&mut Vec::new())
        .and_then(Result::ok)
}

#[test]
fn a_qualified_constructor_in_the_problem_is_disclosed_on_every_surface_reader() {
    let (exec, outputs) = solve(
        "(set-option :produce-proofs true)\n",
        QUALIFIED_CONSTRUCTOR_BESIDE_INT_REFUTATION,
    );
    assert_eq!(outputs, vec!["unsat"]);

    // Witness: the proof alone, and the elaborated signature, are inside the
    // grammar; only the authored spelling is not.
    let proof = exec.last_proof().expect("retained UNSAT proof");
    assert_eq!(
        ay_proof::carcara_proof_surface(
            proof,
            &exec.ctx.terms,
            exec.last_proof_term_overrides.as_ref()
        ),
        CarcaraSurface::Supported
    );

    let gate = exec.strict_gate_carcara_surface();
    assert!(names(gate.as_ref(), "(as A E)"), "gate surface: {gate:?}");
    let public = exec.last_unsat_proof_carcara_surface();
    assert!(
        names(public.as_ref(), "(as A E)"),
        "public surface: {public:?}"
    );
    let artifact = exec.carcara_surface_for_last_export(false);
    assert!(
        names(artifact.as_ref(), "(as A E)"),
        "artifact surface: {artifact:?}"
    );
    let paired = exec
        .try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()
        .and_then(Result::ok)
        .map(|(_, surface)| surface);
    assert!(
        names(paired.as_ref(), "(as A E)"),
        "paired surface: {paired:?}"
    );
    let streamed = streamed(&exec);
    assert!(
        names(streamed.as_ref(), "(as A E)"),
        "streamed surface: {streamed:?}"
    );
}

#[test]
fn an_unqualified_constructor_keeps_the_surface_supported() {
    let (exec, outputs) = solve(
        "(set-option :produce-proofs true)\n",
        PLAIN_CONSTRUCTOR_BESIDE_INT_REFUTATION,
    );
    assert_eq!(outputs, vec!["unsat"]);
    assert_eq!(
        exec.last_unsat_proof_carcara_surface(),
        Some(CarcaraSurface::Supported)
    );
    assert_eq!(
        exec.carcara_surface_for_last_export(false),
        Some(CarcaraSurface::Supported)
    );
}

/// Strict proofs claim an external check, so they withhold an `unsat` whose
/// problem pinned Carcara cannot parse (owner decision D7); the unqualified
/// twin still publishes.
#[test]
fn strict_proofs_withhold_unsat_on_a_problem_carcara_cannot_parse() {
    let strict = "(set-option :produce-proofs true)\n(set-option :check-proofs-strict true)\n";
    let (_, outputs) = solve(strict, QUALIFIED_CONSTRUCTOR_BESIDE_INT_REFUTATION);
    assert_eq!(outputs, vec!["unknown"]);
    let (_, outputs) = solve(strict, PLAIN_CONSTRUCTOR_BESIDE_INT_REFUTATION);
    assert_eq!(outputs, vec!["unsat"]);
}

/// The native BV/LIA bundle class is no exception: `:check-proofs-strict`
/// claims an external check (owner decision D7), so the query spelled with
/// `bv2nat`, which pinned Carcara does not define, is withheld with that
/// reason, while its `ubv_to_int` twin, which AY elaborates to the same term,
/// publishes.
#[test]
fn strict_proofs_withhold_the_bv2nat_spelling_of_a_native_bundle_refutation() {
    let script = |conversion: &str| {
        format!(
            "(set-logic QF_UFBVLIA)
(declare-const result (_ BitVec 16))
(declare-const x (_ BitVec 16))
(assert (= x #x9c40))
(assert (= x result))
(assert (<= (* ({conversion} x) 2) 65535))
(check-sat)
"
        )
    };
    let strict = "(set-option :produce-proofs true)\n(set-option :check-proofs-strict true)\n";
    let (exec, outputs) = solve(strict, &script("bv2nat"));
    assert_eq!(outputs, vec!["unknown"]);
    let detail = exec.unknown_detail().unwrap_or_default();
    assert!(detail.contains("`bv2nat`"), "{detail}");
    let (_, outputs) = solve(strict, &script("ubv_to_int"));
    assert_eq!(outputs, vec!["unsat"]);
}

/// Carcara reads the whole authored file, a `(reset)` included, so a gap
/// before it still applies to the certificate of a later query; a library
/// caller's `(reset)` starts a fresh problem.
#[test]
fn an_authored_reset_keeps_the_gap_and_a_generic_reset_clears_it() {
    let script = "(set-option :produce-proofs true)
(set-logic ALL)
(declare-const y Int)
(assert (= (as y Int) 1))
(reset)
(set-option :produce-proofs true)
(set-logic ALL)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
";
    let commands = parse(script).expect("fixture parses");
    let mut authored = Executor::new();
    let mut outputs = Vec::new();
    for command in &commands {
        outputs.extend(
            authored
                .execute_authored(command)
                .expect("authored command"),
        );
    }
    assert_eq!(outputs, vec!["unsat"]);
    let surface = authored.last_unsat_proof_carcara_surface();
    assert!(
        names(surface.as_ref(), "(as y Int)"),
        "authored: {surface:?}"
    );
    let surface = streamed(&authored);
    assert!(
        names(surface.as_ref(), "(as y Int)"),
        "authored, streamed: {surface:?}"
    );

    let mut generic = Executor::new();
    assert_eq!(
        generic.execute_all(&commands).expect("generic commands"),
        vec!["unsat"]
    );
    assert_eq!(
        generic.last_unsat_proof_carcara_surface(),
        Some(CarcaraSurface::Supported)
    );
    assert_eq!(streamed(&generic), Some(CarcaraSurface::Supported));
}

/// The CLI hands each command's source text over: AY reads `define-const` as
/// a `define-fun`, which pinned Carcara parses, but Carcara skips the
/// `define-const` command itself (`identifier 'c' is not defined`).
#[test]
fn a_command_spelling_only_the_source_shows_is_disclosed() {
    let script = "(set-option :produce-proofs true)
(set-logic ALL)
(define-const c Int 1)
(declare-const x Int)
(assert (> x c))
(assert (< x 0))
(check-sat)
";
    let mut exec = Executor::new();
    let mut stream = ay_frontend::CommandStream::new(script);
    let mut outputs = Vec::new();
    loop {
        let start = stream.position();
        let Some(ay_frontend::CommandStreamItem::Command(command)) = stream.next_command() else {
            break;
        };
        exec.observe_authored_command_source(&script[start..stream.position()]);
        outputs.extend(exec.execute_authored(&command).expect("authored command"));
    }
    assert_eq!(outputs, vec!["unsat"]);
    let surface = exec.last_unsat_proof_carcara_surface();
    assert!(
        names(surface.as_ref(), "`define-const`"),
        "surface: {surface:?}"
    );
    let surface = streamed(&exec);
    assert!(
        names(surface.as_ref(), "`define-const`"),
        "streamed: {surface:?}"
    );
}

/// Review probe b01: strict proofs decide at the `check-sat`, before the
/// `FloatingPoint` declaration after it runs, and Carcara parses the whole
/// file. The CLI's file mode hands the rest of the file over first
/// (`observe_authored_commands_ahead`), so that `unsat` is withheld with the
/// reason; a tail Carcara parses still publishes.
#[test]
fn strict_proofs_read_the_commands_after_the_deciding_query() {
    let decide = |tail: &str| {
        let script = format!(
            "(set-option :produce-proofs true)
(set-option :check-proofs-strict true)
(set-logic ALL)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
{tail}"
        );
        let mut exec = Executor::new();
        let mut stream = ay_frontend::CommandStream::new(&script);
        loop {
            let start = stream.position();
            let Some(ay_frontend::CommandStreamItem::Command(command)) = stream.next_command()
            else {
                panic!("the script reaches its check-sat");
            };
            let query = matches!(*command, Command::CheckSat);
            if query {
                exec.observe_authored_commands_ahead(&script[start..]);
            }
            exec.observe_authored_command_source(&script[start..stream.position()]);
            let output = exec.execute_authored(&command).expect("authored command");
            if query {
                let detail = exec.unknown_detail().map(str::to_string);
                return (output, detail.unwrap_or_default());
            }
        }
    };
    let (output, detail) = decide("(declare-const f (_ FloatingPoint 8 24))\n");
    assert_eq!(output.as_deref(), Some("unknown"));
    assert!(detail.contains("FloatingPoint"), "{detail}");
    let (output, _) = decide("(declare-const y Int)\n(exit)\n");
    assert_eq!(output.as_deref(), Some("unsat"));
}

/// PRECEDENCE on the library's paired export: its verdict carries the render's
/// dialect report, so a document that keeps a Clean-only spelling is
/// `CleanDialect`. An authored problem pinned Carcara cannot parse is
/// `Unsupported` all the same, naming the construct, although the document
/// still keeps that spelling: the checker stops at the problem first. The
/// CLI's streamed verdict agrees on both.
#[test]
fn an_unparseable_problem_outranks_a_clean_only_spelling_on_the_paired_export() {
    const ASHR: &str = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
        (assert (not (= (bvashr x #x03) ((_ sign_extend 3) ((_ extract 7 3) x)))))\n";
    let paired = |extra: &str| {
        let script = format!("{ASHR}{extra}(check-sat)\n");
        let (exec, outputs) = solve("(set-option :produce-proofs true)\n", &script);
        assert_eq!(outputs, vec!["unsat"], "{extra}");
        let (document, surface) = exec
            .try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()
            .and_then(Result::ok)
            .unwrap_or_else(|| panic!("{extra}: the paired export renders"));
        (document, surface, streamed(&exec))
    };
    let (document, surface, streamed) = paired("");
    assert!(document.contains(":rule bitblast_ashr"), "{document}");
    assert!(
        matches!(surface, CarcaraSurface::CleanDialect { .. }),
        "{surface:?}"
    );
    assert_eq!(streamed, Some(surface));
    let (document, surface, streamed) = paired("(assert (= x (as x (_ BitVec 8))))\n");
    assert!(document.contains(":rule bitblast_ashr"), "{document}");
    assert!(names(Some(&surface), "(as x (_ BitVec 8))"), "{surface:?}");
    assert_eq!(streamed, Some(surface));
}
