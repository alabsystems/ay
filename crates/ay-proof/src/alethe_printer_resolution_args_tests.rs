// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::{
    try_export_alethe, try_export_alethe_with_problem_scope_and_overrides,
    try_export_alethe_with_problem_scope_overrides_and_budget, AlethePrintError,
};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, Sort, Symbol, TermId, TermStore};

#[test]
fn generic_resolution_export_rejects_malformed_argument_count() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let h1 = proof.add_assume(x, None);
        let h2 = proof.add_assume(not_x, None);
        proof.add_rule_step(rule, Vec::new(), vec![h1, h2], vec![x]);

        let error = try_export_alethe(&proof, &terms)
            .expect_err("one pivot without its polarity must fail closed");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("requires 2 pivot/polarity arguments, found 1")
            ),
            "{error}"
        );
    }
}

#[test]
fn generic_resolution_export_rejects_non_boolean_polarity() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);
    let one = terms.mk_int(1.into());

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let h1 = proof.add_assume(x, None);
        let h2 = proof.add_assume(not_x, None);
        proof.add_rule_step(rule, Vec::new(), vec![h1, h2], vec![x, one]);

        let error =
            try_export_alethe(&proof, &terms).expect_err("a non-Boolean polarity must fail closed");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("polarity for link 0 must be true or false")
            ),
            "{error}"
        );
    }
}

#[test]
fn generic_resolution_export_accepts_complete_nary_annotations() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    let yes = terms.mk_bool(true);

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let first = proof.add_theory_lemma("test", vec![a, b]);
        let second = proof.add_theory_lemma("test", vec![not_b]);
        let third = proof.add_theory_lemma("test", vec![not_a]);
        proof.add_rule_step(
            rule,
            Vec::new(),
            vec![first, second, third],
            vec![b, yes, a, yes],
        );

        let output = try_export_alethe(&proof, &terms)
            .expect("one pivot/polarity pair per link must export");
        assert!(output.contains(":args (b true a true)"), "{output}");
    }
}

#[test]
fn generic_resolution_export_rejects_surface_changed_polarity() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let yes = terms.mk_bool(true);
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(yes, "(= p p)".to_string());

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let h1 = proof.add_assume(p, None);
        let h2 = proof.add_assume(not_p, None);
        proof.add_rule_step(rule, Vec::new(), vec![h1, h2], vec![p, yes]);

        let error = try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &terms,
            &[p, not_p],
            Some(&overrides),
        )
        .expect_err("a Boolean constant printed as an equality must fail closed");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("effective surface overrides are active")
            ),
            "{error}"
        );
    }
}

#[test]
fn generic_resolution_export_rejects_surface_changed_pivot_depth() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let yes = terms.mk_bool(true);
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(p, "(not (not p))".to_string());
    overrides.insert(not_p, "(not p)".to_string());

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let h1 = proof.add_assume(p, None);
        let h2 = proof.add_assume(not_p, None);
        proof.add_rule_step(rule, Vec::new(), vec![h1, h2], vec![p, yes]);

        let error = try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &terms,
            &[p, not_p],
            Some(&overrides),
        )
        .expect_err("a surface pivot with a different exact negation depth must fail closed");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("effective surface overrides are active")
            ),
            "{error}"
        );
    }
}

/// What the expensive `or` is wrapped in before it is assumed.
///
/// The pre-flight is allowed to answer QUIETLY (decline just the bridge) about
/// two schemas it cannot render — a binder and AY's internal `const-array` —
/// and every wrapper here puts one of them around a term whose RENDER is the
/// thing the bound exists to prevent. A pre-flight that answers on the schema
/// it met first never measures the wrapped term, so it degrades into the
/// printer, and its answer depends on which child the stack popped first.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum WideShape {
    /// The bare `(or p ... p)`.
    Plain,
    /// `(forall ((z Int)) (or p ... p))`: an unrenderable SHAPE wrapped around
    /// an unaffordable SIZE. The size has to win.
    UnderBinder,
    /// `(and (or p ... p) (= (select (const-array #x00) k) #x00))`, in both
    /// operand orders. Two orders because a pre-flight that stops at the first
    /// unrenderable symbol answers one way when the wide conjunct is popped
    /// first and the other way when it is popped second — the verdict must not
    /// depend on traversal order.
    ConstArrayConjunct { wide_first: bool },
}

/// An `(or p p ... p)` of `arity` arguments — optionally wrapped per
/// [`WideShape`] — with both polarities of the root mapped to a tiny surface
/// spelling and resolved against each other. The canonical rendering of the
/// wide `or` is ~2 bytes per argument, so the term is cheap to BUILD and
/// expensive to RENDER — which is the whole point: it separates a gate that
/// inspects structure from one that formats it.
struct WideOverrideCase {
    terms: TermStore,
    /// The expensive `or` itself, whatever the root is wrapped in. This is the
    /// render the pre-flight exists to prevent, so it is what the timing
    /// comparison is calibrated against.
    wide: TermId,
    root: TermId,
    not_root: TermId,
    proof: Proof,
    /// The same refutation with a PLAIN resolution step, so the
    /// annotated-resolution override gate never fires and the authored-assume
    /// pre-flight is the only gate on the path. Without it that second gate
    /// masks a pre-flight that let the term through: the leak shows up as
    /// `Err` either way and the difference is invisible.
    unannotated_proof: Proof,
    overrides: DetHashMap<TermId, String>,
}

impl WideOverrideCase {
    fn new(arity: usize, shape: WideShape) -> Self {
        let mut terms = TermStore::new();
        let p = terms.mk_var("p", Sort::Bool);
        let wide = terms.mk_app(Symbol::Named("or".to_string()), vec![p; arity], Sort::Bool);
        let (root, surface) = match shape {
            WideShape::Plain => (wide, "p".to_string()),
            WideShape::UnderBinder => (
                terms.mk_forall(vec![("z".to_string(), Sort::Int)], wide),
                "(forall ((z Int)) p)".to_string(),
            ),
            WideShape::ConstArrayConjunct { wide_first } => {
                let byte = Sort::bitvec(8);
                let fill = terms.mk_bitvec(0u32.into(), 8);
                let const_array = terms.mk_app(
                    Symbol::named("const-array"),
                    [fill],
                    Sort::array(byte.clone(), byte.clone()),
                );
                let key = terms.mk_var("k", byte.clone());
                let read = terms.mk_app(Symbol::named("select"), [const_array, key], byte);
                let read_is_fill = terms.mk_app(Symbol::named("="), [read, fill], Sort::Bool);
                let conjuncts = if wide_first {
                    vec![wide, read_is_fill]
                } else {
                    vec![read_is_fill, wide]
                };
                let read_surface =
                    "(= (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) k) #x00)";
                let surface = if wide_first {
                    format!("(and p {read_surface})")
                } else {
                    format!("(and {read_surface} p)")
                };
                (
                    terms.mk_app(Symbol::Named("and".to_string()), conjuncts, Sort::Bool),
                    surface,
                )
            }
        };
        let not_root = terms.mk_not_raw(root);
        let yes = terms.mk_bool(true);
        let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
        overrides.insert(root, surface.clone());
        overrides.insert(not_root, format!("(not {surface})"));

        let mut proof = Proof::new();
        let h1 = proof.add_assume(root, None);
        let h2 = proof.add_assume(not_root, None);
        proof.add_rule_step(
            AletheRule::Resolution,
            Vec::new(),
            vec![h1, h2],
            vec![root, yes],
        );
        let mut unannotated_proof = Proof::new();
        let u1 = unannotated_proof.add_assume(root, None);
        let u2 = unannotated_proof.add_assume(not_root, None);
        unannotated_proof.add_resolution(Vec::new(), root, u1, u2);
        Self {
            terms,
            wide,
            root,
            not_root,
            proof,
            unannotated_proof,
            overrides,
        }
    }

    fn export(&self, work_budget: Option<u64>) -> Result<String, AlethePrintError> {
        try_export_alethe_with_problem_scope_overrides_and_budget(
            &self.proof,
            &self.terms,
            &[self.root, self.not_root],
            Some(&self.overrides),
            work_budget,
        )
    }

    fn export_unannotated(&self) -> Result<String, AlethePrintError> {
        try_export_alethe_with_problem_scope_overrides_and_budget(
            &self.unannotated_proof,
            &self.terms,
            &[self.root, self.not_root],
            Some(&self.overrides),
            None,
        )
    }
}

/// Smallest wall of `rounds` repetitions, in microseconds. The minimum (not the
/// mean) is what makes these ratios usable under a loaded test harness: a
/// scheduler steal can only ever inflate a sample, never deflate one.
fn min_wall_us(rounds: usize, mut body: impl FnMut()) -> f64 {
    let mut best = f64::MAX;
    for _ in 0..rounds {
        let started = std::time::Instant::now();
        body();
        let us = started.elapsed().as_secs_f64() * 1e6;
        if us < best {
            best = us;
        }
    }
    best
}

/// Smallest per-export wall over several rounds, abandoning a round as soon as
/// it has already blown `ceiling_us` per export. The early exit is what keeps a
/// REGRESSED gate honest: without it a gate that started rendering would make
/// this test grind for minutes through the very formatting it forbids before
/// reporting. With it, the returned figure is >= `ceiling_us` and the caller's
/// assertion fails in well under a second.
fn per_rejection_wall_us(case: &WideOverrideCase, ceiling_us: f64) -> f64 {
    const ITERS: usize = 512;
    const ROUNDS: usize = 9;
    const CLOCK_STRIDE: usize = 64;
    let _ = case.export(Some(64));
    let mut best = f64::MAX;
    for _ in 0..ROUNDS {
        let started = std::time::Instant::now();
        let mut done = 0usize;
        for _ in 0..ITERS {
            let _ = std::hint::black_box(case.export(Some(64)));
            done += 1;
            if (done == 1 || done.is_multiple_of(CLOCK_STRIDE))
                && started.elapsed().as_secs_f64() * 1e6 > ceiling_us * done as f64
            {
                break;
            }
        }
        let us = started.elapsed().as_secs_f64() * 1e6 / done as f64;
        if us < best {
            best = us;
        }
    }
    best
}

/// Wall of the single `render_term_canonical` call the structural pre-flight
/// exists to prevent — measured here, on this machine, under this load, so the
/// comparison below is self-calibrating rather than a hard-coded millisecond
/// budget that drifts with hardware.
fn one_canonical_render_wall_us(case: &WideOverrideCase) -> f64 {
    min_wall_us(3, || {
        std::hint::black_box(crate::render_term_canonical(&case.terms, case.wide));
    })
}

/// Two bounded gates can claim this input: the authored-assume structural
/// pre-flight and the annotated-resolution override gate. Which one fires
/// first is an internal ordering this test deliberately does NOT pin — both
/// reject without formatting, and the timing assertions below are what prove
/// that, rather than the spelling of a message. What IS pinned is that the
/// rejection came from a gate that inspected the step at all.
fn is_bounded_gate_rejection(reason: &str) -> bool {
    reason.contains("canonical term exceeds the structural rendering bound")
        || reason.contains("effective surface overrides are active")
}

#[test]
fn annotated_resolution_override_gate_does_not_render_huge_canonical_term() {
    const SCALED_ARITY: usize = 8_192;
    const HUGE_ARITY: usize = 1_000_000;
    /// One guarded rejection must be at least this many times cheaper than the
    /// single canonical render it prevents. Measured margin on this shape is
    /// ~90_000x (0.22us per rejection against a 20ms render at 1_000_000
    /// arguments); a gate that formatted the term before refusing lands at ~1x,
    /// so the threshold sits three orders of magnitude clear of the failure.
    const MIN_REJECT_SPEEDUP_OVER_ONE_RENDER: f64 = 1_000.0;
    /// Growing the `or` from 8_192 to 1_000_000 arguments multiplies arity by
    /// 122; the per-rejection wall may not follow it. Measured 0.97x. A gate
    /// that walked every argument before refusing lands near 122x.
    const MAX_REJECT_WALL_GROWTH: f64 = 16.0;

    let huge = WideOverrideCase::new(HUGE_ARITY, WideShape::Plain);

    // Fail closed, and do so independently of the emission work budget.
    // Budget exhaustion is a REACHABLE outcome on this shape — the same
    // construction at arity 2 under `Some(64)` returns
    // `EmissionBudgetExhausted` — so pinning the variant is what stops this
    // test from passing on an emission stall that never inspected the term.
    for work_budget in [Some(64u64), Some(1_000_000u64), None] {
        let error = huge
            .export(work_budget)
            .expect_err("annotated resolution with any active override must fail closed");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if is_bounded_gate_rejection(reason)
            ),
            "budget {work_budget:?}: {error}"
        );
    }

    // NO HUGE RENDER, asserted directly rather than through a message proxy:
    // one rejection has to be orders of magnitude cheaper than one render of
    // the very term it refused. If any gate on the path formatted the term
    // before refusing, this ratio collapses to ~1.
    let one_render_us = one_canonical_render_wall_us(&huge);
    let ceiling_us = one_render_us / MIN_REJECT_SPEEDUP_OVER_ONE_RENDER;
    let per_rejection_us = per_rejection_wall_us(&huge, ceiling_us);
    let speedup = one_render_us / per_rejection_us;
    assert!(
        speedup >= MIN_REJECT_SPEEDUP_OVER_ONE_RENDER,
        "rejecting a {HUGE_ARITY}-argument term cost {per_rejection_us:.4}us against a \
         {one_render_us:.1}us canonical render of the same term ({speedup:.1}x); a gate that \
         refuses without rendering must be at least {MIN_REJECT_SPEEDUP_OVER_ONE_RENDER:.0}x cheaper"
    );

    // ...and the same wall, held flat across a 122x arity increase, so a gate
    // that merely renders CHEAPLY still cannot satisfy this test.
    let scaled = WideOverrideCase::new(SCALED_ARITY, WideShape::Plain);
    let scaled_us = per_rejection_wall_us(&scaled, ceiling_us);
    let growth = per_rejection_us / scaled_us;
    assert!(
        growth <= MAX_REJECT_WALL_GROWTH,
        "the rejection wall tracked arity: {scaled_us:.4}us at {SCALED_ARITY} arguments vs \
         {per_rejection_us:.4}us at {HUGE_ARITY} ({growth:.1}x for a 122x arity increase)"
    );
}

/// The same no-huge-render property as above, on the two schemas the
/// authored-assume pre-flight is allowed to decline QUIETLY.
///
/// The pre-flight may answer `UnsupportedShape` — which the planner turns into
/// "no bridge" rather than "no document" — but it may only do so AFTER it has
/// finished measuring the term. A pre-flight that answers the instant it meets
/// a binder or a `const-array` never measures what the schema is wrapped
/// around, so the caller degrades into the ordinary printer and formats the
/// very term the bound exists to keep off the wire: measured here, a
/// `(forall ((z Int)) (or p ... p))` of 1_000_000 arguments was rendered in
/// 31_979us against 0.5us for the same refusal without the binder, i.e. the
/// wall tracked arity at 121x for a 122x arity increase. The bare `or` in
/// `annotated_resolution_override_gate_does_not_render_huge_canonical_term`
/// carries no binder at all, which is exactly why it did not catch this.
///
/// Same two criteria, same constants, applied per shape.
#[test]
fn wrapped_unrenderable_shapes_do_not_render_huge_canonical_terms() {
    const SCALED_ARITY: usize = 8_192;
    const HUGE_ARITY: usize = 1_000_000;
    /// Identical to the bare-`or` ratchet: one guarded rejection must be at
    /// least this many times cheaper than the single canonical render it
    /// prevents.
    const MIN_REJECT_SPEEDUP_OVER_ONE_RENDER: f64 = 1_000.0;
    /// Identical to the bare-`or` ratchet: growing the `or` from 8_192 to
    /// 1_000_000 arguments multiplies arity by 122, and the per-rejection wall
    /// may not follow it.
    const MAX_REJECT_WALL_GROWTH: f64 = 16.0;

    for shape in [
        WideShape::UnderBinder,
        WideShape::ConstArrayConjunct { wide_first: true },
        WideShape::ConstArrayConjunct { wide_first: false },
    ] {
        let huge = WideOverrideCase::new(HUGE_ARITY, shape);

        // Fail closed. A term that is BOTH unrenderable and oversized is a
        // size failure: the size verdict outranks the shape verdict, so the
        // quiet `Ok(None)` decline is not available here.
        for work_budget in [Some(64u64), Some(1_000_000u64), None] {
            let error = match huge.export(work_budget) {
                Err(error) => error,
                Ok(document) => panic!(
                    "{shape:?} at {HUGE_ARITY} arguments, budget {work_budget:?}: an \
                     unrenderable schema wrapped around an unaffordable term must still fail \
                     closed, got a {}-byte document",
                    document.len()
                ),
            };
            assert!(
                matches!(
                    error,
                    AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                        if is_bounded_gate_rejection(reason)
                ),
                "{shape:?}, budget {work_budget:?}: {error}"
            );
        }

        // NO HUGE RENDER: one rejection has to be orders of magnitude cheaper
        // than one render of the wide `or` it refused.
        let one_render_us = one_canonical_render_wall_us(&huge);
        let ceiling_us = one_render_us / MIN_REJECT_SPEEDUP_OVER_ONE_RENDER;
        let per_rejection_us = per_rejection_wall_us(&huge, ceiling_us);
        let speedup = one_render_us / per_rejection_us;
        assert!(
            speedup >= MIN_REJECT_SPEEDUP_OVER_ONE_RENDER,
            "{shape:?}: rejecting a {HUGE_ARITY}-argument term cost {per_rejection_us:.4}us \
             against a {one_render_us:.1}us canonical render of the same term ({speedup:.1}x); a \
             gate that refuses without rendering must be at least \
             {MIN_REJECT_SPEEDUP_OVER_ONE_RENDER:.0}x cheaper"
        );

        // ...and the wall stays flat across a 122x arity increase, so a gate
        // that walked the wrapped term before refusing cannot satisfy this.
        let scaled = WideOverrideCase::new(SCALED_ARITY, shape);
        let scaled_us = per_rejection_wall_us(&scaled, ceiling_us);
        let growth = per_rejection_us / scaled_us;
        assert!(
            growth <= MAX_REJECT_WALL_GROWTH,
            "{shape:?}: the rejection wall tracked arity: {scaled_us:.4}us at {SCALED_ARITY} \
             arguments vs {per_rejection_us:.4}us at {HUGE_ARITY} ({growth:.1}x for a 122x \
             arity increase)"
        );
    }
}

/// The pre-flight's answer may not depend on which child its stack pops first.
///
/// `(and WIDE CONST_ARRAY_READ)` and `(and CONST_ARRAY_READ WIDE)` are the same
/// term with its conjuncts swapped. A pre-flight that returns at the first
/// unrenderable symbol answers them differently — measured on the rejected
/// revision, `wide_first = true` refused in 0.4us while `wide_first = false`
/// returned a 240-byte document in 7_710us — which makes a fail-closed bound
/// depend on an internal ordering no caller controls.
///
/// Deliberately on the UNANNOTATED refutation. With an annotated resolution the
/// override gate refuses both orders for its own reason and the leak is
/// invisible; here the authored-assume pre-flight is the only gate on the path,
/// so a leak shows up as the document it actually produces.
///
/// Both directions are pinned: an affordable conjunction must still EXPORT (the
/// quiet decline is what keeps one constant-array assertion from costing the
/// whole proof), and an unaffordable one must FAIL CLOSED — whichever operand
/// the walk happens to reach first.
#[test]
fn const_array_conjunct_verdict_does_not_depend_on_operand_order() {
    for (arity, must_fail_closed) in [(2usize, false), (8_192, true), (1_000_000, true)] {
        let wide_first =
            WideOverrideCase::new(arity, WideShape::ConstArrayConjunct { wide_first: true })
                .export_unannotated();
        let wide_second =
            WideOverrideCase::new(arity, WideShape::ConstArrayConjunct { wide_first: false })
                .export_unannotated();
        assert_eq!(
            wide_first.is_ok(),
            wide_second.is_ok(),
            "at {arity} arguments the same conjunction answered differently with its operands \
             swapped: wide-first {wide_first:?} vs wide-second {wide_second:?}"
        );
        assert_eq!(
            wide_first.is_err(),
            must_fail_closed,
            "at {arity} arguments the conjunction should {} closed: {wide_first:?}",
            if must_fail_closed { "fail" } else { "NOT fail" }
        );
    }
}

/// Companion to the huge-term case above, which now lands on the structural
/// pre-flight and so no longer reaches the override gate at all. Without this,
/// widening that test's reason to accept either gate would silently retire the
/// only coverage the annotated-resolution override gate had.
#[test]
fn annotated_resolution_override_gate_rejects_a_small_surface_override() {
    let case = WideOverrideCase::new(2, WideShape::Plain);
    let error = case
        .export(None)
        .expect_err("an annotated resolution under active surface overrides must fail closed");
    assert!(
        matches!(
            error,
            AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                if reason.contains("effective surface overrides are active")
        ),
        "{error}"
    );
}

#[test]
fn generic_resolution_export_rejects_repeated_directed_pivot() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let yes = terms.mk_bool(true);

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let left = proof.add_theory_lemma("test", vec![p]);
        let right = proof.add_theory_lemma("test", vec![not_p, not_p]);
        proof.add_rule_step(rule, Vec::new(), vec![left, right], vec![p, yes]);

        let error = try_export_alethe(&proof, &terms)
            .expect_err("a duplicate next-premise pivot must not be erased only internally");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("premise 1 contains a duplicate literal")
            ),
            "{error}"
        );
    }
}

#[test]
fn generic_resolution_export_rejects_duplicate_in_first_premise() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let yes = terms.mk_bool(true);

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let left = proof.add_theory_lemma("test", vec![p, p]);
        let right = proof.add_theory_lemma("test", vec![not_p]);
        proof.add_rule_step(rule, vec![p], vec![left, right], vec![p, yes]);

        let error = try_export_alethe(&proof, &terms)
            .expect_err("an explicit resolution first premise must be duplicate-free");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("first premise contains a duplicate literal")
            ),
            "{error}"
        );
    }
}

#[test]
fn generic_resolution_export_rejects_duplicate_in_conclusion() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let yes = terms.mk_bool(true);

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let left = proof.add_theory_lemma("test", vec![p, q]);
        let right = proof.add_theory_lemma("test", vec![not_p]);
        proof.add_rule_step(rule, vec![q, q], vec![left, right], vec![p, yes]);

        let error = try_export_alethe(&proof, &terms)
            .expect_err("an explicit resolution conclusion must be duplicate-free");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("conclusion contains a duplicate literal")
            ),
            "{error}"
        );
    }
}

#[test]
fn generic_resolution_export_rejects_cross_premise_residual_collision() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let yes = terms.mk_bool(true);

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let left = proof.add_theory_lemma("test", vec![p, q]);
        let right = proof.add_theory_lemma("test", vec![not_p, q]);
        proof.add_rule_step(rule, vec![q], vec![left, right], vec![p, yes]);

        let error = try_export_alethe(&proof, &terms)
            .expect_err("an explicit resolution must retain both residual occurrences");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("residual for link 0 contains a duplicate literal")
            ),
            "{error}"
        );
    }
}

#[test]
fn generic_resolution_keeps_certified_distinct_bridge() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let equality = terms.mk_eq(x, y);
    let disequality = terms.mk_not_raw(equality);
    let no = terms.mk_bool(false);
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(disequality, "(distinct x y)".to_string());

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let h1 = proof.add_assume(disequality, None);
        let h2 = proof.add_assume(equality, None);
        proof.add_rule_step(rule, Vec::new(), vec![h1, h2], vec![equality, no]);

        let output = try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &terms,
            &[disequality, equality],
            Some(&overrides),
        )
        .expect("the exact unit distinct/equality bridge remains supported");
        assert!(output.contains(":rule distinct_elim"), "{output}");
    }
}

#[test]
fn argument_free_resolution_keeps_surface_override_path() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(p, "(not (not p))".to_string());
    overrides.insert(not_p, "(not p)".to_string());

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let h1 = proof.add_assume(p, None);
        let h2 = proof.add_assume(not_p, None);
        proof.add_rule_step(rule, Vec::new(), vec![h1, h2], Vec::new());

        let output = try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &terms,
            &[p, not_p],
            Some(&overrides),
        )
        .expect("argument-free resolution retains its existing inferred-pivot path");
        assert!(!output.contains(":args"), "{output}");
    }
}
