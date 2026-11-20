// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The renderability check is BOUNDED (DR-PROOF-RENDER-BUDGET-20261118).
//!
//! `congruence_derivation_renders` used to build a budget-free printer and
//! render every step in full, keeping only `.is_ok()`. The printer streams
//! every occurrence of a shared application again, so the bytes it wrote grew
//! with the root's TREE size. MEASURED on CHC-COMP 2026 LRA-Lin
//! `oral_messages` (`ec4cd5b8abaf3a98`): a 4,659-node authored root is 1.03e14
//! tree nodes; one check built a 1.3 GB `String` and the run died of a 5 GB
//! memout ~4 s in, taking every portfolio engine with it.
//!
//! The doubling chain below is the same shape in miniature: `t_{i+1} =
//! (+ t_i t_i)` is a 23-node DAG whose text is ~25 MB. The `ite` chain is the
//! shape that defeats a byte counter: every level is an ASSEMBLED `String`
//! that copies the whole chain below it, so the check's allocation is
//! quadratic in the depth unless the work counter charges every assembled
//! `String` (the export's counter, unchanged) and nothing is assembled past
//! the budget (`AssembledRendering::CachedWithinBudget`).

use super::{
    render_derivation_within, CongruenceDerivation, DerivationRender, DERIVATION_RENDER_WORK_BUDGET,
};
use crate::alethe_printer::{AlethePrinter, AssembledRendering};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, ProofId, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;
use num_rational::BigRational;

/// The largest single charge the printer makes between two exhaustion checks
/// in these fixtures (one application head, one variable name, one cached
/// `not`): the check is "over the budget", so the work may pass it by at most
/// one write.
const ONE_WRITE: u64 = 4096;

/// The budget of ay-dpll's full-document screens and best-effort default
/// export (`DEFAULT_ALETHE_EMISSION_WORK_BUDGET`): printers that are NOT a
/// renderability check, and charge exactly as on origin/main.
const SCREEN_BUDGET: u64 = 64 << 20;

fn real_zero(terms: &mut TermStore) -> TermId {
    terms.mk_rational(BigRational::from_integer(BigInt::from(0)))
}

fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

/// `t_0 = x`, `t_{i+1} = (+ t_i t_i)`; returns `t_depth`.
fn doubling_chain(terms: &mut TermStore, x: TermId, depth: usize) -> TermId {
    let mut t = x;
    for _ in 0..depth {
        t = terms.mk_app(Symbol::named("+"), vec![t, t], Sort::Real);
    }
    t
}

/// `assume ROOT; and_pos (cl (not ROOT) conjunct) :args (ROOT);
/// th_resolution (cl conjunct)` — the authored-conjunct lane's fragment.
fn conjunct_fragment(
    terms: &mut TermStore,
    root: TermId,
    position: u32,
    conjunct: TermId,
) -> CongruenceDerivation {
    let not_root = terms.mk_not_raw(root);
    CongruenceDerivation {
        steps: vec![
            ProofStep::Assume(root),
            ProofStep::Step {
                rule: AletheRule::AndPos(position),
                clause: vec![not_root, conjunct],
                premises: Vec::new(),
                args: vec![root],
            },
            ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: vec![conjunct],
                premises: vec![ProofId(1), ProofId(0)],
                args: Vec::new(),
            },
        ],
        clause: vec![conjunct],
    }
}

/// `(and (= t_depth 0.0) (= x 1.0))` and its fragment for the first conjunct.
fn doubling_fragment(terms: &mut TermStore, depth: usize) -> CongruenceDerivation {
    let x = terms.mk_var("x", Sort::Real);
    let t = doubling_chain(terms, x, depth);
    let zero = real_zero(terms);
    let one = terms.mk_rational(BigRational::from_integer(BigInt::from(1)));
    let first = eq(terms, t, zero);
    let second = eq(terms, x, one);
    let root = terms.mk_app(Symbol::named("and"), vec![first, second], Sort::Bool);
    conjunct_fragment(terms, root, 0, first)
}

#[test]
fn the_small_doubling_fragment_renders() {
    // The control: the SAME fragment shape over a short chain renders, so the
    // declines below are about size and nothing else.
    let mut terms = TermStore::new();
    let derivation = doubling_fragment(&mut terms, 4);
    let (renders, work) = render_derivation_within(
        &terms,
        None,
        &derivation,
        DERIVATION_RENDER_WORK_BUDGET,
        &mut || true,
    );
    assert_eq!(renders, DerivationRender::Renders, "the four-deep chain");
    assert!(work > 0 && work < 4096, "work {work}");
}

#[test]
fn a_tree_blowup_is_declined_within_a_small_budget() {
    let mut terms = TermStore::new();
    let derivation = doubling_fragment(&mut terms, 22);
    let budget = 1 << 20;
    let (renders, work) = render_derivation_within(&terms, None, &derivation, budget, &mut || true);
    assert_eq!(
        renders,
        DerivationRender::OutOfBudget,
        "a 25 MB root cannot render in 1 MiB"
    );
    assert!(
        work <= budget + ONE_WRITE,
        "the check charged {work} bytes against a {budget} budget"
    );
}

#[test]
fn a_tree_blowup_is_declined_within_the_default_budget() {
    // Each step prints ROOT (~25 MB) at least once, so the fragment is over
    // 32 MiB; the unbounded check rendered all of it and answered `true`.
    let mut terms = TermStore::new();
    let derivation = doubling_fragment(&mut terms, 22);
    let (renders, work) = render_derivation_within(
        &terms,
        None,
        &derivation,
        DERIVATION_RENDER_WORK_BUDGET,
        &mut || true,
    );
    assert_eq!(renders, DerivationRender::OutOfBudget);
    assert!(
        work <= DERIVATION_RENDER_WORK_BUDGET + ONE_WRITE,
        "work {work}"
    );
}

#[test]
fn a_refusing_stop_declines_even_a_small_fragment() {
    let mut terms = TermStore::new();
    let derivation = doubling_fragment(&mut terms, 4);
    let (renders, _) = render_derivation_within(
        &terms,
        None,
        &derivation,
        DERIVATION_RENDER_WORK_BUDGET,
        &mut || false,
    );
    assert_eq!(
        renders,
        DerivationRender::OutOfBudget,
        "the solve's stop must decline the check"
    );
}

#[test]
fn a_hard10_shaped_root_still_renders_every_conjunct() {
    // `QF_UFLIA/mathsat/EufLaArithmetic/hard/hard10.smt2` parses to one flat
    // 146-ary authored `and`, from which the lane derives 145 conjuncts. Every
    // one of those fragments must still render under the per-check budget.
    let mut terms = TermStore::new();
    let ten = terms.mk_int(BigInt::from(10));
    let conjuncts: Vec<TermId> = (0..146)
        .map(|i| {
            let x = terms.mk_var(&format!("x{i}"), Sort::Int);
            terms.mk_app(Symbol::named("<="), vec![x, ten], Sort::Bool)
        })
        .collect();
    let root = terms.mk_app(Symbol::named("and"), conjuncts.clone(), Sort::Bool);
    for (position, &conjunct) in conjuncts.iter().enumerate() {
        let position = u32::try_from(position).expect("small");
        let derivation = conjunct_fragment(&mut terms, root, position, conjunct);
        let (renders, work) = render_derivation_within(
            &terms,
            None,
            &derivation,
            DERIVATION_RENDER_WORK_BUDGET,
            &mut || true,
        );
        assert_eq!(
            renders,
            DerivationRender::Renders,
            "conjunct {position} must still render"
        );
        assert!(work < 64 * 1024, "conjunct {position} charged {work}");
    }
}

/// `(ite c_k (not (ite c_{k-1} ...)) s)` nested `depth` deep over a shared
/// leaf `s`, so assembled renderings nest AND repeat (cache hits).
fn ite_nest(terms: &mut TermStore, depth: usize) -> TermId {
    let y = terms.mk_var("y", Sort::Real);
    let zero = real_zero(terms);
    let shared = eq(terms, y, zero);
    let mut term = shared;
    for i in 0..depth {
        let c = terms.mk_var(&format!("c{i}"), Sort::Bool);
        let negated = terms.mk_not_raw(term);
        term = terms.mk_ite_raw(c, negated, shared);
    }
    term
}

#[test]
fn every_assembled_string_is_charged_as_the_export_charges_it() {
    // The work counter is the export's, unchanged: an assembled `not`/`ite`
    // is charged its FULL length when built, on top of its children, so a
    // 12-deep nest of 311 bytes is charged 4,035. That over-count is what
    // makes the counter cover every `String` `format_cache` retains; the
    // emission, screen and preflight budgets that read it are calibrated on
    // exactly this figure.
    let mut terms = TermStore::new();
    let term = ite_nest(&mut terms, 12);
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, None);
    let text = printer.format_term(term);
    assert_eq!(text.len(), 311);
    assert_eq!(printer.work_used(), 4035);
}

/// `E_0 = e`, `E_{i+1} = (ite p_i A_i E_i)`, each `A_i` a DISTINCT depth-12
/// doubling chain (~28 KB of text, never a cache hit); returns `E_depth`.
fn ite_chain_over_distinct_branches(terms: &mut TermStore, depth: usize) -> TermId {
    let mut chain = terms.mk_var("e", Sort::Real);
    for i in 0..depth {
        let p = terms.mk_var(&format!("p{i}"), Sort::Bool);
        let y = terms.mk_var(&format!("y{i}"), Sort::Real);
        let branch = doubling_chain(terms, y, 12);
        chain = terms.mk_ite_raw(p, branch, chain);
    }
    chain
}

#[test]
fn an_ite_chain_over_distinct_branches_is_declined_within_twice_the_budget() {
    // Review probe (DR-PROOF-RENDER-BUDGET-20261118): the conjunct fragment
    // of `(and (= E_400 0) (= x0 1))`. `E_400` is 14.3 MB of text over a
    // term store of 6,003 nodes, and the 400 levels assembled on the way back
    // up copy ~2.8 GB. A counter of output bytes alone let the check build
    // them all (3.73 GB peak RSS, review 2), and so does the export's counter
    // when assembly continues past exhaustion (2.81 GB charged, 3.73 GB peak
    // RSS, measured). Here no assembly is built once the budget is passed, so
    // the check stops within `2 * B` of charged work
    // (`DERIVATION_RENDER_WORK_BUDGET`'s argument): measured 33.7 MB charged,
    // 55.5 MB peak RSS for the whole test process (4.9 MB for an empty test).
    let mut terms = TermStore::new();
    let chain = ite_chain_over_distinct_branches(&mut terms, 400);
    let zero = real_zero(&mut terms);
    let x0 = terms.mk_var("x0", Sort::Real);
    let one = terms.mk_rational(BigRational::from_integer(BigInt::from(1)));
    let first = eq(&mut terms, chain, zero);
    let second = eq(&mut terms, x0, one);
    let root = terms.mk_app(Symbol::named("and"), vec![first, second], Sort::Bool);
    let derivation = conjunct_fragment(&mut terms, root, 0, first);
    let (renders, work) = render_derivation_within(
        &terms,
        None,
        &derivation,
        DERIVATION_RENDER_WORK_BUDGET,
        &mut || true,
    );
    assert_eq!(renders, DerivationRender::OutOfBudget);
    assert!(
        work <= 2 * DERIVATION_RENDER_WORK_BUDGET + ONE_WRITE,
        "the check charged {work} bytes against a {DERIVATION_RENDER_WORK_BUDGET} budget"
    );
}

/// Render `term` streamed under no budget; returns the text and the work.
fn streamed(
    terms: &TermStore,
    term: TermId,
    overrides: Option<&DetHashMap<TermId, String>>,
) -> (String, u64) {
    let printer = AlethePrinter::new_with_overrides_and_budget(terms, overrides, None)
        .with_assembled_rendering(AssembledRendering::Streamed);
    let text = printer.format_term(term);
    (text, printer.work_used())
}

#[test]
fn the_streamed_rendering_is_the_assembled_one_and_charges_its_bytes() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("odd name", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let le = terms.mk_app(Symbol::named("<="), vec![x, zero], Sort::Bool);
    let ge = terms.mk_app(Symbol::named(">="), vec![y, x], Sort::Bool);
    let not = terms.mk_not_raw(le);
    let ite = terms.mk_ite_raw(not, x, y);
    let ite_eq = terms.mk_app(Symbol::named("="), vec![ite, ite], Sort::Bool);
    let empty_let = terms.mk_let(Vec::new(), ge);
    let let_term = terms.mk_let(vec![("a".to_string(), x), ("b c".to_string(), ite)], ite_eq);
    let forall = terms.mk_forall(
        vec![("x".to_string(), Sort::Int), ("q".to_string(), Sort::Bool)],
        let_term,
    );
    let exists = terms.mk_exists(vec![("z".to_string(), Sort::Real)], forall);
    let nested = terms.mk_not_raw(exists);
    let const_array = terms.mk_const_array(Sort::Int, ite);
    let nest = ite_nest(&mut terms, 12);
    let shapes = [
        not,
        ite,
        ite_eq,
        empty_let,
        let_term,
        forall,
        exists,
        nested,
        const_array,
        nest,
    ];
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(le, "(not (> x 0))".to_string());
    for &term in &shapes {
        let assembled = crate::format_term_alethe(&terms, term);
        let (text, work) = streamed(&terms, term, None);
        assert_eq!(
            text,
            assembled,
            "streamed spelling of {:?}",
            terms.get(term)
        );
        assert_eq!(work, text.len() as u64, "streamed work of {assembled}");
        let assembled = crate::format_term_alethe_with_overrides(&terms, term, &overrides);
        let (text, work) = streamed(&terms, term, Some(&overrides));
        assert_eq!(text, assembled, "streamed spelling under overrides");
        assert_eq!(work, text.len() as u64, "streamed work of {assembled}");
    }
}

#[test]
fn the_bounded_term_renderer_is_exact_within_its_cap_and_declines_past_it() {
    let mut terms = TermStore::new();
    let nest = ite_nest(&mut terms, 12);
    let full = crate::format_term_alethe(&terms, nest);
    assert_eq!(
        crate::format_term_alethe_bounded(&terms, nest, None, full.len() as u64, &mut || true),
        Some(full.clone()),
        "a rendering of exactly the cap is admitted, byte-identical"
    );
    assert_eq!(
        crate::format_term_alethe_bounded(&terms, nest, None, full.len() as u64 - 1, &mut || {
            true
        }),
        None
    );
    assert_eq!(
        crate::format_term_alethe_bounded(&terms, nest, None, full.len() as u64, &mut || false),
        None,
        "a refusing stop declines"
    );
    let x = terms.mk_var("x", Sort::Real);
    let blowup = doubling_chain(&mut terms, x, 40);
    assert_eq!(
        crate::format_term_alethe_bounded(&terms, blowup, None, 64 * 1024, &mut || true),
        None,
        "a 6.6e12-byte rendering is declined without being built"
    );
}

#[test]
fn the_bounded_term_renderer_holds_an_ite_chain_to_its_cap() {
    // Streamed, the 400-level chain's ~11 MB is never assembled: the render
    // stops at the cap after writing about the cap.
    let mut terms = TermStore::new();
    let chain = ite_chain_over_distinct_branches(&mut terms, 400);
    let cap = 64 * 1024;
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(cap))
        .with_assembled_rendering(AssembledRendering::Streamed);
    let _ = printer.format_term(chain);
    assert!(printer.work_budget_exhausted());
    assert!(
        printer.work_used() <= cap + ONE_WRITE,
        "{}",
        printer.work_used()
    );
    assert_eq!(
        crate::format_term_alethe_bounded(&terms, chain, None, cap, &mut || true),
        None
    );
}

/// `t_0 = x`, `t_d` the doubling chain, `ROOT = (and (= t_d 0.0) (= x 1.0))`,
/// with ROOT's override an authored `let` spelling of `levels` levels: `depth`
/// of them build the chain, the rest bind `u_k` to `x` unused. Returns ROOT,
/// its first conjunct and the override table.
fn let_bridge_probe(
    terms: &mut TermStore,
    depth: usize,
    levels: usize,
) -> (TermId, TermId, DetHashMap<TermId, String>) {
    let x = terms.mk_var("x", Sort::Real);
    let t = doubling_chain(terms, x, depth);
    let zero = real_zero(terms);
    let one = terms.mk_rational(BigRational::from_integer(BigInt::from(1)));
    let first = eq(terms, t, zero);
    let second = eq(terms, x, one);
    let root = terms.mk_app(Symbol::named("and"), vec![first, second], Sort::Bool);
    let canonical = crate::format_term_alethe(terms, root);
    let chain_text = crate::format_term_alethe(terms, t);
    let body = canonical.replacen(&chain_text, &format!("a{depth}"), 1);
    assert_ne!(body, canonical, "the chain prints inside the root");
    let mut surface = String::new();
    for i in 1..=depth {
        let previous = if i == 1 {
            "x".to_string()
        } else {
            format!("a{}", i - 1)
        };
        surface.push_str(&format!("(let ((a{i} (+ {previous} {previous}))) "));
    }
    for k in 1..=levels - depth {
        surface.push_str(&format!("(let ((u{k} x)) "));
    }
    surface.push_str(&body);
    surface.push_str(&")".repeat(levels));
    let mut overrides = DetHashMap::default();
    overrides.insert(root, surface);
    (root, first, overrides)
}

#[test]
fn the_let_assume_bridge_charges_every_byte_it_writes() {
    // Review 2 finding 1 (DR-PROOF-RENDER-BUDGET-20261118): the certified arm
    // writes the eliminated form once per level, in the `refl` and three
    // times more, but was charged four copies. Unbudgeted, the bridge must
    // still be the certified one, and the work must cover its text.
    let mut terms = TermStore::new();
    let (root, _, overrides) = let_bridge_probe(&mut terms, 8, 30);
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, Some(&overrides), None)
        .as_renderability_check();
    let text = printer
        .format_step(&ProofStep::Assume(root), ProofId(0))
        .expect("the bridge renders");
    assert!(text.contains(":rule let)"), "the certified arm: {text}");
    assert!(
        printer.work_used() >= text.len() as u64,
        "charged {} for {} bytes written",
        printer.work_used(),
        text.len()
    );
}

#[test]
fn a_deep_let_assume_bridge_is_declined_before_it_is_written() {
    // Review 2's probe: a 60-level authored surface over a 3.1 MB eliminated
    // form. The bridge's text is ~200 MB; it was written for 33 MB charged
    // (222 MB peak RSS). Its size is now charged before a byte of it is
    // written, so the check declines with the bridge unwritten.
    let mut terms = TermStore::new();
    let (root, first, overrides) = let_bridge_probe(&mut terms, 19, 60);
    let derivation = conjunct_fragment(&mut terms, root, 0, first);
    let (renders, _) = render_derivation_within(
        &terms,
        Some(&overrides),
        &derivation,
        DERIVATION_RENDER_WORK_BUDGET,
        &mut || true,
    );
    assert_eq!(renders, DerivationRender::OutOfBudget);
}

/// A flat `count`-ary canonical `and` of `(<= NAME_i 10)` atoms whose
/// override is the right-nested authored spelling `(and c0 (and c1 …))`.
fn right_nested_and_probe(
    terms: &mut TermStore,
    count: usize,
    name_width: usize,
) -> (TermId, Vec<TermId>, DetHashMap<TermId, String>) {
    let ten = terms.mk_int(BigInt::from(10));
    let conjuncts: Vec<TermId> = (0..count)
        .map(|i| {
            let x = terms.mk_var(&format!("v{i:0>name_width$}"), Sort::Int);
            terms.mk_app(Symbol::named("<="), vec![x, ten], Sort::Bool)
        })
        .collect();
    let root = terms.mk_app(Symbol::named("and"), conjuncts.clone(), Sort::Bool);
    let printed: Vec<String> = conjuncts
        .iter()
        .map(|&c| crate::format_term_alethe(terms, c))
        .collect();
    let mut surface = printed[count - 1].clone();
    for operand in printed[..count - 1].iter().rev() {
        surface = format!("(and {operand} {surface})");
    }
    let mut overrides = DetHashMap::default();
    overrides.insert(root, surface);
    (root, conjuncts, overrides)
}

#[test]
fn the_nested_and_pos_navigator_charges_every_byte_it_writes() {
    // Review 2 finding 2: each hop writes its parent and child in full.
    let mut terms = TermStore::new();
    let (root, conjuncts, overrides) = right_nested_and_probe(&mut terms, 64, 8);
    let step = and_pos_step(&mut terms, root, 40, conjuncts[40]);
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, Some(&overrides), None)
        .as_renderability_check();
    let text = printer
        .format_step(&step, ProofId(1))
        .expect("the navigator renders");
    assert!(text.contains(".g40 "), "40 hops: {text}");
    assert!(
        printer.work_used() >= text.len() as u64,
        "charged {} for {} bytes written",
        printer.work_used(),
        text.len()
    );
}

#[test]
fn a_deep_and_pos_navigation_is_declined_before_it_is_written() {
    // Review 2's probe, at the authored cap: a 1,001-ary canonical `and`
    // whose 64 KB override nests to the right. Conjunct 999 sits 999 hops
    // down and the hops write ~64 MB; it was copied ~2 x 999 times uncharged
    // and ANSWERED `Renders` (220 MB peak RSS at 43 KB).
    let mut terms = TermStore::new();
    let (root, conjuncts, overrides) = right_nested_and_probe(&mut terms, 1001, 48);
    let surface_len = overrides[&root].len();
    assert!(
        (60_000..=66_000).contains(&surface_len),
        "{surface_len} bytes"
    );
    let derivation = conjunct_fragment(&mut terms, root, 999, conjuncts[999]);
    let (renders, _) = render_derivation_within(
        &terms,
        Some(&overrides),
        &derivation,
        DERIVATION_RENDER_WORK_BUDGET,
        &mut || true,
    );
    assert_eq!(renders, DerivationRender::OutOfBudget);
}

/// `and_pos (cl (not ROOT) conjunct) :args (ROOT)` at `position`.
fn and_pos_step(terms: &mut TermStore, root: TermId, position: u32, conjunct: TermId) -> ProofStep {
    let not_root = terms.mk_not_raw(root);
    ProofStep::Step {
        rule: AletheRule::AndPos(position),
        clause: vec![not_root, conjunct],
        premises: Vec::new(),
        args: vec![root],
    }
}

#[test]
fn a_screen_printer_writes_deep_and_pos_navigations_charged_as_on_main() {
    // Parity review of rev 3, finding 1 scenario A: the navigator's pre-write
    // charge sat in the shared printer, so a 64 MiB full-document screen (and
    // the default export) declined a document with two `and_pos` steps deep
    // in a right-nested override, which origin/main wrote. Only a
    // renderability check charges them now. A 1,001-ary `and` whose ~64 KB
    // override (the authored-assume input cap) nests to the right, and
    // conjuncts 999 and 998 under it: the navigator writes ~60 MB per step.
    let mut terms = TermStore::new();
    let (root, conjuncts, overrides) = right_nested_and_probe(&mut terms, 1001, 48);
    let surface_len = overrides[&root].len() as u64;
    let steps = [
        and_pos_step(&mut terms, root, 999, conjuncts[999]),
        and_pos_step(&mut terms, root, 998, conjuncts[998]),
    ];

    let screen =
        AlethePrinter::new_with_overrides_and_budget(&terms, Some(&overrides), Some(SCREEN_BUDGET));
    let mut written = 0u64;
    for (index, step) in steps.iter().enumerate() {
        let text = screen
            .format_step(step, ProofId(index as u32 + 1))
            .expect("a screen still writes the navigation");
        assert!(text.contains(".g998 "), "998+ hops");
        written += text.len() as u64;
    }
    assert!(written > SCREEN_BUDGET, "{written} bytes written");
    // Main's charge: the printed root and clause a fixed number of times per
    // step (measured 1.92 MB, ~15 roots per step), nothing per hop.
    assert!(
        screen.work_used() < 32 * surface_len && screen.work_used() < written / 16,
        "charged {} for an {surface_len}-byte root and {written} bytes written",
        screen.work_used()
    );

    let check =
        AlethePrinter::new_with_overrides_and_budget(&terms, Some(&overrides), Some(SCREEN_BUDGET))
            .with_assembled_rendering(AssembledRendering::CachedWithinBudget)
            .as_renderability_check();
    let declined = steps
        .iter()
        .enumerate()
        .any(|(index, step)| check.format_step(step, ProofId(index as u32 + 1)).is_err());
    assert!(
        declined && check.work_budget_exhausted(),
        "declined as out of budget"
    );
}

#[test]
fn a_screen_printer_writes_a_certified_let_bridge_charged_as_on_main() {
    // Parity review of rev 3, finding 1 scenario B: a 45-level authored `let`
    // over a 1.5 MB eliminated form. Main charged ~7 copies of it, which fits
    // a 64 MiB screen; the certified arm writes ~49 copies, which does not.
    // Only a renderability check charges those before writing them.
    let mut terms = TermStore::new();
    let (root, _, overrides) = let_bridge_probe(&mut terms, 18, 45);
    let eliminated = crate::format_term_alethe(&terms, root).len() as u64;
    assert!(eliminated > 1_000_000, "{eliminated} bytes");

    let screen =
        AlethePrinter::new_with_overrides_and_budget(&terms, Some(&overrides), Some(SCREEN_BUDGET));
    let text = screen
        .format_step(&ProofStep::Assume(root), ProofId(0))
        .expect("a screen still writes the bridge");
    assert!(text.contains(":rule let)"), "the certified arm");
    assert!(text.len() as u64 > SCREEN_BUDGET, "{} bytes", text.len());
    assert!(
        screen.work_used() < 10 * eliminated,
        "charged {} for a {eliminated}-byte eliminated form",
        screen.work_used()
    );

    let check =
        AlethePrinter::new_with_overrides_and_budget(&terms, Some(&overrides), Some(SCREEN_BUDGET))
            .with_assembled_rendering(AssembledRendering::CachedWithinBudget)
            .as_renderability_check();
    assert!(check
        .format_step(&ProofStep::Assume(root), ProofId(0))
        .is_err());
    assert!(check.work_budget_exhausted(), "declined as out of budget");
}

/// `(= (store (store a i E_depth) i w) (store a i w))`, the `ArrayRowChain`
/// clause whose shadowed-stores lowering renders `E_depth` (an `ite` chain
/// over distinct branches) on an override-free sub-printer, and the one-step
/// derivation that checks it.
fn shadowed_store_probe(terms: &mut TermStore, depth: usize) -> CongruenceDerivation {
    let value = ite_chain_over_distinct_branches(terms, depth);
    let sort = Sort::array(Sort::Real, Sort::Real);
    let a = terms.mk_var("a", sort.clone());
    let i = terms.mk_var("i", Sort::Real);
    let w = terms.mk_var("w", Sort::Real);
    // Raw applications: `mk_store` would fold the shadowed write away.
    let inner = terms.mk_app(Symbol::named("store"), vec![a, i, value], sort.clone());
    let left = terms.mk_app(Symbol::named("store"), vec![inner, i, w], sort.clone());
    let right = terms.mk_app(Symbol::named("store"), vec![a, i, w], sort);
    let equality = eq(terms, left, right);
    CongruenceDerivation {
        steps: vec![ProofStep::TheoryLemma {
            theory: "array".into(),
            clause: vec![equality],
            farkas: None,
            kind: TheoryLemmaKind::ArrayRowChain,
            lia: None,
        }],
        clause: vec![equality],
    }
}

#[test]
fn a_shadowed_store_chain_is_checked_within_the_check_budget() {
    // Review 2 of rev 3, finding 1: the shadowed-stores lowering renders the
    // overwritten value on its own 4 MiB `raw` printer, which assembled every
    // `ite` level on the way back up past its budget before the check saw
    // the cost (d = 100: 165 MB charged, 286 MB peak RSS; d = 200: 245 MB,
    // 453 MB). `raw` is now built within the check's budget: it assembles
    // nothing past it and its exhaustion is the check's. The d = 0 control
    // renders; peak RSS is measured by running one test alone (DR).
    let mut terms = TermStore::new();
    let control = shadowed_store_probe(&mut terms, 0);
    let (renders, _) = render_derivation_within(
        &terms,
        None,
        &control,
        DERIVATION_RENDER_WORK_BUDGET,
        &mut || true,
    );
    assert_eq!(renders, DerivationRender::Renders);
    for depth in [100, 200] {
        let mut terms = TermStore::new();
        let derivation = shadowed_store_probe(&mut terms, depth);
        let (renders, work) = render_derivation_within(
            &terms,
            None,
            &derivation,
            DERIVATION_RENDER_WORK_BUDGET,
            &mut || true,
        );
        assert_eq!(renders, DerivationRender::OutOfBudget, "d = {depth}");
        assert!(
            work <= 2 * DERIVATION_RENDER_WORK_BUDGET + ONE_WRITE,
            "d = {depth}: the check charged {work} bytes"
        );
    }
}

#[test]
fn the_shadowed_store_lowering_is_unchanged_outside_a_check() {
    // The same `raw` sub-printer outside a renderability check is the one
    // origin/main built: an unbudgeted printer reaches the lowering exactly
    // as before (d = 3 renders either way).
    let mut terms = TermStore::new();
    let derivation = shadowed_store_probe(&mut terms, 3);
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, None);
    let text = printer
        .format_step(&derivation.steps[0], ProofId(0))
        .expect("renders outside a check");
    let (renders, _) = render_derivation_within(
        &terms,
        None,
        &derivation,
        DERIVATION_RENDER_WORK_BUDGET,
        &mut || true,
    );
    assert_eq!(renders, DerivationRender::Renders);
    assert!(text.contains(":rule arrays_ext"), "{text}");
}

/// `ROOT = (and (P t_depth) (= x 1.0))` over the doubling chain `t_depth`,
/// with `t_depth` printed as `tt` and ROOT as the flat `(and (Q tt) (= x
/// 1.0))`: the printed conjunct `(P tt)` is no printed operand, so the
/// `and_pos` bridges run down to (5), which compares the conjunct's
/// override-free rendering, the whole doubling TREE, against `(P tt)`.
fn equivalent_operand_probe(
    terms: &mut TermStore,
    depth: usize,
) -> (ProofStep, DetHashMap<TermId, String>) {
    let x = terms.mk_var("x", Sort::Real);
    let t = doubling_chain(terms, x, depth);
    let conjunct = terms.mk_app(Symbol::named("P"), vec![t], Sort::Bool);
    let one = terms.mk_rational(BigRational::from_integer(BigInt::from(1)));
    let second = eq(terms, x, one);
    let root = terms.mk_app(Symbol::named("and"), vec![conjunct, second], Sort::Bool);
    let mut overrides = DetHashMap::default();
    overrides.insert(t, "tt".to_string());
    overrides.insert(root, "(and (Q tt) (= x 1.0))".to_string());
    (and_pos_step(terms, root, 0, conjunct), overrides)
}

#[test]
fn the_and_pos_equivalence_bridge_renders_its_conjunct_within_the_check_budget() {
    // Review 2 of rev 3, finding 2: bridge (5) ran `render_term_canonical`
    // on a fresh unbudgeted printer, so a conjunct printed as `(P tt)`
    // expanded its whole tree (d = 26: 2^26 leaves, ~1 GB) inside a check.
    // Under a check that render is charged to the check now, and declined.
    for depth in [4, 26] {
        let mut terms = TermStore::new();
        let (step, overrides) = equivalent_operand_probe(&mut terms, depth);
        let derivation = CongruenceDerivation {
            clause: Vec::new(),
            steps: vec![step],
        };
        let (renders, work) = render_derivation_within(
            &terms,
            Some(&overrides),
            &derivation,
            DERIVATION_RENDER_WORK_BUDGET,
            &mut || true,
        );
        let expected = if depth == 4 {
            // Small: every bridge declines and the step is refused, as on
            // main.
            DerivationRender::Unrenderable
        } else {
            DerivationRender::OutOfBudget
        };
        assert_eq!(renders, expected, "d = {depth}");
        assert!(
            work <= 2 * DERIVATION_RENDER_WORK_BUDGET + ONE_WRITE,
            "d = {depth}: the check charged {work} bytes"
        );
    }
}
