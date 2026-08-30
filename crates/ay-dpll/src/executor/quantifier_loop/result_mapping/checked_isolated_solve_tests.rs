// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arena-prune pins for the checked probe's isolated context.

#![allow(clippy::panic)]

use super::*;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermStore};
use ay_frontend::parse;

/// A datatype, a declared-but-unasserted constant, and one tiny assertion —
/// then a pile of arena SCRATCH of the shape an enclosing solve leaves behind
/// (instances, bridge nodes): interned, reachable from no assertion, named by
/// nothing.
fn scratch_laden_executor() -> (Executor, Vec<TermId>) {
    let commands = parse(
        r#"
        (set-logic ALL)
        (declare-datatypes ((PruneList 0))
          (((PruneCons (prune_hd Int) (prune_tl PruneList)) (PruneNil))))
        (declare-const prune_a Int)
        (declare-const prune_b Int)
        (declare-const prune_unused Int)
        (assert (= prune_a prune_b))
    "#,
    )
    .expect("prune fixture parses");
    let mut executor = Executor::new();
    assert!(executor
        .execute_all(&commands)
        .expect("prune fixture executes")
        .is_empty());
    let roots = executor.ctx.assertions.clone();
    assert_eq!(roots.len(), 1, "the fixture asserts exactly one root");
    let a = executor.ctx.terms.mk_var("prune_a", Sort::Int);
    let b = executor.ctx.terms.mk_var("prune_b", Sort::Int);
    for index in 0..SCRATCH_NODES {
        let scratch = executor.ctx.terms.mk_app(
            Symbol::named(format!("prune_scratch_{index}")),
            [a, b],
            Sort::Bool,
        );
        let _negated = executor.ctx.terms.mk_not_raw(scratch);
    }
    (executor, roots)
}

/// Scratch applications interned per fixture; each also gets a negation, so the
/// fixture adds `2 * SCRATCH_NODES` unnamed arena entries.
const SCRATCH_NODES: usize = 256;

/// Every id in the arena whose head is `Var(name, _)` or a nullary
/// `App(name, [])`. Scans the arena itself rather than any side index, so a
/// term pinned only by a side index cannot make this answer non-empty.
fn arena_terms_named(store: &TermStore, name: &str) -> Vec<TermId> {
    (0..store.len())
        .map(|index| TermId(u32::try_from(index).expect("arena index fits u32")))
        .filter(|&id| match store.get(id) {
            TermData::Var(spelling, _) => spelling == name,
            TermData::App(Symbol::Named(spelling), args) => spelling == name && args.is_empty(),
            _ => false,
        })
        .collect()
}

/// The DELIBERATELY TOO-AGGRESSIVE rule this pruning must not be: mark only
/// from the probe's roots over the real term DAG, pinning nothing else.
fn reachable_from_roots_only(store: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    let mut seen: Vec<TermId> = Vec::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(id) = stack.pop() {
        if id.is_sentinel() || seen.contains(&id) {
            continue;
        }
        seen.push(id);
        match store.get(id) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, term)| *term));
                stack.push(*body);
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(cond, then_branch, else_branch) => {
                stack.extend([*cond, *then_branch, *else_branch]);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            // `TermData` is `#[non_exhaustive]` outside `ay-core`. A new shape
            // must be given children here before this reference rule can claim
            // to under-approximate anything.
            other => panic!("reference roots-only walk does not handle {other:?}"),
        }
    }
    seen
}

/// THE NEGATIVE. A declared-but-unasserted constant and a nullary datatype
/// constructor are both unreachable from the probe's roots — a rule that marked
/// from the roots alone would reclaim them, and the probe would then be unable
/// to name symbols its own declarations still promise. The rule actually used
/// marks from every `TermId` the context holds plus the store's own pins, so
/// both survive.
#[test]
fn pruned_probe_context_keeps_what_a_roots_only_rule_would_drop() {
    let (executor, roots) = scratch_laden_executor();

    let unused = arena_terms_named(&executor.ctx.terms, "prune_unused");
    let nil = arena_terms_named(&executor.ctx.terms, "PruneNil");
    assert_eq!(unused.len(), 1, "the fixture interns `prune_unused` once");
    assert_eq!(nil.len(), 1, "the fixture interns `PruneNil` once");

    // The negative is only meaningful if the too-aggressive rule really would
    // drop these two.
    let roots_only = reachable_from_roots_only(&executor.ctx.terms, &roots);
    assert!(
        !roots_only.contains(&unused[0]),
        "a roots-only rule must be shown to drop `prune_unused`, else this test proves nothing"
    );
    assert!(
        !roots_only.contains(&nil[0]),
        "a roots-only rule must be shown to drop `PruneNil`, else this test proves nothing"
    );

    let pruned = executor
        .pruned_isolated_probe_context(&roots)
        .expect("the probe context builds");
    assert_eq!(
        arena_terms_named(&pruned.terms, "prune_unused").len(),
        1,
        "the declared-but-unasserted constant must survive the prune"
    );
    assert_eq!(
        arena_terms_named(&pruned.terms, "PruneNil").len(),
        1,
        "the nullary datatype constructor must survive the prune"
    );
}

/// The prune reclaims the enclosing solve's unnamed scratch and leaves the
/// probe's own query identical in shape.
#[test]
fn pruned_probe_context_reclaims_scratch_and_preserves_the_roots() {
    let (executor, roots) = scratch_laden_executor();
    let before = executor.ctx.terms.len();

    let pruned = executor
        .pruned_isolated_probe_context(&roots)
        .expect("the probe context builds");

    assert!(
        pruned.terms.len() + 2 * SCRATCH_NODES <= before,
        "the {} scratch nodes must be reclaimed: {before} -> {}",
        2 * SCRATCH_NODES,
        pruned.terms.len()
    );
    for index in 0..SCRATCH_NODES {
        let name = format!("prune_scratch_{index}");
        assert!(
            pruned.terms.find_app_named(&name, &[]).is_none(),
            "scratch node {index} must not survive under its own head symbol"
        );
    }
    assert_eq!(
        pruned.assertions.len(),
        roots.len(),
        "the probe keeps exactly its installed roots"
    );
    let TermData::App(Symbol::Named(head), args) = pruned.terms.get(pruned.assertions[0]) else {
        panic!("the installed root must still be an application");
    };
    assert_eq!(head, "=", "the root's head symbol is unchanged");
    assert_eq!(args.len(), 2, "the root's arity is unchanged");
    let spellings = args
        .iter()
        .map(|&arg| match pruned.terms.get(arg) {
            TermData::Var(name, _) => name.clone(),
            other => panic!("root argument became {other:?}"),
        })
        .collect::<Vec<_>>();
    assert_eq!(
        spellings,
        vec!["prune_a".to_string(), "prune_b".to_string()],
        "the root's arguments are the same two constants"
    );
}

/// The witness-value probe is deliberately NOT pruned: it evaluates
/// enclosing-store ids against the probe's model, so a relabelled arena would
/// read them as different terms. Its context must stay id-compatible with the
/// enclosing one.
#[test]
fn unpruned_probe_context_keeps_enclosing_term_ids() {
    let (executor, roots) = scratch_laden_executor();
    let before = executor.ctx.terms.len();
    let unpruned = executor
        .isolated_probe_context(&roots)
        .expect("the probe context builds");
    assert_eq!(
        unpruned.terms.len(),
        before,
        "the unpruned probe context keeps every id the enclosing store had"
    );
    assert_eq!(
        unpruned.assertions, roots,
        "and the roots keep their enclosing-store ids"
    );
}

/// THE SECOND NEGATIVE, and the one that was measured rather than imagined: a
/// term whose IDENTITY is spelled inside another symbol's NAME. The
/// mod/div-elimination pass mints `__ay_zerodiv_{op}_{dividend index}` and
/// `collect_zero_divisor_vars` parses that index straight back into a
/// `TermId`, so relabelling the arena makes the name denote a different term
/// or none. No `TermId` walk can see that holder — it is a string. Pruning
/// must therefore refuse the whole context.
#[test]
fn probe_context_is_not_pruned_when_a_symbol_name_spells_a_term_id() {
    let (mut executor, roots) = scratch_laden_executor();
    let dividend = executor.ctx.terms.mk_var("prune_a", Sort::Int);
    let smuggler = format!("__ay_zerodiv_div_{}", dividend.index());
    let _var = executor.ctx.terms.mk_var(smuggler.clone(), Sort::Int);
    let before = executor.ctx.terms.len();

    let probe_ctx = executor
        .pruned_isolated_probe_context(&roots)
        .expect("the probe context builds");

    assert_eq!(
        probe_ctx.terms.len(),
        before,
        "a store whose symbol names spell TermIds must be handed to the probe \
         UNPRUNED; pruning it relabels the arena out from under `{smuggler}`"
    );
    assert_eq!(
        probe_ctx.assertions, roots,
        "the unpruned fallback keeps the enclosing store's ids"
    );
}

/// The veto is a property of the NAME, not of the marker: an AY-internal symbol
/// with no digits in it cannot be spelling a `TermId`, so it does not stop the
/// prune. This pins the shape the `inc_some_list` probe actually carries —
/// `__ay_dt_depth_List`, its only internal symbol — because a veto that fired
/// on that would silently give the whole prune back.
#[test]
fn a_digit_free_internal_symbol_does_not_veto_the_prune() {
    let (mut executor, roots) = scratch_laden_executor();
    let _depth = executor
        .ctx
        .terms
        .mk_var("__ay_dt_depth_PruneList", Sort::Int);
    let before = executor.ctx.terms.len();

    let probe_ctx = executor
        .pruned_isolated_probe_context(&roots)
        .expect("the probe context builds");

    assert!(
        probe_ctx.terms.len() + 2 * SCRATCH_NODES <= before,
        "a digit-free internal symbol must not veto pruning: {before} -> {}",
        probe_ctx.terms.len()
    );
}

/// The RoundingMode branch image the finite-domain expansion hands this probe,
/// with the RM-literal equality left UNFOLDED — the shape a producer that
/// forgets `rm_literal_atom_folds` (or any other substituting pass) yields.
///
/// It is a regression pin for the probe/top-level ASYMMETRY that was reported
/// and does not exist: measured at c8a7afd54, the probe and a fresh top-level
/// `check_sat` return the SAME verdict on this exact root vector, and both
/// returned `Unknown`. The cause was never a probe environment that loses the
/// Pass-B axioms — `rm_domain_axioms` produces the identical distinct-5 axiom
/// on both sides — but that neither side's axiom NAMED the substitution-built
/// atom. See `executor::rm_domain::RmLiteralAtoms`.
///
/// # Why an unconstrained RM atom could not publish a wrong `sat`
///
/// The residual this closes was a RELAXATION (an atom no axiom names), so the
/// lane's `unsat` stayed sound and only its `sat` could be wrong. That a wrong
/// probe `sat` cannot cross [`Executor::checked_isolated_solve`] is a claim
/// about SAT-certificate MINTING, and `GroundDecision` accepts a certificate
/// from ANY lane — `SatCertificate::confirms_sat_emission` is exhaustive over
/// all three kinds — so naming only the ordinary funnel is not a proof. There
/// are FOUR minting sites in non-test code, all in `model/sat_emit.rs`
/// (`last_sat_certificate = Some(..)`; the other two occurrences in that file
/// are `#[cfg(test)]`), and each needs its own permit:
///
/// 1. `emit_sat_verdict`, VACUOUS arm — guarded by
///    `self.ctx.assertions.is_empty() && roots.is_empty()`. With no assertions
///    and no roots there is no RM atom in the DAG at all, so `rm_domain_axioms`
///    returns `NoMention` and this pass contributes nothing to reach it.
/// 2. `emit_sat_verdict`, TERMINAL arm — mints only when `gated == Sat`, i.e.
///    after `apply_independent_model_gate` returns `ConfirmedSat` over
///    `independent_gate_query_roots`. Those are the probe's own installed
///    roots: the Pass-B axioms are scope-transient and restored before
///    emission, so the gate judges the query, not the axiom set. A model that
///    violates a free RM atom fails there — MEASURED twice, as
///    `MODEL-UNCONFIRMED ... Assertion N violated`, both times degrading to
///    `unknown` rather than publishing.
/// 3. `emit_checked_projection_sat` and
/// 4. `emit_checked_exact_exists_sat` — both live inside
///    `check_sat_guarded`'s `if let Some(permit) = projection_authority`
///    block. A probe enters through `Executor::check_sat`, which passes `None`
///    and, by its own contract, "cannot infer authority from call depth or
///    assertion shape". So neither lane is reachable from a probe at all, which
///    `a_probe_route_solve_carries_no_projection_authority` pins.
///
/// A fifth minting site added later would NOT inherit any of these permits.
mod rm_literal_atom_probe {
    use super::*;

    const RM_BRANCH_SCRIPT: &str = "(declare-const rm RoundingMode) \
         (assert (= (fp.roundToIntegral rm ((_ to_fp 8 24) RNE 2.5)) ((_ to_fp 8 24) RNE 2.0))) \
         (assert (= rm roundTowardPositive))";

    fn branch_image(executor: &mut Executor) -> Vec<TermId> {
        let roots = executor.ctx.assertions.clone();
        let rtn = crate::executor::rm_domain::rm_literal_term(
            &mut executor.ctx.terms,
            ay_fp::RoundingMode::RTN,
        );
        let variable = (0..executor.ctx.terms.len())
            .map(|index| TermId(u32::try_from(index).expect("arena index fits u32")))
            .find(
                |&id| matches!(executor.ctx.terms.get(id), TermData::Var(name, _) if name == "rm"),
            )
            .expect("the fixture declares `rm`");
        let mut map = ay_core::kani_compat::DetHashMap::default();
        map.insert(variable, rtn);
        roots
            .iter()
            .map(|&root| executor.ctx.terms.substitute_terms(root, &map))
            .collect()
    }

    fn branch_executor() -> (Executor, Vec<TermId>) {
        let commands = parse(RM_BRANCH_SCRIPT).expect("RM branch fixture parses");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("RM branch fixture executes");
        let image = branch_image(&mut executor);
        (executor, image)
    }

    /// The UNSAT-only probe decides the branch.
    #[test]
    fn exact_unsat_probe_refutes_the_substituted_rm_branch() {
        let (mut executor, image) = branch_executor();
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let outcome = executor
            .checked_isolated_solve(image.clone(), CheckedIsolatedMode::ExactUnsat, 5_000)
            .map(|(_, kind)| kind);
        assert!(
            matches!(outcome, Some(CheckedGroundKind::Unsat)),
            "the exact-UNSAT probe must refute the branch, got {outcome:?}"
        );
    }

    /// ...and so does the ground-decision probe, which is the one whose `Sat`
    /// arm carries authority.
    #[test]
    fn ground_decision_probe_refutes_the_substituted_rm_branch() {
        let (mut executor, image) = branch_executor();
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let outcome = executor
            .checked_isolated_solve(image.clone(), CheckedIsolatedMode::GroundDecision, 5_000)
            .map(|(_, kind)| kind);
        assert!(
            matches!(outcome, Some(CheckedGroundKind::Unsat)),
            "the ground-decision probe must refute the branch, got {outcome:?}"
        );
    }

    /// The permit half of the four-site argument in this module's docs: the
    /// route a probe takes into `check_sat_guarded` carries NO
    /// `AuthoredPlainHardQueryPermit`, so `emit_checked_projection_sat` and
    /// `emit_checked_exact_exists_sat` — the two SAT-certificate lanes that do
    /// not run the independent model gate — are unreachable behind it.
    #[test]
    fn a_probe_route_solve_carries_no_projection_authority() {
        let (executor, image) = branch_executor();
        let mut top = Executor::new();
        top.ctx = executor.ctx.clone();
        top.ctx
            .process_command(&ay_frontend::Command::ResetAssertions)
            .expect("the derived query resets the outer assertions");
        for &root in &image {
            top.ctx.add_assertion_with_parsed(
                root,
                ay_frontend::command::Term::Symbol(NATIVE_API_ASSERTION_PLACEHOLDER.to_string()),
            );
        }
        top.begin_public_solve(false);
        top.bind_unsat_query_assumptions(&[]);
        let _ = top.check_sat().expect("the solve completes");
        assert!(
            !top.last_authored_query_authority_seen,
            "`Executor::check_sat` must reach the solve with no projection permit"
        );
    }

    /// THE ASYMMETRY CLAIM, PINNED. A fresh top-level `check_sat` over exactly
    /// the probe's root vector must agree with the probe. This is what makes
    /// "the probe environment loses something the top level has" a falsifiable
    /// statement rather than a diagnosis: if a future change gives the probe a
    /// weaker environment than the top level, these two verdicts diverge here.
    #[test]
    fn the_probe_and_a_fresh_top_level_solve_agree_on_the_branch() {
        let (executor, image) = branch_executor();

        let mut top = Executor::new();
        top.ctx = executor.ctx.clone();
        top.ctx
            .process_command(&ay_frontend::Command::ResetAssertions)
            .expect("the derived query resets the outer assertions");
        for &root in &image {
            top.ctx.add_assertion_with_parsed(
                root,
                ay_frontend::command::Term::Symbol(NATIVE_API_ASSERTION_PLACEHOLDER.to_string()),
            );
        }
        top.begin_public_solve(false);
        top.bind_unsat_query_assumptions(&[]);
        let verdict = top.check_sat().expect("the top-level solve completes");
        assert!(
            verdict.is_unsat(),
            "a fresh top-level solve over the probe's own roots must reach the \
             same verdict the probe does, got {verdict:?}"
        );
    }
}
