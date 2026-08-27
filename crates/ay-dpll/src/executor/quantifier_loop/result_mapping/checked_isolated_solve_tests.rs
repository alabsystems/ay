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
