// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::{eighty_stores, loaded, raw_root};
use super::*;

fn stored_read(executor: &Executor, root: TermId) -> TermId {
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        if let TermData::App(Symbol::Named(head), args) = executor.ctx.terms.get(term) {
            if head == "select"
                && args.len() == 2
                && matches!(
                    executor.ctx.terms.get(args[0]),
                    TermData::App(Symbol::Named(op), _) if op == "store"
                )
            {
                return term;
            }
        }
        pending.extend(ReadHints::children(&executor.ctx.terms, term).unwrap());
    }
    panic!("fixture must contain an actual stored-memory read")
}

#[test]
fn unresolved_store_reads_decline_before_any_arena_or_authority_mutation() {
    let unknown = format!(
        "(declare-const observe (_ BitVec 64)){}",
        eighty_stores(0).replace("(bvadd (bvsub base (_ bv80 64)) (_ bv80 64))", "observe",),
    );
    for source in [
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../ay-proof/src/alethe_printer/bv_packed/circuit/memory_fixtures/cell32.smt2"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../ay-proof/src/alethe_printer/bv_packed/circuit/memory_fixtures/cell64.smt2"
        )),
        unknown.as_str(),
    ] {
        let mut executor = loaded(source);
        let root = raw_root(&mut executor);
        let before = executor.ctx.terms.snapshot_stamp();
        let birth = executor.ctx.terms.entry_stamp(root);
        let metadata = executor.ctx.terms.checker_visible_metadata_generation();
        let fresh = executor.ctx.terms.var_counter();
        let scope = executor.ctx.source_context_stamp();
        assert!(executor.early_array_read_memory_candidate(root).is_none());
        assert_eq!(executor.ctx.terms.snapshot_stamp(), before);
        assert_eq!(executor.ctx.terms.entry_stamp(root), birth);
        assert_eq!(
            executor.ctx.terms.checker_visible_metadata_generation(),
            metadata
        );
        assert_eq!(executor.ctx.terms.var_counter(), fresh);
        assert_eq!(executor.ctx.source_context_stamp(), scope);
        assert!(executor.last_proof().is_none());
        assert!(executor.last_unsat_certificate.is_none());
        assert_eq!(
            executor.last_proof_raw_original_assertions,
            [] as [TermId; 0]
        );
        assert_eq!(executor.last_proof_rebuild_originals, [] as [TermId; 0]);
    }
}

#[test]
fn exact_original_read_hints_survive_only_append_only_live_epochs() {
    for invalidation in 0..4 {
        let mut executor = loaded(&eighty_stores(0));
        let root = raw_root(&mut executor);
        let read = stored_read(&executor, root);
        let mut visits = 0;
        let running = || false;
        let mut hints = ReadHints::preflight(&executor.ctx, root, &mut visits, &running).unwrap();
        assert!(hints
            .read(&executor.ctx, read, &mut visits, &running)
            .is_some());
        // Appending a nonsemantic constant preserves the original entries.
        let _ = executor.ctx.terms.mk_bitvec(999.into(), 64);
        assert!(hints
            .read(&executor.ctx, read, &mut visits, &running)
            .is_some());
        match invalidation {
            0 => executor.ctx.terms = executor.ctx.terms.clone(),
            1 => {
                executor
                    .execute_all(&ay_frontend::parse("(declare-const hint_epoch Bool)").unwrap())
                    .unwrap();
            }
            2 => executor.ctx.terms.mark_skolem_symbol("hint_metadata"),
            _ => {
                let checkpoint = executor.ctx.terms.rollback_checkpoint();
                let _ = executor.ctx.terms.mk_bitvec(1000.into(), 64);
                // No hint references this discarded suffix; the existing API
                // still retires the structural snapshot of the original cone.
                executor.ctx.terms.rollback_to(checkpoint);
            }
        }
        assert!(hints
            .read(&executor.ctx, read, &mut visits, &running)
            .is_none());
    }
}

#[test]
fn cached_read_hints_cannot_bypass_live_stop_or_existing_work_allowance() {
    let mut executor = loaded(&eighty_stores(0));
    let root = raw_root(&mut executor);
    let read = stored_read(&executor, root);
    let mut visits = 0;
    let running = || false;
    let mut hints = ReadHints::preflight(&executor.ctx, root, &mut visits, &running).unwrap();
    assert!(hints
        .read(&executor.ctx, read, &mut visits, &running)
        .is_some());
    assert!(hints
        .read(&executor.ctx, read, &mut visits, &|| true)
        .is_none());
    visits = MAX_VISITS;
    assert!(hints
        .read(&executor.ctx, read, &mut visits, &running)
        .is_none());
}
