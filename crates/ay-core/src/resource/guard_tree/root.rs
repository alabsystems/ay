// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The root of the GuardTree (the development design notes §2 and §3, step
//! S1): the process.
//!
//! The process-wide pieces are the root's storage. Its flag is the process
//! cancel, its ledger the process work ledger, and its memory the process
//! budget, whose bytes stay in ay-sys (`node::Memory::Process`). The two
//! statics stay statics, so `cancel_process`, `process_cancelled` and
//! `work` keep their meaning and their cost: one store, one relaxed load,
//! one address. The root has no deadline, no count and no CPU slice of its
//! own. The CLI's watchdogs end a run by raising its flag, as before.

use std::sync::atomic::AtomicBool;

use super::node::Node;
use crate::resource::WorkLedger;

/// The root's flag: the process-wide cancel, raised by the CLI when the
/// run's deadline passes, its memory budget is breached, or it is told to
/// terminate.
pub(crate) static PROCESS_CANCEL: AtomicBool = AtomicBool::new(false);

/// The root's ledger: the process-wide work ledger. Every node's ledger adds
/// into it (GT5), and the CLI watchdog reads it.
pub(crate) static WORK: WorkLedger = WorkLedger::new();

/// The root node over them. No `Guard` holds it; every node built with
/// `Guard::root_child` hangs from it.
pub(super) static ROOT: Node = Node::root();

#[cfg(test)]
mod tests {
    use std::sync::atomic::Ordering;

    use super::*;
    use crate::resource::guard_tree::{ChildSpec, Guard, NodeLabel, TICKS_PER_CLOCK_READ};
    use crate::resource::{process_cancelled, work, WorkSnapshot};

    #[test]
    fn the_root_is_the_process_wide_storage() {
        assert_eq!(ROOT.label, NodeLabel::Root);
        assert!(ROOT.up().is_none());
        assert!(std::ptr::eq(ROOT.cancel.get(), &raw const PROCESS_CANCEL));
        let ledger: &WorkLedger = &ROOT.ledger;
        assert!(std::ptr::eq(ledger, work()));
        assert_eq!(
            process_cancelled(),
            ROOT.cancel.get().load(Ordering::Relaxed)
        );
        let top = Guard::new();
        assert!(top
            .node
            .up()
            .is_some_and(|up| std::ptr::eq(up, &raw const ROOT)));
        let below = top.child(ChildSpec::new(NodeLabel::Search));
        assert!(below
            .node
            .ancestors()
            .last()
            .is_some_and(|up| std::ptr::eq(up, &raw const ROOT)));
    }

    #[test]
    fn a_nodes_work_reaches_the_process_ledger() {
        let ticks = WORK.ticks();
        let before = work().snapshot();
        let check = Guard::new();
        let lane = check.child(ChildSpec::new(NodeLabel::Search));
        lane.tick(TICKS_PER_CLOCK_READ).expect("no limit is set");
        lane.record_work(&WorkSnapshot {
            sat_conflicts: 2,
            ..WorkSnapshot::default()
        });
        // Other tests in this process may add work concurrently: at least
        // ours, unless one of them saturated the count.
        let now = WORK.ticks();
        assert!(now == u64::MAX || now - ticks >= TICKS_PER_CLOCK_READ);
        assert!(work().snapshot().since(before).sat_conflicts >= 2);
        assert_eq!(check.ledger_ticks(), TICKS_PER_CLOCK_READ);
    }
}
