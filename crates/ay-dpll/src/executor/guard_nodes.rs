// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The executor's GuardTree nodes (the development design notes §3, steps S2
//! and S3).
//!
//! Every check-sat runs in a Check node, entered on the solving thread for
//! the check's extent (GT4). Its external flag is the executor's interrupt,
//! its deadline the executor's solve deadline read live, and its memory the
//! share of the portfolio lane the polling thread runs in: what the stop the
//! executor installed before S2 (`make_should_stop`) read. A loop deep inside
//! a theory, with no handle on the executor, polls it through
//! `ay_core::resource::check_stop_requested`. Work reported while the check
//! runs is charged to the node (GT5), so its ledger is the check's work.
//!
//! A nested check-sat is a `Full` child of the node it runs in: it obeys
//! the deadline and the interrupt of every check around it, and draws on
//! every work cap around it (DR-39's default). Before S2 it replaced the
//! stop of the check around it and was chained to nothing (§1.3). Under a
//! Certify node a check sees the cancels above Certify but not their
//! deadlines (DR-39; `api/proofs/certification_effort.rs`). A check of an
//! executor armed for a certification (`arm_certification_grant`) is a
//! child of that certification's Certify node while the thread runs above
//! it: in no node, or in Certify or an ancestor of it. Inside Certify, or
//! beside it in a node entered after Certify was built, the check hangs
//! where the thread runs (`open_check_node`).
//!
//! A deadline slicer's half (GT6, step S3) is a Share node: a `Full` child
//! of the node the slicer runs in, entered for the attempt, with a deadline
//! cell of its own that the executor's deadline view reads and writes while
//! the share is open (`solve_deadline.rs`). The slicer never writes the
//! executor's deadline, and the share counts itself: `deadline_shares` when
//! it opens, `deadline_shares_spent` when it closes spent.

use std::sync::Arc;

use ay_core::resource::{
    current_guard, ChildSpec, DeadlineSource, EnterScope, Guard, NodeLabel, Portion,
};

use super::solve_deadline::OpenShare;
use super::Executor;

/// What a deadline share takes from the executor ([`Executor::open_deadline_share`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum ShareOf {
    /// The solve deadline alone: the certification deadline, the
    /// publication boundary, is untouched (the RDL and DT lazy lanes).
    Search,
    /// The solve deadline, and the certification deadline no later than
    /// the share's: the attempt's solve and its certification both run on
    /// the share (a fallback-chain attempt).
    SearchAndCertification,
}

/// An open deadline share; dropping it closes the share (GT6).
#[must_use = "the deadline share closes when this is dropped"]
pub(in crate::executor) struct DeadlineShare {
    _solve: Option<OpenShare>,
    _certification: Option<OpenShare>,
    _inside: EnterScope,
}

impl Executor {
    /// The node of a check-sat about to run on this thread: a `Full` child
    /// of the thread's current node, or of the root on a thread in none. Its
    /// deadline is the cell the executor's deadline view reads now: a share
    /// open around the call (a fallback-chain attempt's) is the deadline
    /// every write of this call moves, so the node reads what
    /// `make_should_stop` reads.
    ///
    /// An executor armed for a certification hangs its check from that
    /// certification's Certify node instead, while it is open and the thread
    /// runs above it: in no node, or in Certify or one of its ancestors.
    /// Inside Certify (a nested call of its own) the check hangs where the
    /// thread runs; so it does beside Certify, in a node entered after
    /// Certify was built (a ceiling, a grant, a share), whose limits the
    /// check must not escape.
    pub(super) fn open_check_node(&self) -> Guard {
        let spec = ChildSpec::new(NodeLabel::Check)
            .with_deadline(DeadlineSource::Live(self.solve_deadline.current()))
            .with_lane_share();
        let spec = match &self.solve_interrupt {
            Some(flag) => spec.with_external(Arc::clone(flag)),
            None => spec,
        };
        let current = current_guard();
        let parent = match self.certification_parent.upgrade() {
            Some(certify) if current.as_ref().is_none_or(|node| certify.is_within(node)) => {
                Some(certify)
            }
            _ => current,
        };
        match parent {
            Some(parent) => parent.child(spec),
            None => Guard::root_child(spec),
        }
    }

    /// Run every check-sat of this executor under `certify` (DR-39: a
    /// nested certification check is a `Full` child of its Certify node);
    /// `None` restores the default, the node the check runs in. The executor
    /// holds it weakly: the certification that armed it (its envelope, its
    /// assembly) keeps it open, and once that is done the executor's checks
    /// hang where they run, and keep no node above them open.
    pub(crate) fn set_certification_parent(&mut self, certify: Option<Guard>) {
        self.certification_parent = certify.as_ref().map(Guard::downgrade).unwrap_or_default();
    }

    /// The Certify node proof assembly runs in and polls (DR-39: Certify
    /// covers proof assembly): the executor's interrupt, the certification
    /// envelope read live (an open share's, when one is), and the lane share.
    pub(super) fn proof_assembly_certify_node(&self) -> Guard {
        crate::api::proofs::certify_node(
            self.solve_interrupt.clone(),
            DeadlineSource::Live(self.certification_deadline.current()),
        )
    }

    /// Open a share of half the time left before the executor's deadline
    /// (GT6, step S3): a Share node below the thread's current node (the
    /// root's on a thread in none), entered until the returned scope drops,
    /// whose own cell is the executor's deadline meanwhile. `None` when
    /// there is nothing to divide. Under a tick budget the share takes half
    /// the ticks left instead and leaves the deadline whole (DR-38 rule 7).
    pub(in crate::executor) fn open_deadline_share(&self, of: ShareOf) -> Option<DeadlineShare> {
        let parent = current_guard();
        // Under a tick budget the share is a tick share, and DR-38 rule 7
        // leaves the deadlines whole: this executor's would not be halved,
        // and a fallback attempt's certification deadline not narrowed. No
        // check has a tick budget before S6, which decides what the slicers
        // do then (guard-tree.md §12).
        debug_assert!(
            parent.as_ref().and_then(Guard::remaining).is_none(),
            "a deadline share under a tick budget is S6's (DR-38 rule 7)"
        );
        let share = Guard::share_of(parent.as_ref(), Portion::Half, self.solve_deadline.get())?;
        let cell = share.live_deadline();
        let certification = match (of, cell.as_ref().and_then(|cell| cell.get())) {
            (ShareOf::SearchAndCertification, Some(narrowed)) => {
                let envelope = self
                    .certification_deadline
                    .get()
                    .map_or(narrowed, |cert| cert.min(narrowed));
                let envelope = ay_core::resource::LiveDeadline::new(Some(envelope));
                Some(self.certification_deadline.open_share(envelope))
            }
            _ => None,
        };
        Some(DeadlineShare {
            _solve: cell.map(|cell| self.solve_deadline.open_share(cell)),
            _certification: certification,
            _inside: share.enter(),
        })
    }

    /// End a lazy lane's attempt (RDL's, DT's): close the share it opened,
    /// or, when it opened none (no deadline, or nothing left to divide), put
    /// back the deadline it `found`, as every such slicer did before S3. A
    /// write inside the attempt that does not restore itself
    /// (`eq_qe_bound_legacy_refutation` narrows the rest of its check-sat)
    /// moves an open share's cell and closes with it; with no share it moves
    /// the executor's own, and must not outlive the attempt.
    pub(in crate::executor) fn end_sliced_attempt(
        &self,
        share: Option<DeadlineShare>,
        found: Option<ay_core::time::Instant>,
    ) {
        match share {
            Some(share) => drop(share),
            None => self.solve_deadline.set(found),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;
    use std::time::Duration;

    use ay_core::resource::{Exhausted, NodeLabel};
    use ay_core::time::Instant;

    use super::Executor;

    const HOUR: Duration = Duration::from_secs(3600);

    #[test]
    fn a_check_node_reads_the_interrupt_and_the_live_deadline() {
        let interrupt = Arc::new(AtomicBool::new(false));
        let mut exec = Executor::new();
        exec.set_solve_controls(Some(Arc::clone(&interrupt)), Some(Instant::now() + HOUR));
        let check = exec.open_check_node();
        assert_eq!(check.label(), NodeLabel::Check);
        assert_eq!(check.poll(), None);
        exec.solve_deadline.set(Some(Instant::now()));
        assert_eq!(check.poll(), Some(Exhausted::Deadline), "read live");
        exec.solve_deadline.set(Some(Instant::now() + HOUR));
        assert_eq!(check.poll(), None, "a restore is read too");
        interrupt.store(true, Ordering::Relaxed);
        assert_eq!(check.poll(), Some(Exhausted::Cancelled));
    }

    #[test]
    fn a_nested_check_is_chained_to_the_check_it_runs_in() {
        let mut outer = Executor::new();
        outer.set_solve_controls(None, Some(Instant::now() + HOUR));
        let check = outer.open_check_node();
        let _in_check = check.enter();
        let nested = Executor::new().open_check_node();
        assert!(nested.is_within(&check));
        outer.solve_deadline.set(Some(Instant::now()));
        assert!(nested.poll().is_some(), "the outer deadline reaches it");
    }

    #[test]
    fn an_armed_executors_checks_run_under_its_certify_node() {
        let mut outer = Executor::new();
        outer.set_solve_controls(None, Some(Instant::now() + HOUR));
        outer.solve_deadline.set(Some(Instant::now()));
        let search = outer.open_check_node();
        let _in_search = search.enter();
        let certify = outer.proof_assembly_certify_node();
        assert!(certify.is_within(&search));
        let mut nested = Executor::new();
        nested.arm_certification_grant(10, 10, None, None, Some(certify.clone()));
        let check = nested.open_check_node();
        assert!(check.is_within(&certify));
        assert_eq!(
            check.poll(),
            None,
            "under Certify, the passed search deadline does not reach it"
        );
        let _in_check = check.enter();
        assert!(
            nested.open_check_node().is_within(&check),
            "a nested call of its own stays inside its check"
        );
    }

    #[test]
    fn an_armed_executors_check_hangs_from_its_certify_only_from_above_it() {
        use ay_core::resource::{enter_work_ceiling, ChildSpec, DeadlineSource, Guard};

        let mut nested = Executor::new();
        let certify = crate::api::proofs::certify_node(None, DeadlineSource::None);
        nested.arm_certification_grant(10, 10, None, None, Some(certify.clone()));
        assert!(
            nested.open_check_node().is_within(&certify),
            "from a thread in no node"
        );

        let search = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        let _in_search = search.enter();
        let certify = crate::api::proofs::certify_node(None, DeadlineSource::None);
        nested.arm_certification_grant(10, 10, None, None, Some(certify.clone()));
        assert!(
            nested.open_check_node().is_within(&certify),
            "from an ancestor of Certify"
        );
        let ceiling = enter_work_ceiling(Some(1_000));
        let beside = nested.open_check_node();
        assert!(
            !beside.is_within(&certify),
            "a node entered after Certify was built is not escaped"
        );
        assert!(beside.nearest(NodeLabel::Ceiling).is_some());
        drop(beside);
        drop(ceiling);
    }

    #[test]
    fn an_armed_executor_keeps_no_certify_node_open() {
        use ay_core::resource::DeadlineSource;

        let certify = crate::api::proofs::certify_node(None, DeadlineSource::None);
        let watch = certify.downgrade();
        let mut exec = Executor::new();
        exec.arm_certification_grant(10, 10, None, None, Some(certify.clone()));
        exec.reset();
        assert!(
            exec.open_check_node().is_within(&certify),
            "carried across a reset while its certification is open"
        );
        drop(certify);
        assert!(
            watch.upgrade().is_none(),
            "the executor does not keep it open"
        );
        assert!(
            exec.open_check_node().nearest(NodeLabel::Certify).is_none(),
            "its checks hang where they run"
        );
    }

    #[test]
    fn a_check_opened_inside_a_share_reads_the_cell_its_writes_move() {
        use super::ShareOf;
        use ay_core::resource::{ChildSpec, Guard};

        let mut exec = Executor::new();
        exec.set_solve_controls(None, Some(Instant::now() + HOUR));
        let outer = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        let _in_outer = outer.enter();
        let _share = exec
            .open_deadline_share(ShareOf::SearchAndCertification)
            .expect("there is time to divide");
        let check = exec.open_check_node();
        exec.solve_deadline.set(Some(Instant::now()));
        assert_eq!(
            check.poll(),
            Some(Exhausted::Deadline),
            "the check reads the share's cell, which the write moved"
        );
        exec.solve_deadline.set(Some(Instant::now() + HOUR / 4));
        assert_eq!(check.poll(), None, "and a restore of it");
        // The two asserts above hold through the Share around the check,
        // whichever cell the check reads; only this one tells them apart.
        exec.solve_deadline.live().set(Some(Instant::now()));
        assert_eq!(
            check.poll(),
            None,
            "the check does not read the executor's own cell"
        );
    }

    /// End to end: the solve polls its deadline inside its Check node, the
    /// RDL attempt (a deadline slicer) inside a Share below it, and while the
    /// share is open the executor's own deadline is never written.
    #[test]
    fn check_sat_runs_in_its_check_node_and_its_share_leaves_the_own_deadline_alone() {
        use std::cell::RefCell;
        use std::rc::Rc;

        use ay_core::resource::{current_guard, Guard};

        #[derive(Clone, Copy, Debug)]
        struct Seen {
            shares: usize,
            own_writes: u64,
            current: Option<NodeLabel>,
            in_check: bool,
        }
        let solve = |exec: &mut Executor, script: &str| -> (String, Vec<Seen>) {
            let seen = Rc::new(RefCell::new(Vec::new()));
            let log = Rc::clone(&seen);
            let cmds = ay_frontend::parse(script).expect("parse");
            let outputs = super::super::solve_deadline::watch_for_testing(
                move |shares, own| {
                    let current = current_guard();
                    log.borrow_mut().push(Seen {
                        shares,
                        own_writes: own.generation(),
                        current: current.as_ref().map(Guard::label),
                        in_check: current
                            .as_ref()
                            .is_some_and(|node| node.nearest(NodeLabel::Check).is_some()),
                    });
                },
                || exec.execute_all(&cmds).expect("execute"),
            );
            let verdict = outputs
                .into_iter()
                .rfind(|out| matches!(out.trim(), "sat" | "unsat" | "unknown"))
                .expect("a verdict");
            let seen = seen.borrow().clone();
            (verdict.trim().to_string(), seen)
        };

        let mut exec = Executor::new();
        let (verdict, seen) = solve(
            &mut exec,
            "(set-logic QF_RDL)
             (declare-fun x () Real)
             (declare-fun y () Real)
             (declare-fun z () Real)
             (assert (or (<= (- x y) (- 3)) (>= (- x y) 3)))
             (assert (< (- y z) 2))
             (assert (<= (- z x) 5))
             (check-sat)",
        );
        assert_eq!(verdict, "sat");
        assert!(
            seen.iter()
                .any(|at| at.current == Some(NodeLabel::Check) && at.shares == 0),
            "the solve polls its deadline in its Check node: {seen:?}"
        );
        assert!(
            seen.iter()
                .any(|at| at.current == Some(NodeLabel::Share) && at.in_check && at.shares == 1),
            "the RDL attempt polls it in a Share below the Check: {seen:?}"
        );
        for pair in seen.windows(2) {
            if pair[0].shares > 0 && pair[1].shares > 0 {
                assert_eq!(
                    pair[0].own_writes, pair[1].own_writes,
                    "the executor's own deadline is written while a share is open"
                );
            }
        }
        assert_eq!(
            exec.statistics().get_int("all_lanes.deadline_shares"),
            Some(1)
        );

        let (verdict, seen) = solve(
            &mut Executor::new(),
            "(set-logic QF_LIA)
             (declare-fun x () Int)
             (declare-fun p () Bool)
             (assert (=> p (> x 2)))
             (assert (< x 5))
             (check-sat-assuming (p))",
        );
        assert_eq!(verdict, "sat");
        assert!(
            seen.iter().any(|at| at.in_check),
            "check-sat-assuming polls its deadline in its Check node: {seen:?}"
        );
    }

    #[test]
    fn a_deadline_share_is_the_executors_deadline_while_open_and_counts_itself() {
        use ay_core::resource::{ChildSpec, Guard};

        use super::ShareOf;

        let mut exec = Executor::new();
        let wall = Instant::now() + HOUR;
        exec.set_solve_controls(None, Some(wall));
        let check = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        let _in_check = check.enter();
        let share = exec
            .open_deadline_share(ShareOf::Search)
            .expect("there is time to divide");
        let half = exec.solve_deadline.get().expect("the share's deadline");
        assert!(half < wall && half > Instant::now() + HOUR / 3, "{half:?}");
        assert_eq!(
            exec.solve_deadline.live().get(),
            Some(wall),
            "never written"
        );
        assert_eq!(exec.certification_deadline.get(), Some(wall), "untouched");
        assert_eq!(check.ledger().deadline_shares, 1);
        exec.solve_deadline.set(Some(Instant::now()));
        assert!(exec.solve_deadline.expired(), "a write moves the share");
        assert!(
            ay_core::resource::check_stop_requested(),
            "the share is entered: a theory loop sees it"
        );
        drop(share);
        assert_eq!(
            exec.solve_deadline.get(),
            Some(wall),
            "the executor's is back"
        );
        assert!(!ay_core::resource::check_stop_requested());
        assert_eq!(check.ledger().deadline_shares_spent, 1, "closed spent");

        let both = exec
            .open_deadline_share(ShareOf::SearchAndCertification)
            .expect("there is time to divide");
        let half = exec.solve_deadline.get();
        assert_eq!(exec.certification_deadline.get(), half, "no later than it");
        drop(both);
        assert_eq!(exec.certification_deadline.get(), Some(wall));
        assert_eq!(check.ledger().deadline_shares, 2);
        assert_eq!(check.ledger().deadline_shares_spent, 1);

        exec.set_solve_controls(None, None);
        assert!(
            exec.open_deadline_share(ShareOf::Search).is_none(),
            "no deadline, nothing to divide"
        );
    }

    #[test]
    fn proof_assembly_polls_its_certify_node_and_its_envelope() {
        let interrupt = Arc::new(AtomicBool::new(false));
        let mut exec = Executor::new();
        exec.set_solve_controls(Some(Arc::clone(&interrupt)), Some(Instant::now() + HOUR));
        exec.solve_deadline.set(Some(Instant::now()));
        assert!(
            !exec.proof_assembly_stop_requested(),
            "the search wall is not the assembly's deadline"
        );
        exec.certification_deadline.set(Some(Instant::now()));
        assert!(exec.proof_assembly_stop_requested(), "its envelope is");
        exec.certification_deadline.set(Some(Instant::now() + HOUR));
        assert!(!exec.proof_assembly_stop_requested());
        interrupt.store(true, Ordering::Relaxed);
        assert!(exec.proof_assembly_stop_requested(), "and the interrupt");
    }
}
