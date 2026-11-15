// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The exact-division sweeps a proof build has already seen fail, so the
//! build's other spellings of the same divider obligation do not sweep it
//! again.
//!
//! ## Why
//!
//! 6571be1b9 gave a `BvBitBlast` lemma that mentions `bvudiv`/`bvurem`, once
//! its abstracted attempt fails, ONE more attempt with the exact divider
//! (`checker/bv_bitblast/division.rs`). When that attempt's monolithic
//! refutation stops on a counted proof-size cap, the split and the sweep
//! after it get the envelope's whole 200,000 conflicts (DR-31,
//! `bv_blast_solver/sweep.rs`). One proof build asks the strict checker
//! about one divider obligation in many spellings: the solver's lemma
//! (`reassert_final_promotion_boundaries`), the guarded collapse's
//! `(not (and A1 .. An))`, the exact-authored lane's concrete roots, the
//! raw-root lane's `(not A1) .. (not An)`, the residual-trust rescue, and
//! each again in the certification's re-solves. The checker's memo is keyed
//! by the exact clause (`checker/bv_bitblast/semantic_decision.rs`), so no
//! spelling hits another's refusal. Measured 2026-10-14 on ay 85f8d30d3
//! (model-checker-consumer R30 `rem_in_range`, `u64 x % 1000003 < 1000003`): seven
//! spellings each spent about 1 s in the monolithic attempt and 19-25 s
//! sweeping without closing, 145 of the run's 148 s.
//!
//! ## What is remembered, and what it changes
//!
//! * An exact-division attempt over no case reading whose split and sweep
//!   spent the WHOLE envelope's conflicts or work without closing, before
//!   the hang guard and with a poll confirming the caller was still going,
//!   records its clause's DIVISION SIGNATURE in the memo installed on the
//!   thread: every `bvudiv`/`bvurem` term of the clause read structurally
//!   ([`Division`]), with the reading and the identity of the counted
//!   envelope. A sweep that closes, or ends short of its envelope, records
//!   nothing.
//! * A later exact-division attempt with that signature, under the same
//!   memo, still makes its monolithic attempt (a spelling can close there
//!   when another one did not), and skips only the split and the sweep.
//! * Nothing else changes. The first sweep of every signature has its whole
//!   envelope, as DR-31 rules; a sweep that closes records nothing; the
//!   abstracted attempt, case readings, every other sweep and every caller
//!   that installed no memo decide exactly as before.
//! * A refusal reached after a skipped sweep is not the counted envelope's
//!   verdict on that clause. The checker never records it in the store's
//!   refusal memo: it records it here, keyed by the exact clause, counted
//!   envelope and store snapshot, and repeats it only while this memo is
//!   installed. A speculative decline cannot answer a strict decision.
//! * Fail-closed: the memo only ever withholds a sweep, and every refutation
//!   is replayed before it is admitted.
//! * A refusal the strict producer repeats for an input it already decided
//!   (`bv_blast_solver/compact/refusal_memo.rs`) remembers again the failed
//!   sweep that decision remembered, in the attempt in progress
//!   ([`failing`]), as deciding the input again would.
//!
//! ## Scope and hand-off
//!
//! An executor holds one [`ExactDivisionSweepMemo`]. Each of its proof builds
//! starts it afresh and installs it on the thread for the build
//! ([`ExactDivisionSweepMemo::begin_build`]). An executor derived from it to
//! re-solve the same problem for certification shares it
//! ([`ExactDivisionSweepMemo::share_with_derived`]): its builds carry on
//! from what the parent's build learned. A signature is structural (names,
//! sorts, constants, shape; no `TermId`), so it holds in the derived
//! executor's compacted clone of the store; a clause decline is
//! store-stamped and never crosses stores.
//!
//! ## Deciding with no exact divider at all
//!
//! [`without_exact_division`] runs strict decisions that make no
//! exact-division attempt: a lemma the abstracted attempt cannot refute is
//! refused there. It is for a caller asking whether a lemma closes WITHOUT
//! the exact divider, ahead of a lane that would pay for it (`ay-dpll`'s
//! `guarded/urem_bound/before_division.rs`). Such a refusal is not the
//! counted envelope's verdict, so nothing remembers it: not the store's
//! refusal memo, not a memo's declines. Every later decision of the clause
//! is made as if the probe had never run.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::sync::{Arc, Mutex, PoisonError};

use ay_core::term::TermStoreSnapshotStamp;
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};

/// Terms a clause walk visits, and nodes its division terms may have
/// together, before the clause is left without a signature (decided as if
/// no memo were installed).
const MAX_CLAUSE_VISITS: usize = 1 << 20;
const MAX_SIGNATURE_NODES: usize = 4096;
/// Failed signatures and clause declines one memo keeps; past either it
/// remembers no more, which costs time, never correctness.
const MAX_FAILED: usize = 256;
const MAX_DECLINED: usize = 1024;

/// The reason a decline repeated from the memo carries.
pub(crate) const DECLINED: &str = "an exact-division sweep of this clause's divider obligation \
     already failed in this proof build, and this clause was refused without one; it is decided \
     afresh outside the build";

/// The exact-division sweeps one proof build has seen fail; see the module
/// documentation. Cloning shares nothing: use
/// [`Self::share_with_derived`].
pub struct ExactDivisionSweepMemo {
    shared: Arc<Mutex<Memo>>,
    inherited: bool,
}

impl Default for ExactDivisionSweepMemo {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for ExactDivisionSweepMemo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExactDivisionSweepMemo")
            .field("failed_signatures", &self.failed_signatures())
            .field("skipped_sweeps", &self.skipped_sweeps())
            .field("inherited", &self.inherited)
            .finish_non_exhaustive()
    }
}

impl ExactDivisionSweepMemo {
    /// An empty memo of its own.
    #[must_use]
    pub fn new() -> Self {
        Self {
            shared: Arc::default(),
            inherited: false,
        }
    }

    /// This memo for an executor derived from its holder to re-solve the
    /// same problem: the derived executor's builds draw on and add to it,
    /// and never start it afresh.
    #[must_use]
    pub fn share_with_derived(&self) -> Self {
        Self {
            shared: Arc::clone(&self.shared),
            inherited: true,
        }
    }

    /// Begin one proof build: a memo of its own starts afresh (unless it is
    /// already the one installed on this thread, by an enclosing build), a
    /// shared one carries on. The memo is installed on this thread until the
    /// returned scope drops.
    pub fn begin_build(&mut self) -> ExactDivisionSweepScope {
        if !self.inherited && !installed(&self.shared) {
            self.shared = Arc::default();
        }
        let previous = CURRENT.with(|current| current.replace(Some(Arc::clone(&self.shared))));
        ExactDivisionSweepScope {
            previous,
            _thread: PhantomData,
        }
    }

    /// Division signatures whose sweep failed under this memo.
    #[must_use]
    pub fn failed_signatures(&self) -> usize {
        self.with(|memo| memo.failed.len())
    }

    /// Sweeps this memo withheld.
    #[must_use]
    pub fn skipped_sweeps(&self) -> u64 {
        self.with(|memo| memo.skipped)
    }

    fn with<T>(&self, read: impl FnOnce(&Memo) -> T) -> T {
        read(&self.shared.lock().unwrap_or_else(PoisonError::into_inner))
    }
}

/// The memo of one build, installed on the thread that opened it until this
/// drops (it then reinstates whatever was installed before). Not `Send`.
#[must_use = "the memo is installed only while this value lives"]
pub struct ExactDivisionSweepScope {
    previous: Option<Arc<Mutex<Memo>>>,
    _thread: PhantomData<*const ()>,
}

impl Drop for ExactDivisionSweepScope {
    fn drop(&mut self) {
        let previous = self.previous.take();
        CURRENT.with(|current| current.replace(previous));
    }
}

#[derive(Default)]
struct Memo {
    failed: HashSet<Key>,
    declined: Vec<(u64, TermStoreSnapshotStamp, Vec<TermId>)>,
    skipped: u64,
}

/// One node of a division term read structurally; children by position in
/// the post-order its [`Division`] lists.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Node {
    Const(Constant),
    Var(String, u32, Sort),
    App(Symbol, Sort, Vec<u32>),
    Not(u32),
    Ite(u32, u32, u32),
}

/// One `bvudiv`/`bvurem` term: its DAG in post-order.
type Division = Vec<Node>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Key {
    envelope: u64,
    hypotheses: bool,
    divisions: Vec<Division>,
}

/// The exact-division attempt in progress on this thread.
struct Attempt {
    key: Key,
    memo: Arc<Mutex<Memo>>,
}

thread_local! {
    static CURRENT: RefCell<Option<Arc<Mutex<Memo>>>> = const { RefCell::new(None) };
    static ATTEMPT: RefCell<Option<Attempt>> = const { RefCell::new(None) };
    /// The decision in progress withheld a sweep on the memo's word.
    static SKIPPED: Cell<bool> = const { Cell::new(false) };
    /// The decision in progress remembered a failed sweep ([`sweep_failed`]).
    static FAILED: Cell<bool> = const { Cell::new(false) };
    /// Decisions on this thread make no exact-division attempt
    /// ([`without_exact_division`]).
    static NO_EXACT_DIVISION: Cell<bool> = const { Cell::new(false) };
}

/// Run `decide` with every exact-division attempt its strict decisions would
/// make withheld (see the module documentation). A lemma one of them refuses
/// for want of the exact divider is refused, and that refusal is remembered
/// nowhere. Whatever they accept was refuted and replayed in full.
pub fn without_exact_division<T>(decide: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            let outer = self.0;
            NO_EXACT_DIVISION.with(|withheld| withheld.set(outer));
        }
    }
    let _restore = Restore(NO_EXACT_DIVISION.with(|withheld| withheld.replace(true)));
    decide()
}

/// Whether the exact-division attempt about to start is withheld by
/// [`without_exact_division`]. The decision in progress is told it withheld
/// one, so it remembers its refusal in no store.
pub(crate) fn withholds_exact_division() -> bool {
    if !NO_EXACT_DIVISION.with(Cell::get) {
        return false;
    }
    SKIPPED.with(|skipped| skipped.set(true));
    true
}

fn installed(shared: &Arc<Mutex<Memo>>) -> bool {
    CURRENT.with(|current| {
        current
            .borrow()
            .as_ref()
            .is_some_and(|memo| Arc::ptr_eq(memo, shared))
    })
}

fn current() -> Option<Arc<Mutex<Memo>>> {
    CURRENT.with(|current| current.borrow().clone())
}

fn lock(memo: &Mutex<Memo>) -> std::sync::MutexGuard<'_, Memo> {
    memo.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Run `attempt`, the exact-division attempt at `clause`, under the
/// installed memo: `hypotheses` is its reading (`None` for a case reading,
/// which the memo leaves alone), `envelope` its counted envelope's identity.
pub(crate) fn exact_division<T>(
    terms: &TermStore,
    clause: &[TermId],
    hypotheses: Option<bool>,
    envelope: u64,
    attempt: impl FnOnce() -> T,
) -> T {
    struct Leave(Option<Attempt>);
    impl Drop for Leave {
        fn drop(&mut self) {
            let outer = self.0.take();
            ATTEMPT.with(|attempt| attempt.replace(outer));
        }
    }
    let entered = current().and_then(|memo| {
        let key = Key {
            envelope,
            hypotheses: hypotheses?,
            divisions: division_signature(terms, clause)?,
        };
        Some(Attempt { key, memo })
    });
    let _leave = Leave(ATTEMPT.with(|attempt| attempt.replace(entered)));
    attempt()
}

/// Whether the sweep the exact-division attempt in progress is about to make
/// is one its memo already saw fail (counted as withheld).
pub(crate) fn skips_sweep() -> bool {
    ATTEMPT.with(|attempt| {
        let attempt = attempt.borrow();
        let Some(Attempt { key, memo }) = attempt.as_ref() else {
            return false;
        };
        let mut memo = lock(memo);
        if !memo.failed.contains(key) {
            return false;
        }
        memo.skipped = memo.skipped.saturating_add(1);
        SKIPPED.with(|skipped| skipped.set(true));
        true
    })
}

/// Whether a failed sweep of the attempt in progress would be remembered.
pub(crate) fn remembers_sweep() -> bool {
    ATTEMPT.with(|attempt| attempt.borrow().is_some())
}

/// The sweep of the attempt in progress spent its whole envelope without
/// closing, before the hang guard, and the caller is still going: remember
/// its signature.
pub(crate) fn sweep_failed() {
    ATTEMPT.with(|attempt| {
        if let Some(Attempt { key, memo }) = attempt.borrow().as_ref() {
            FAILED.with(|failed| failed.set(true));
            let mut memo = lock(memo);
            if memo.failed.len() < MAX_FAILED {
                memo.failed.insert(key.clone());
            }
        }
    });
}

/// Run one strict decision and report whether it withheld a sweep.
pub(crate) fn deciding<T>(decide: impl FnOnce() -> T) -> (T, bool) {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            let outer = self.0;
            SKIPPED.with(|skipped| skipped.set(skipped.get() || outer));
        }
    }
    let restore = Restore(SKIPPED.with(|skipped| skipped.replace(false)));
    let outcome = decide();
    let withheld = SKIPPED.with(Cell::get);
    drop(restore);
    (outcome, withheld)
}

/// Run one strict decision and report whether it remembered a failed sweep
/// in the attempt in progress, so that a memo of the decision's outcome
/// (`bv_blast_solver/compact/refusal_memo.rs`) can remember it again.
pub(crate) fn failing<T>(decide: impl FnOnce() -> T) -> (T, bool) {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            let outer = self.0;
            FAILED.with(|failed| failed.set(failed.get() || outer));
        }
    }
    let restore = Restore(FAILED.with(|failed| failed.replace(false)));
    let outcome = decide();
    let failed = FAILED.with(Cell::get);
    drop(restore);
    (outcome, failed)
}

/// Whether the installed memo holds a decline of exactly `clause` in
/// `terms` under this counted `envelope`.
pub(crate) fn declined(terms: &TermStore, clause: &[TermId], envelope: u64) -> bool {
    current().is_some_and(|memo| {
        lock(&memo)
            .declined
            .iter()
            .any(|(remembered_envelope, stamp, declined)| {
                *remembered_envelope == envelope
                    && declined.as_slice() == clause
                    && stamp.is_append_only_prefix_of(terms)
            })
    })
}

/// Remember, in the installed memo, a refusal of `clause` in `terms` reached
/// after a withheld sweep under this counted `envelope`. One reached under
/// [`without_exact_division`] is remembered nowhere.
pub(crate) fn record_decline(terms: &TermStore, clause: &[TermId], envelope: u64) {
    if NO_EXACT_DIVISION.with(Cell::get) {
        return;
    }
    if let Some(memo) = current() {
        let mut memo = lock(&memo);
        if memo.declined.len() < MAX_DECLINED {
            memo.declined
                .push((envelope, terms.snapshot_stamp(), clause.to_vec()));
        }
    }
}

/// Every `bvudiv`/`bvurem` term below `clause`, each read structurally and
/// listed in an order no store's numbering decides, or `None` when the
/// clause has none or is too large to read so.
fn division_signature(terms: &TermStore, clause: &[TermId]) -> Option<Vec<Division>> {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = clause.to_vec();
    let mut divisions: Vec<TermId> = Vec::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_CLAUSE_VISITS {
            return None;
        }
        if let TermData::App(Symbol::Named(name), _) = terms.get(term) {
            if matches!(name.as_str(), "bvudiv" | "bvurem") {
                divisions.push(term);
            }
        }
        stack.extend(terms.children(term));
    }
    let mut budget = MAX_SIGNATURE_NODES;
    let mut read: Vec<(u64, Division)> = Vec::with_capacity(divisions.len());
    for division in divisions {
        let nodes = read_structurally(terms, division, &mut budget)?;
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        nodes.hash(&mut hasher);
        read.push((hasher.finish(), nodes));
    }
    if read.is_empty() {
        return None;
    }
    read.sort_by_key(|(hash, _)| *hash);
    Some(read.into_iter().map(|(_, nodes)| nodes).collect())
}

/// `root`'s DAG in post-order, children before parents in the order the term
/// lists them, or `None` past `budget` nodes or at a binder.
fn read_structurally(terms: &TermStore, root: TermId, budget: &mut usize) -> Option<Division> {
    let mut position: HashMap<TermId, u32> = HashMap::new();
    let mut nodes: Division = Vec::new();
    let mut stack: Vec<(TermId, bool)> = vec![(root, false)];
    while let Some((term, children_done)) = stack.pop() {
        if position.contains_key(&term) {
            continue;
        }
        let data = terms.get(term);
        if !children_done {
            stack.push((term, true));
            let children = match data {
                TermData::Const(_) | TermData::Var(..) => Vec::new(),
                TermData::App(_, args) => args.clone(),
                TermData::Not(inner) => vec![*inner],
                TermData::Ite(c, t, e) => vec![*c, *t, *e],
                _ => return None,
            };
            stack.extend(children.into_iter().rev().map(|child| (child, false)));
            continue;
        }
        *budget = budget.checked_sub(1)?;
        let at = |child: &TermId| position.get(child).copied();
        let node = match data {
            TermData::Const(value) => Node::Const(value.clone()),
            TermData::Var(name, id) => Node::Var(name.clone(), *id, terms.sort(term).clone()),
            TermData::App(symbol, args) => Node::App(
                symbol.clone(),
                terms.sort(term).clone(),
                args.iter().map(at).collect::<Option<_>>()?,
            ),
            TermData::Not(inner) => Node::Not(at(inner)?),
            TermData::Ite(c, t, e) => Node::Ite(at(c)?, at(t)?, at(e)?),
            _ => return None,
        };
        position.insert(term, u32::try_from(nodes.len()).ok()?);
        nodes.push(node);
    }
    Some(nodes)
}

#[cfg(test)]
#[path = "exact_division_sweeps_tests.rs"]
mod tests;
