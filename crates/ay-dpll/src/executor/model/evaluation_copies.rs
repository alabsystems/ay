// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Optional native evaluation restrictions. All storage is conservatively
//! cumulative for this call, not a claim about physical live allocations.
//! Immutable model DATA may retain that prepaid arena with its shared payload;
//! scratch-only traversals release their buffers without refunding work.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use super::functional_arrays::PinAdmission;
use super::{EvalValue, Executor};
use crate::executor::UnknownOrigin;

struct Owner {
    admission: PinAdmission,
    source: ay_frontend::SourceContextStamp,
    store: ay_core::term::TermStoreSnapshotStamp,
    frames: Cell<usize>,
}

/// A retained conservative DATA charge, not an execution callback or grant.
/// The immutable payload and this token must share the same Arc owner.
pub(in crate::executor) struct RetainedEvaluationMemory {
    pub(in crate::executor::model) _arena: std::sync::Arc<super::EvaluationArena>,
    pub(in crate::executor::model) original: super::EvaluationAttempt,
    pub(in crate::executor::model) bytes: usize,
    pub(in crate::executor::model) ceiling: Option<usize>,
}

impl std::fmt::Debug for RetainedEvaluationMemory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RetainedEvaluationMemory")
            .field("bytes", &self.bytes)
            .finish_non_exhaustive()
    }
}

impl RetainedEvaluationMemory {
    /// DATA already occupying another attempt's arena must also be priced in
    /// this read. An unchanged attempt already includes the original arena.
    pub(in crate::executor) fn charge_for_attempt(
        &self,
        attempt: &super::EvaluationAttempt,
    ) -> (usize, Option<usize>) {
        (
            if self.original.is_same_attempt(attempt) {
                0
            } else {
                self.bytes
            },
            self.ceiling,
        )
    }
    /// Price retained DATA in the current read's ledger. Never poll or record
    /// a new read's refusal on the earlier solve's clock/attempt.
    pub(super) fn read_charge(
        &self,
        exec: &Executor,
    ) -> Result<super::EvaluationArena, UnknownOrigin> {
        let attempt = exec.evaluation_attempt();
        exec.poll_evaluation_stop()?;
        if !attempt.is_same_attempt(&exec.evaluation_attempt()) {
            let origin = attempt.record_stop(UnknownOrigin::IncompleteSolverLane);
            return Err(exec.record_evaluation_stop(origin));
        }
        let arena = attempt.temporary_arena()?;
        let bytes = if self.original.is_same_attempt(&attempt) {
            0 // Already present in the SAME ledger through `self._arena`.
        } else {
            self.bytes
        };
        let limit = match (self.ceiling, exec.evaluation_term_memory_limit()) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        };
        arena.check_usage(exec.ctx.terms.true_memory_bytes(), bytes, limit)?;
        exec.poll_evaluation_stop()?;
        if !attempt.is_same_attempt(&exec.evaluation_attempt()) {
            let origin = attempt.record_stop(UnknownOrigin::IncompleteSolverLane);
            return Err(exec.record_evaluation_stop(origin));
        }
        Ok(arena)
    }
}

impl Executor {
    /// Only the currently retained native operation may supply a tactic's
    /// refusal origin. A parked preceding decision is not this request.
    pub(crate) fn tactic_refusal_origin(&self) -> Option<UnknownOrigin> {
        self.evaluation_read_controls()?;
        self.evaluation_stop_origin()
    }

    /// Retain the exact source-root metadata under the same construction owner
    /// before the first pointer copy. No read timer or balance is created here.
    pub(crate) fn capture_tactic_source_roots(
        &self,
        end: Option<std::time::Instant>,
    ) -> Result<(Vec<ay_core::TermId>, TacticConstructionScope), UnknownOrigin> {
        let scope = self.capture_tactic_construction_until(end)?;
        let mut roots = Vec::new();
        ay_core::term::reserve_counted(&mut roots, self.ctx.assertions.len(), scope.admission())
            .map_err(|_| {
                self.evaluation_stop_origin()
                    .unwrap_or(UnknownOrigin::IncompleteSolverLane)
            })?;
        if !scope.validate(self) {
            return Err(self
                .evaluation_stop_origin()
                .unwrap_or(UnknownOrigin::IncompleteSolverLane));
        }
        roots.extend_from_slice(&self.ctx.assertions);
        if !scope.validate(self) {
            return Err(self
                .evaluation_stop_origin()
                .unwrap_or(UnknownOrigin::IncompleteSolverLane));
        }
        Ok((roots, scope))
    }
    pub(crate) fn capture_tactic_construction(
        &self,
    ) -> Result<TacticConstructionScope, UnknownOrigin> {
        self.capture_tactic_construction_until(None)
    }

    /// An existing caller's absolute execution end, never a renewed timeout.
    pub(crate) fn capture_tactic_construction_until(
        &self,
        end: Option<std::time::Instant>,
    ) -> Result<TacticConstructionScope, UnknownOrigin> {
        Ok(TacticConstructionScope {
            fence: EvaluationCopyScope::enter(self)?.into_construction(self)?,
            end,
        })
    }
}

/// A native goal pass's consuming original read handoff. This opaque token
/// retains paid scratch until the caller's post-construction publication fence.
pub(crate) struct TacticConstructionScope {
    fence: EvaluationConstructionFence,
    end: Option<std::time::Instant>,
}
impl TacticConstructionScope {
    /// Consuming handoff to an explicit native declaration command. Retain
    /// the SAME controls/counter/arena; this type offers no immutable read or
    /// construction/source permission after authored metadata starts changing.
    pub(crate) fn into_declarations(
        self,
        exec: &Executor,
    ) -> Result<TacticDeclarationScope, UnknownOrigin> {
        if !self.validate(exec) {
            return Err(exec
                .evaluation_stop_origin()
                .unwrap_or(UnknownOrigin::IncompleteSolverLane));
        }
        Ok(TacticDeclarationScope {
            store: exec.ctx.terms.snapshot_stamp(),
            source: RefCell::new(exec.ctx.source_context_stamp()),
            end: self.end,
            owner: self.fence.owner,
        })
    }
    pub(crate) fn admission(&self) -> &dyn ay_core::term::TermConstructionAdmission {
        self
    }
    /// Retain immutable construction DATA, without retaining an old clock or
    /// callback grant. The caller keeps the token at least as long as the DATA.
    pub(in crate::executor) fn retain_data_memory(
        &self,
        exec: &Executor,
    ) -> Option<RetainedEvaluationMemory> {
        self.validate(exec)
            .then(|| self.fence.owner.admission.retain_data_memory())
    }
    pub(crate) fn validate(&self, exec: &Executor) -> bool {
        use ay_core::term::TermConstructionAdmission as _;
        self.check().is_ok() && self.fence.validate(exec) && self.check().is_ok()
    }
}

pub(crate) struct TacticDeclarationScope {
    owner: Rc<Owner>,
    store: ay_core::term::TermStoreSnapshotStamp,
    source: RefCell<ay_frontend::SourceContextStamp>,
    end: Option<std::time::Instant>,
}
enum TacticStorePhase {
    Declarations,
    Decision,
}
impl TacticDeclarationScope {
    pub(crate) fn admission(&self) -> &dyn ay_core::term::TermConstructionAdmission {
        &self.owner.admission
    }
    /// Called only immediately after the canonical prepaid declaration update,
    /// with no intervening observer callback. Never captures a new allowance.
    pub(crate) fn recorded_native_declaration(&self, exec: &Executor) {
        *self.source.borrow_mut() = exec.ctx.source_context_stamp();
    }
    pub(crate) fn validate_controls(&self, exec: &Executor) -> bool {
        self.validate_phase(exec, TacticStorePhase::Declarations)
    }
    /// A native decision may append internal terms, but cannot replace the
    /// original store, declarations, attempt or prepaid storage owner.
    pub(crate) fn validate_decision(&self, exec: &Executor) -> bool {
        self.validate_phase(exec, TacticStorePhase::Decision)
    }
    fn validate_phase(&self, exec: &Executor, phase: TacticStorePhase) -> bool {
        if self.end.is_some_and(|end| std::time::Instant::now() >= end) {
            self.owner.admission.refuse_deadline();
        }
        let current = || {
            self.owner.frames.get() == 0
                && !active()
                && *self.source.borrow() == exec.ctx.source_context_stamp()
                && self.owner.admission.matches_current_read(exec)
                && match phase {
                    TacticStorePhase::Decision => {
                        self.store.is_append_only_prefix_of(&exec.ctx.terms)
                    }
                    TacticStorePhase::Declarations => self.store == exec.ctx.terms.snapshot_stamp(),
                }
        };
        if current()
            && self.owner.admission.poll().is_ok()
            && current()
            && self
                .owner
                .admission
                .check_source_usage(exec.ctx.terms.true_memory_bytes())
                .is_ok()
            && current()
        {
            true
        } else {
            let origin = self.owner.admission.refuse_source();
            exec.record_evaluation_stop(origin);
            false
        }
    }
}

impl ay_core::term::TermConstructionAdmission for TacticConstructionScope {
    fn admit(
        &self,
        work: usize,
        bytes: usize,
    ) -> Result<(), ay_core::original_query::CountedAdmissionError> {
        let poll = || {
            if self.end.is_some_and(|end| std::time::Instant::now() >= end) {
                self.fence.owner.admission.refuse_deadline();
            }
            self.fence.term_admission().check()
        };
        poll()?;
        self.fence.term_admission().admit(work, bytes)?;
        poll()
    }
    fn refuse(
        &self,
        error: ay_core::original_query::CountedAdmissionError,
    ) -> ay_core::original_query::CountedAdmissionError {
        ay_core::term::TermConstructionAdmission::refuse(self.fence.term_admission(), error)
    }
}

impl Drop for Owner {
    fn drop(&mut self) {
        // Cached copies created by this call must die before its cumulative
        // arena is released. Clearing is verdict-neutral and also invalidates
        // callback-era memo snapshots before the original admission drops.
        super::eval_memo::clear();
    }
}

thread_local! {
    static ACTIVE: RefCell<Option<Rc<Owner>>> = const { RefCell::new(None) };
    static ENTERING: Cell<bool> = const { Cell::new(false) };
}

struct Entering;
impl Drop for Entering {
    fn drop(&mut self) {
        ENTERING.with(|slot| slot.set(false));
    }
}

/// Nested callers retain one original counter/arena and cannot renew it.
pub(in crate::executor) struct EvaluationCopyScope {
    owner: Rc<Owner>,
}

/// Resource debit plus the SAME immutable source/read fence, including after
/// callbacks. Counted native helpers can therefore refuse before allocation.
pub(in crate::executor::model) struct EvaluationReadAdmission<'a> {
    scope: &'a EvaluationCopyScope,
    exec: &'a Executor,
}

impl ay_core::term::TermConstructionAdmission for EvaluationReadAdmission<'_> {
    fn admit(
        &self,
        work: usize,
        bytes: usize,
    ) -> Result<(), ay_core::original_query::CountedAdmissionError> {
        use ay_core::original_query::OriginalAdmissionError;
        use ay_core::term::TermConstructionAdmission;
        if !validate(self.exec) {
            return Err(self.refuse(OriginalAdmissionError::ObserverStopped.into()));
        }
        self.scope.owner.admission.admit(work, bytes)?;
        if !validate(self.exec) {
            return Err(self.refuse(OriginalAdmissionError::ObserverStopped.into()));
        }
        Ok(())
    }
    fn refuse(
        &self,
        error: ay_core::original_query::CountedAdmissionError,
    ) -> ay_core::original_query::CountedAdmissionError {
        ay_core::term::TermConstructionAdmission::refuse(&self.scope.owner.admission, error)
    }
}

/// Live scratch only. It borrows the SAME original owner and counter, but
/// releases actual traversal buffers before the next public value is read.
pub(in crate::executor::model) struct TemporaryReadAdmission<'a> {
    arena: super::EvaluationArena,
    scope: &'a EvaluationCopyScope,
    exec: &'a Executor,
    bytes: Cell<usize>,
}

impl ay_core::term::TermConstructionAdmission for TemporaryReadAdmission<'_> {
    fn admit(
        &self,
        work: usize,
        bytes: usize,
    ) -> Result<(), ay_core::original_query::CountedAdmissionError> {
        use ay_core::original_query::{CountedAdmissionError, OriginalAdmissionError};
        use ay_core::term::TermConstructionAdmission;
        self.scope.owner.admission.admit(work, 0)?;
        if !validate(self.exec) {
            return Err(self.refuse(OriginalAdmissionError::ObserverStopped.into()));
        }
        let bytes = self
            .bytes
            .get()
            .checked_add(bytes)
            .ok_or_else(|| self.refuse(CountedAdmissionError::Memory))?;
        let limit = match (
            self.scope.owner.admission.captured_term_limit(),
            self.exec.evaluation_term_memory_limit(),
        ) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        };
        if self
            .arena
            .check_usage(self.exec.ctx.terms.true_memory_bytes(), bytes, limit)
            .is_err()
        {
            self.scope.owner.admission.admit(0, 0)?;
            return Err(self.refuse(CountedAdmissionError::Memory));
        }
        self.bytes.set(bytes);
        self.scope.owner.admission.admit(0, 0)?;
        if !validate(self.exec) {
            return Err(self.refuse(OriginalAdmissionError::ObserverStopped.into()));
        }
        Ok(())
    }
    fn refuse(
        &self,
        error: ay_core::original_query::CountedAdmissionError,
    ) -> ay_core::original_query::CountedAdmissionError {
        ay_core::term::TermConstructionAdmission::refuse(&self.scope.owner.admission, error)
    }
}

impl EvaluationCopyScope {
    pub(in crate::executor::model) fn read_admission<'a>(
        &'a self,
        exec: &'a Executor,
    ) -> EvaluationReadAdmission<'a> {
        EvaluationReadAdmission { scope: self, exec }
    }
    pub(in crate::executor::model) fn temporary_admission<'a>(
        &'a self,
        exec: &'a Executor,
    ) -> Result<TemporaryReadAdmission<'a>, UnknownOrigin> {
        if !validate(exec) {
            return Err(self.owner.admission.refuse_source());
        }
        self.owner.admission.pay(1, 0)?;
        if !validate(exec) {
            return Err(self.owner.admission.refuse_source());
        }
        let arena = exec.evaluation_attempt().temporary_arena()?;
        if !validate(exec) {
            return Err(self.owner.admission.refuse_source());
        }
        Ok(TemporaryReadAdmission {
            arena,
            scope: self,
            exec,
            bytes: Cell::new(0),
        })
    }
    pub(in crate::executor::model) fn retain_data_memory(
        &self,
        exec: &Executor,
    ) -> Option<RetainedEvaluationMemory> {
        use ay_core::term::TermConstructionAdmission;
        // Do not retain somebody else's enclosing temporary copy scope as
        // model storage. This optional producer may decline a nested request.
        if self.owner.frames.get() != 1 || !validate(exec) {
            return None;
        }
        self.owner.admission.admit(1, 0).ok()?;
        validate(exec).then(|| self.owner.admission.retain_data_memory())
    }
    pub(in crate::executor) fn admission(&self) -> &dyn ay_core::term::TermConstructionAdmission {
        &self.owner.admission
    }
    /// End the immutable producer read without releasing its paid values or
    /// original controls. Only the sole read may transition to growing terms.
    pub(in crate::executor) fn into_construction(
        self,
        exec: &Executor,
    ) -> Result<EvaluationConstructionFence, UnknownOrigin> {
        if !validate(exec)
            || self.owner.frames.get() != 1
            || !owner().is_some_and(|active| Rc::ptr_eq(&active, &self.owner))
        {
            return Err(self.owner.admission.refuse_source());
        }
        let owner = Rc::clone(&self.owner);
        // Retaining Owner postpones its destructor: retire read-era memo entries
        // NOW, before deregistering TLS and allowing the term store to grow.
        super::eval_memo::clear();
        drop(self);
        Ok(EvaluationConstructionFence { owner })
    }

    pub(in crate::executor) fn enter(exec: &Executor) -> Result<Self, UnknownOrigin> {
        let previous = owner();
        let current = if let Some(current) = &previous {
            if !validate(exec) {
                return Err(exec
                    .evaluation_stop_origin()
                    .unwrap_or(UnknownOrigin::IncompleteSolverLane));
            }
            Rc::clone(current)
        } else {
            if ENTERING.with(|slot| slot.replace(true)) {
                return Err(exec
                    .evaluation_attempt()
                    .record_stop(UnknownOrigin::IncompleteSolverLane));
            }
            let _entering = Entering;
            let source = exec.ctx.source_context_stamp();
            let store = exec.ctx.terms.snapshot_stamp();
            let admission = PinAdmission::capture_current_read(exec)?;
            admission.pay(
                1,
                std::mem::size_of::<Owner>() + 2 * std::mem::size_of::<usize>(),
            )?;
            if source != exec.ctx.source_context_stamp() || store != exec.ctx.terms.snapshot_stamp()
            {
                return Err(admission.refuse_source());
            }
            Rc::new(Owner {
                admission,
                source,
                store,
                frames: Cell::new(0),
            })
        };
        let Some(frames) = current.frames.get().checked_add(1) else {
            return Err(current.admission.refuse_source());
        };
        current.frames.set(frames);
        ACTIVE.with(|slot| *slot.borrow_mut() = Some(Rc::clone(&current)));
        Ok(Self { owner: current })
    }
}

/// A consuming read-to-construction handoff. This retains the SAME admission,
/// cumulative arena, counter and original callbacks, never a new read snapshot.
pub(in crate::executor) struct EvaluationConstructionFence {
    owner: Rc<Owner>,
}

impl EvaluationConstructionFence {
    pub(in crate::executor) fn term_admission(
        &self,
    ) -> &impl ay_core::term::TermConstructionAdmission {
        &self.owner.admission
    }

    pub(in crate::executor) fn validate(&self, exec: &Executor) -> bool {
        let current = || {
            self.owner.frames.get() == 0
                && !active()
                && self.owner.admission.matches_current_read(exec)
                && self.owner.source == exec.ctx.source_context_stamp()
                && self.owner.store.is_append_only_prefix_of(&exec.ctx.terms)
        };
        // No RefCell borrow or store borrow remains held during original user
        // callbacks. A callback may invalidate source, attempt or read currency.
        if current()
            && self.owner.admission.poll().is_ok()
            && current()
            && self
                .owner
                .admission
                .check_source_usage(exec.ctx.terms.true_memory_bytes())
                .is_ok()
            && current()
        {
            true
        } else {
            let origin = self.owner.admission.refuse_source();
            exec.record_evaluation_stop(origin);
            false
        }
    }
}

impl Drop for EvaluationCopyScope {
    fn drop(&mut self) {
        self.owner
            .frames
            .set(self.owner.frames.get().saturating_sub(1));
        if self.owner.frames.get() == 0 {
            ACTIVE.with(|slot| {
                if slot
                    .borrow()
                    .as_ref()
                    .is_some_and(|owner| Rc::ptr_eq(owner, &self.owner))
                {
                    *slot.borrow_mut() = None;
                }
            });
        }
    }
}

fn owner() -> Option<Rc<Owner>> {
    ACTIVE.with(|slot| slot.borrow().clone())
}

pub(super) fn refuse_original(
    error: ay_core::original_query::CountedAdmissionError,
) -> ay_core::original_query::CountedAdmissionError {
    owner().map_or(error, |owner| {
        ay_core::term::TermConstructionAdmission::refuse(&owner.admission, error)
    })
}

pub(super) fn active() -> bool {
    ACTIVE.with(|slot| slot.borrow().is_some())
}

pub(super) fn charges_work_to(used: &std::sync::Arc<std::sync::atomic::AtomicUsize>) -> bool {
    owner().is_some_and(|owner| owner.admission.charges_work_to(used))
}

/// Keep the restriction alive across callbacks even if a reentrant caller
/// releases its outer frame. This shares ownership, not a renewed allowance.
pub(super) fn retain() -> Option<EvaluationCopyScope> {
    let owner = owner()?;
    let Some(frames) = owner.frames.get().checked_add(1) else {
        owner.admission.refuse_source();
        return None;
    };
    owner.frames.set(frames);
    Some(EvaluationCopyScope { owner })
}

/// Called even by the source-validated recursive entry: this scope never
/// grants permission to bypass normal source checks.
pub(in crate::executor) fn validate(exec: &Executor) -> bool {
    owner().is_none_or(|owner| {
        if owner.admission.matches_current_read(exec)
            && owner.source == exec.ctx.source_context_stamp()
            && owner.store == exec.ctx.terms.snapshot_stamp()
        {
            if owner.admission.pay(0, 0).is_err() {
                return false;
            }
            if owner.admission.matches_current_read(exec)
                && owner.source == exec.ctx.source_context_stamp()
                && owner.store == exec.ctx.terms.snapshot_stamp()
            {
                true
            } else {
                owner.admission.refuse_source();
                exec.evaluation_attempt()
                    .record_stop(UnknownOrigin::IncompleteSolverLane);
                false
            }
        } else {
            owner.admission.refuse_source();
            exec.evaluation_attempt()
                .record_stop(UnknownOrigin::IncompleteSolverLane);
            false
        }
    })
}

pub(in crate::executor) fn pay(work: usize, bytes: usize) -> bool {
    owner().is_none_or(|owner| owner.admission.pay(work, bytes).is_ok())
}

fn retain_refusal(accepted: bool) -> bool {
    if !accepted {
        if let Some(owner) = owner() {
            owner.admission.refuse_source();
        }
    }
    accepted
}

fn admit(value: &EvalValue) -> bool {
    !active() || retain_refusal(super::recovery_admission::admit_eval_value_copy(value, pay))
}

pub(super) fn copy(value: &EvalValue) -> EvalValue {
    let _retained = retain();
    if admit(value) {
        value.clone()
    } else {
        EvalValue::Unknown
    }
}

pub(super) fn integer(value: &num_bigint::BigInt) -> bool {
    let Some(bytes) = usize::try_from(value.bits().div_ceil(64))
        .ok()
        .and_then(|limbs| limbs.checked_mul(8))
        .and_then(|bytes| bytes.checked_add(std::mem::size_of::<EvalValue>()))
    else {
        return pay(usize::MAX, usize::MAX);
    };
    pay(bytes, bytes)
}

pub(super) fn rational(value: &num_rational::BigRational) -> bool {
    integer(value.numer()) && integer(value.denom())
}

pub(super) fn string(value: &str) -> bool {
    pay(value.len(), value.len())
}

pub(super) fn copy_string(value: &String) -> Option<String> {
    string(value).then(|| value.clone())
}

pub(super) fn atom(value: &EvalValue) -> bool {
    if !active() {
        return true;
    }
    if !admit(value) {
        return false;
    }
    let bits = match value {
        EvalValue::Fp(value) => u64::from(value.eb()) + u64::from(value.sb()),
        EvalValue::BitVec { value, width } => value.bits().max(u64::from(*width)),
        EvalValue::Rational(value) => {
            match value.numer().bits().checked_add(value.denom().bits()) {
                Some(n) => n,
                None => return false,
            }
        }
        EvalValue::Complex { real, imaginary } => return atom(real) && atom(imaginary),
        EvalValue::Algebraic(_) => {
            // Algebraic-to-number rendering performs resultant/refinement
            // arithmetic, not a payload copy, and has no priced native plan.
            if let Some(owner) = owner() {
                owner.admission.refuse_source();
            }
            return false;
        }
        _ => return admit(value),
    };
    usize::try_from(bits)
        .ok()
        .and_then(|n| n.checked_add(128))
        .and_then(|n| n.checked_mul(4))
        .is_some_and(|bytes| pay(bytes, bytes))
}

pub(super) fn fp(value: &ay_fp::FpModelValue) -> bool {
    if !active() {
        return true;
    }
    retain_refusal(
        super::recovery_admission::fp_copy_payload_bytes(value)
            .is_some_and(|bytes| pay(bytes, bytes)),
    )
}

pub(super) fn algebraic(value: &ay_nra::RealAlgebraicValue) -> bool {
    !active() || value.visit_copy_coefficients(rational)
}

pub(super) fn model_value(value: &ay_model_check::ModelValue) -> bool {
    !active()
        || retain_refusal(
            super::rendered_dt_limits::model_value_work(value)
                .is_some_and(|amount| pay(amount, amount)),
        )
}

/// Admit vector growth BEFORE reserve/extend, including conservative doubling.
pub(super) fn cells(count: usize) -> bool {
    count
        .checked_mul(2 * std::mem::size_of::<EvalValue>())
        .is_some_and(|bytes| pay(count, bytes))
}

pub(super) fn admit_slice(values: &[EvalValue]) -> bool {
    !active() || (cells(values.len()) && values.iter().all(admit))
}

pub(super) fn copy_slice(values: &[EvalValue]) -> Option<Vec<EvalValue>> {
    let _retained = retain();
    admit_slice(values).then(|| values.to_vec())
}

/// Exact data comparison with original admission, not IEEE fp.eq. Differing
/// algebraic representations need a separate arithmetic certificate and are
/// deliberately undecided here, rather than running an unpriced refinement.
pub(super) fn equal(left: &EvalValue, right: &EvalValue) -> Option<bool> {
    let _retained = retain();
    if !active() {
        return Some(left == right);
    }
    if !admit(left) || !admit(right) {
        return None;
    }
    let result = match (left, right) {
        (EvalValue::Unknown, _) | (_, EvalValue::Unknown) => None,
        (EvalValue::Fp(a), EvalValue::Fp(b)) => {
            super::recovery_admission::admitted_fp_equal(a, b, pay)
        }
        (EvalValue::Seq(a), EvalValue::Seq(b)) => equal_slice(a, b),
        (
            EvalValue::Complex {
                real: a,
                imaginary: b,
            },
            EvalValue::Complex {
                real: c,
                imaginary: d,
            },
        ) => Some(equal(a, c)? && equal(b, d)?),
        (EvalValue::Algebraic(a), EvalValue::Algebraic(b)) => {
            a.same_representation(b).then_some(true)
        }
        (EvalValue::Algebraic(_), EvalValue::Rational(_))
        | (EvalValue::Rational(_), EvalValue::Algebraic(_)) => None,
        _ => Some(left == right),
    };
    if pay(0, 0) {
        result
    } else {
        None
    }
}

pub(super) fn equal_slice(left: &[EvalValue], right: &[EvalValue]) -> Option<bool> {
    let _retained = retain();
    if !pay(0, 0) {
        return None;
    }
    if left.len() != right.len() {
        return pay(0, 0).then_some(false);
    }
    for (a, b) in left.iter().zip(right) {
        if !equal(a, b)? {
            return pay(0, 0).then_some(false);
        }
    }
    pay(0, 0).then_some(true)
}

pub(super) fn position(haystack: &[EvalValue], needle: &[EvalValue]) -> Option<Option<usize>> {
    let _retained = retain();
    if !pay(0, 0) {
        return None;
    }
    if needle.is_empty() {
        return pay(0, 0).then_some(Some(0));
    }
    if needle.len() > haystack.len() {
        return pay(0, 0).then_some(None);
    }
    for (index, window) in haystack.windows(needle.len()).enumerate() {
        if equal_slice(window, needle)? {
            return pay(0, 0).then_some(Some(index));
        }
    }
    pay(0, 0).then_some(None)
}

#[cfg(test)]
mod tests {
    use super::super::{eval_memo, EvalMemoSession, Model};
    use super::*;
    use ay_core::Sort;
    use std::sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering},
        Arc,
    };

    thread_local! {
        static CALLBACK_EXECUTOR: RefCell<Option<Rc<Executor>>> = const { RefCell::new(None) };
        static CALLBACK_READ: RefCell<Option<super::super::evaluation_control::EvaluationReadScope>> = const { RefCell::new(None) };
    }

    #[test]
    fn retained_proof_data_survives_scope_and_is_charged_once_per_read() {
        use ay_core::term::{reserve_counted, TermConstructionAdmission};
        let mut exec = Executor::new();
        let source = exec.ctx.terms.true_memory_bytes();
        exec.set_term_memory_limit(Some(source + 131_072));
        let original = exec.evaluation_attempt();
        let scope = exec.capture_tactic_construction().unwrap();
        let mut steps = Vec::new();
        reserve_counted(&mut steps, 64, &scope).unwrap();
        scope.admit(64, 0).unwrap();
        steps.extend((0..64).map(|_| ay_core::ProofStep::Assume(exec.ctx.terms.true_term())));
        reserve_counted(&mut exec.proof_construction_memory, 1, &scope).unwrap();
        let memory = scope.retain_data_memory(&exec).unwrap();
        let paid = memory.bytes;
        exec.last_proof = Some(ay_core::Proof::from_steps(steps));
        exec.proof_construction_memory.push(memory);
        drop(scope);
        assert!(paid > 1024);
        {
            let outer = exec.begin_native_evaluation_read(
                Arc::new(AtomicBool::new(false)),
                None,
                None,
                Some(source + paid + 512),
            );
            assert_eq!(exec.evaluation_stop_origin(), None);
            let _handoff = outer.retain();
            let _inner = exec.begin_external_evaluation_read();
            drop(outer);
            assert_eq!(
                exec.evaluation_stop_origin(),
                None,
                "nested readers share the paid DATA"
            );
            let _scratch = exec.admit_evaluation_scratch(256).unwrap();
            assert!(
                exec.admit_evaluation_scratch(1024).is_err(),
                "DATA remains paid after the first guard dies"
            );
        }
        {
            let _low = exec.begin_native_evaluation_read(
                Arc::new(AtomicBool::new(false)),
                None,
                None,
                Some(source + 1),
            );
            assert_eq!(
                exec.evaluation_stop_origin(),
                Some(UnknownOrigin::MemoryBudget)
            );
        }
        assert_eq!(
            original.stop_origin(),
            None,
            "a later refusal belongs to its own read"
        );
        {
            let _fresh = exec.begin_external_evaluation_read();
            assert_eq!(exec.evaluation_stop_origin(), None);
        }
        exec.invalidate_last_check_result();
        assert!(exec.proof_construction_memory.is_empty());
        assert!(exec.last_proof.is_none());
    }

    #[test]
    fn retained_model_memory_outlives_copy_scope_and_read_refusal_is_local() {
        let mut exec = Executor::new();
        let source = exec.ctx.terms.true_memory_bytes();
        exec.set_term_memory_limit(Some(source + 32_768));
        let original = exec.evaluation_attempt();
        let scope = EvaluationCopyScope::enter(&exec).unwrap();
        assert!(pay(1, 16_384));
        let payload = vec![7u8; 16_384];
        let memory = scope.retain_data_memory(&exec).unwrap();
        let data = Arc::new((payload, memory));
        drop(scope);
        let clone = Arc::clone(&data);
        drop(data);
        {
            let _read = exec.begin_native_evaluation_read(
                Arc::new(AtomicBool::new(false)),
                None,
                None,
                Some(source + 8192),
            );
            assert!(matches!(
                clone.1.read_charge(&exec),
                Err(UnknownOrigin::MemoryBudget)
            ));
        }
        assert_eq!(
            original.stop_origin(),
            None,
            "a later read cannot poison the old solve"
        );
        {
            let _read = exec.begin_native_evaluation_read(
                Arc::new(AtomicBool::new(false)),
                None,
                None,
                None,
            );
            let _charge = clone.1.read_charge(&exec).unwrap();
            assert_eq!(clone.0[0], 7);
        }
        // SAME original arena still includes retained DATA: the copy scope's
        // drop did not release it and a model clone did not create a grant.
        assert!(exec.admit_evaluation_scratch(20_000).is_err());
    }

    #[test]
    fn retained_model_memory_does_not_capture_an_enclosing_copy_scope() {
        let exec = Executor::new();
        let outer = EvaluationCopyScope::enter(&exec).unwrap();
        let inner = EvaluationCopyScope::enter(&exec).unwrap();
        assert!(inner.retain_data_memory(&exec).is_none());
        drop(inner);
        assert!(outer.retain_data_memory(&exec).is_some());
    }

    #[test]
    fn read_scratch_releases_storage_without_renewing_original_work() {
        use ay_core::term::TermConstructionAdmission;
        let mut exec = Executor::new();
        exec.set_term_memory_limit(Some(exec.ctx.terms.true_memory_bytes() + 8192));
        let scope = EvaluationCopyScope::enter(&exec).unwrap();
        let used = exec.evaluation_attempt().functional_work_counter();
        let before = used.load(Ordering::Acquire);
        for _ in 0..3 {
            let scratch = scope.temporary_admission(&exec).unwrap();
            scratch.admit(11, 6000).unwrap();
            let bytes = vec![1u8; 6000];
            assert_eq!(bytes[5999], 1);
            drop(bytes);
            drop(scratch);
        }
        assert!(used.load(Ordering::Acquire) >= before + 33);
        assert!(pay(1, 6000));
        assert!(
            !pay(1, 6000),
            "ordinary retained output cannot refund its storage"
        );
    }

    #[test]
    fn fenced_counted_reserve_refuses_callback_replacement_before_allocation() {
        let exec = Rc::new(Executor::new());
        CALLBACK_EXECUTOR.with(|slot| *slot.borrow_mut() = Some(Rc::clone(&exec)));
        let used = exec.evaluation_attempt().functional_work_counter();
        let threshold = Arc::new(AtomicUsize::new(usize::MAX));
        let arm = Arc::new(AtomicBool::new(true));
        let watch_threshold = Arc::clone(&threshold);
        let watch_arm = Arc::clone(&arm);
        let _stop = ay_core::resource::enter_check_stop(Arc::new(move || {
            if used.load(Ordering::Acquire) >= watch_threshold.load(Ordering::Acquire)
                && watch_arm.swap(false, Ordering::AcqRel)
            {
                let exec = CALLBACK_EXECUTOR
                    .with(|slot| slot.borrow().clone())
                    .unwrap();
                CALLBACK_READ
                    .with(|slot| *slot.borrow_mut() = Some(exec.begin_external_evaluation_read()));
            }
            false
        }));
        let scope = EvaluationCopyScope::enter(&exec).unwrap();
        threshold.store(
            exec.evaluation_attempt()
                .functional_work_counter()
                .load(Ordering::Acquire)
                + 1,
            Ordering::Release,
        );
        let mut values: Vec<u64> = Vec::new();
        assert!(
            ay_core::term::reserve_counted(&mut values, 1, &scope.read_admission(&exec)).is_err()
        );
        assert_eq!(
            values.capacity(),
            0,
            "the allocator must not run after the callback changed owner"
        );
        CALLBACK_READ.with(|slot| slot.borrow_mut().take());
        CALLBACK_EXECUTOR.with(|slot| slot.borrow_mut().take());
    }

    #[test]
    fn construction_transition_keeps_original_work_and_retires_read_memo() {
        let mut exec = Executor::new();
        let term = exec.ctx.terms.mk_bool(true);
        let _memo = EvalMemoSession::new();
        let scope = EvaluationCopyScope::enter(&exec).unwrap();
        assert!(pay(7, 64));
        eval_memo::put(term, &EvalValue::Bool(true));
        assert!(eval_memo::get(term).is_some());
        let attempt = exec.evaluation_attempt();
        let used = attempt.functional_work_counter();
        let paid = used.load(Ordering::Acquire);
        let fence = scope.into_construction(&exec).unwrap();
        assert!(!active());
        assert!(eval_memo::get(term).is_none());
        let _ = exec.ctx.terms.mk_int(42.into());
        assert!(fence.validate(&exec));
        assert!(attempt.is_same_attempt(&exec.evaluation_attempt()));
        assert!(used.load(Ordering::Acquire) >= paid);
    }

    #[test]
    fn construction_transition_refuses_a_live_nested_read() {
        let exec = Executor::new();
        let outer = EvaluationCopyScope::enter(&exec).unwrap();
        let inner = EvaluationCopyScope::enter(&exec).unwrap();
        assert!(inner.into_construction(&exec).is_err());
        assert!(!validate(&exec));
        drop(outer);
    }

    #[test]
    fn construction_transition_keeps_original_source_limit_during_growth() {
        let mut exec = Executor::new();
        let original_limit = exec.ctx.terms.true_memory_bytes() + 64 * 1024;
        exec.set_term_memory_limit(Some(original_limit));
        let fence = EvaluationCopyScope::enter(&exec)
            .unwrap()
            .into_construction(&exec)
            .unwrap();
        assert!(fence.validate(&exec));
        let _ = exec
            .ctx
            .terms
            .mk_int(num_bigint::BigInt::from(1u8) << (1usize << 20));
        assert!(exec.ctx.terms.true_memory_bytes() > original_limit);
        exec.set_term_memory_limit(Some(original_limit + 1024 * 1024));
        assert!(
            !exec.term_memory_exceeded(),
            "the live setter now permits the payload"
        );
        assert!(
            !fence.validate(&exec),
            "the original operation's ceiling cannot renew"
        );
        assert_eq!(
            exec.evaluation_stop_origin(),
            Some(UnknownOrigin::MemoryBudget)
        );
    }

    #[test]
    fn construction_transition_rejects_replaced_store_even_with_same_length() {
        let mut exec = Executor::new();
        let fence = EvaluationCopyScope::enter(&exec)
            .unwrap()
            .into_construction(&exec)
            .unwrap();
        exec.ctx.terms = exec.ctx.terms.clone();
        assert!(!fence.validate(&exec));
    }

    #[test]
    fn construction_transition_rejects_attempt_replacement_inside_original_callback() {
        let exec = Rc::new(Executor::new());
        CALLBACK_EXECUTOR.with(|slot| *slot.borrow_mut() = Some(Rc::clone(&exec)));
        let arm = Arc::new(AtomicBool::new(false));
        let watch = Arc::clone(&arm);
        let _original_stop = ay_core::resource::enter_check_stop(Arc::new(move || {
            if watch.swap(false, Ordering::AcqRel) {
                let exec = CALLBACK_EXECUTOR
                    .with(|slot| slot.borrow().clone())
                    .unwrap();
                let read = exec.begin_external_evaluation_read();
                CALLBACK_READ.with(|slot| *slot.borrow_mut() = Some(read));
            }
            false
        }));
        let fence = EvaluationCopyScope::enter(&exec)
            .unwrap()
            .into_construction(&exec)
            .unwrap();
        arm.store(true, Ordering::Release);
        assert!(!fence.validate(&exec));
        assert!(!arm.load(Ordering::Acquire));
        drop(fence);
        CALLBACK_READ.with(|slot| slot.borrow_mut().take());
        CALLBACK_EXECUTOR.with(|slot| slot.borrow_mut().take());
    }

    #[test]
    fn unrestricted_unknown_results_keep_the_existing_memo_behavior() {
        assert!(!active());
        let mut exec = Executor::new();
        let term = exec.ctx.terms.mk_bool(true);
        let _memo = EvalMemoSession::new();
        eval_memo::put(term, &EvalValue::Unknown);
        assert_eq!(eval_memo::get(term), Some(EvalValue::Unknown));
    }

    #[test]
    fn a_later_admission_callback_cannot_replace_the_original_read_attempt() {
        let mut exec = Executor::new();
        let term = exec.ctx.terms.mk_bool(true);
        let exec = Rc::new(exec);
        CALLBACK_EXECUTOR.with(|slot| *slot.borrow_mut() = Some(Rc::clone(&exec)));
        let used = exec.evaluation_attempt().functional_work_counter();
        let threshold = Arc::new(AtomicUsize::new(usize::MAX));
        let arm = Arc::new(AtomicBool::new(true));
        let watch_threshold = Arc::clone(&threshold);
        let watch_arm = Arc::clone(&arm);
        let _original_stop = ay_core::resource::enter_check_stop(Arc::new(move || {
            if used.load(Ordering::Acquire) >= watch_threshold.load(Ordering::Acquire)
                && watch_arm.swap(false, Ordering::AcqRel)
            {
                let exec = CALLBACK_EXECUTOR
                    .with(|slot| slot.borrow().clone())
                    .unwrap();
                let read = exec.begin_external_evaluation_read();
                CALLBACK_READ.with(|slot| *slot.borrow_mut() = Some(read));
            }
            false
        }));
        let scope = EvaluationCopyScope::enter(&exec).unwrap();
        threshold.store(
            exec.evaluation_attempt()
                .functional_work_counter()
                .load(Ordering::Acquire)
                + 1,
            Ordering::Release,
        );
        assert!(matches!(
            exec.evaluate_term(&Model::empty(), term),
            EvalValue::Unknown
        ));
        assert!(
            !arm.load(Ordering::Acquire),
            "callback ran after the nonzero native-entry debit"
        );
        assert!(!validate(&exec));
        drop(scope);
        CALLBACK_READ.with(|slot| slot.borrow_mut().take());
        CALLBACK_EXECUTOR.with(|slot| slot.borrow_mut().take());
    }

    #[test]
    fn callback_clear_invalidates_original_memo_get_put_and_dependency_write() {
        let mut exec = Executor::new();
        let term = exec.ctx.terms.mk_bool(true);
        let used = exec.evaluation_attempt().functional_work_counter();
        let threshold = Arc::new(AtomicUsize::new(usize::MAX));
        let arm = Arc::new(AtomicBool::new(true));
        let watch_threshold = Arc::clone(&threshold);
        let watch_arm = Arc::clone(&arm);
        let watch_used = Arc::clone(&used);
        let _original_stop = ay_core::resource::enter_check_stop(Arc::new(move || {
            if watch_used.load(Ordering::Acquire) >= watch_threshold.load(Ordering::Acquire)
                && watch_arm.swap(false, Ordering::AcqRel)
            {
                eval_memo::clear();
            }
            false
        }));
        let _memo = EvalMemoSession::new();
        let _scope = EvaluationCopyScope::enter(&exec).unwrap();
        eval_memo::seed_for_test(term, EvalValue::Bool(false));
        threshold.store(used.load(Ordering::Acquire) + 1, Ordering::Release);
        assert_eq!(eval_memo::get(term), None);
        assert!(!arm.load(Ordering::Acquire));
        arm.store(true, Ordering::Release);
        threshold.store(used.load(Ordering::Acquire) + 1, Ordering::Release);
        eval_memo::put(term, &EvalValue::Bool(false));
        assert_eq!(eval_memo::get(term), None);
        arm.store(true, Ordering::Release);
        threshold.store(used.load(Ordering::Acquire) + 1, Ordering::Release);
        eval_memo::residual_dep_put([term], true);
        assert_eq!(eval_memo::residual_dep_get(term), None);
        assert_eq!(
            exec.evaluate_term(&Model::empty(), term),
            EvalValue::Bool(true)
        );
    }

    #[test]
    fn nested_scopes_share_cumulative_original_storage_and_out_of_order_drop() {
        let mut exec = Executor::new();
        exec.set_term_memory_limit(Some(exec.ctx.terms.true_memory_bytes() + 16_384));
        let outer = EvaluationCopyScope::enter(&exec).unwrap();
        let first = owner().unwrap();
        assert!(pay(1, 8_000));
        let inner = EvaluationCopyScope::enter(&exec).unwrap();
        assert!(Rc::ptr_eq(&first, &owner().unwrap()));
        drop(outer);
        assert!(active());
        assert!(!pay(1, 10_000));
        assert!(!pay(0, 0));
        assert_eq!(
            exec.evaluation_stop_origin(),
            Some(UnknownOrigin::MemoryBudget)
        );
        drop(inner);
        assert!(!active());
        assert!(EvaluationCopyScope::enter(&exec).is_err());
    }

    #[test]
    fn shared_native_leaf_and_memo_refuse_before_deep_sequence_copy() {
        let mut exec = Executor::new();
        let term = exec
            .ctx
            .terms
            .mk_fresh_var("retained-sequence", Sort::Seq(Box::new(Sort::String)));
        let mut model = Model::empty();
        model.completed_values.insert(
            term,
            EvalValue::Seq(vec![EvalValue::String("x".repeat(32_768))]),
        );
        let _memo = EvalMemoSession::new();
        eval_memo::seed_for_test(term, model.completed_values.get(&term).unwrap().clone());
        exec.set_term_memory_limit(Some(exec.ctx.terms.true_memory_bytes() + 16_384));
        let _scope = EvaluationCopyScope::enter(&exec).unwrap();
        assert!(matches!(
            exec.evaluate_term(&model, term),
            EvalValue::Unknown
        ));
        assert_eq!(
            exec.evaluation_stop_origin(),
            Some(UnknownOrigin::MemoryBudget)
        );
        assert!(matches!(eval_memo::get(term), Some(EvalValue::Unknown)));
        assert_eq!(
            model.completed_values.get(&term).unwrap(),
            &EvalValue::Seq(vec![EvalValue::String("x".repeat(32_768))])
        );
    }

    #[test]
    fn scoped_native_source_and_interrupt_cannot_fall_back_to_unmetered_copy() {
        let mut exec = Executor::new();
        let term = exec.ctx.terms.mk_bool(true);
        let model = Model::empty();
        let flag = Arc::new(AtomicBool::new(false));
        exec.set_interrupt(Arc::clone(&flag));
        let scope = EvaluationCopyScope::enter(&exec).unwrap();
        let foreign = Executor::new();
        assert!(EvaluationCopyScope::enter(&foreign).is_err());
        assert!(!validate(&exec));
        assert_eq!(equal_slice(&[], &[EvalValue::Bool(true)]), None);
        assert_eq!(position(&[], &[]), None);
        drop(scope);
        exec.begin_external_decision_query(false);
        let scope = EvaluationCopyScope::enter(&exec).unwrap();
        flag.store(true, Ordering::Release);
        assert!(matches!(
            exec.evaluate_term(&model, term),
            EvalValue::Unknown
        ));
        assert_eq!(
            exec.evaluation_stop_origin(),
            Some(UnknownOrigin::InterruptFlag)
        );
        drop(scope);
    }

    #[test]
    fn appended_source_invalidates_the_original_snapshot_before_leaf_evaluation() {
        let mut exec = Executor::new();
        let term = exec.ctx.terms.mk_bool(true);
        let _scope = EvaluationCopyScope::enter(&exec).unwrap();
        exec.ctx.terms.mk_fresh_var("changed-source", Sort::Int);
        assert!(matches!(
            exec.evaluate_term(&Model::empty(), term),
            EvalValue::Unknown
        ));
        assert!(!validate(&exec));
    }

    #[test]
    fn unknown_nested_elements_never_become_equality_evidence_in_the_scope() {
        let exec = Executor::new();
        let _scope = EvaluationCopyScope::enter(&exec).unwrap();
        assert_eq!(
            equal_slice(&[EvalValue::Unknown], &[EvalValue::Unknown]),
            None
        );
    }

    #[test]
    fn extract_with_maximum_count_and_nonzero_start_returns_the_suffix() {
        let mut exec = Executor::new();
        let sort = Sort::Seq(Box::new(Sort::Int));
        let sequence = exec.ctx.terms.mk_fresh_var("extract-source", sort.clone());
        let start = exec.ctx.terms.mk_int(1.into());
        let count = exec.ctx.terms.mk_int(num_bigint::BigInt::from(usize::MAX));
        let extract = exec.ctx.terms.mk_app(
            ay_core::Symbol::named("seq.extract"),
            vec![sequence, start, count],
            sort,
        );
        let mut model = Model::empty();
        let integer =
            |n: i64| EvalValue::Rational(num_rational::BigRational::from_integer(n.into()));
        model.completed_values.insert(
            sequence,
            EvalValue::Seq(vec![integer(1), integer(2), integer(3)]),
        );
        let _scope = EvaluationCopyScope::enter(&exec).unwrap();
        assert_eq!(
            exec.evaluate_term(&model, extract),
            EvalValue::Seq(vec![integer(2), integer(3)])
        );
    }

    #[test]
    fn direct_completed_sequence_and_output_growth_use_the_same_scope() {
        let mut exec = Executor::new();
        let sort = Sort::Seq(Box::new(Sort::String));
        let sequence = exec.ctx.terms.mk_fresh_var("copy-source", sort.clone());
        let concatenation = exec.ctx.terms.mk_app(
            ay_core::Symbol::named("seq.++"),
            vec![sequence, sequence],
            sort,
        );
        let mut model = Model::empty();
        model.completed_values.insert(
            sequence,
            EvalValue::Seq(vec![EvalValue::String("payload".to_string())]),
        );
        let scope = EvaluationCopyScope::enter(&exec).unwrap();
        assert_eq!(
            exec.evaluate_term(&model, concatenation),
            EvalValue::Seq(vec![
                EvalValue::String("payload".to_string()),
                EvalValue::String("payload".to_string())
            ])
        );
        assert!(validate(&exec));
        drop(scope);
        exec.begin_external_decision_query(false);
        exec.set_term_memory_limit(Some(exec.ctx.terms.true_memory_bytes() + 8192));
        model.completed_values.insert(
            sequence,
            EvalValue::Seq(vec![EvalValue::String("large payload".repeat(2048))]),
        );
        let _scope = EvaluationCopyScope::enter(&exec).unwrap();
        assert!(matches!(
            exec.evaluate_term(&model, sequence),
            EvalValue::Unknown
        ));
        assert_eq!(
            exec.evaluation_stop_origin(),
            Some(UnknownOrigin::MemoryBudget)
        );
    }
}
