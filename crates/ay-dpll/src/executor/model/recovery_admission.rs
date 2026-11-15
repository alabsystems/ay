// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared admission for one private model-recovery transaction.
//!
//! Local parsers retain their normal limits. While this scope is installed,
//! every fresh local budget also borrows the SAME aggregate ledger and the
//! original query controls. Neither retries nor rollback refund consumed work.

use std::cell::RefCell;
use std::rc::Rc;

use ay_core::resource::Guard;

use crate::executor::theories::FpStop;
use crate::executor::Executor;

thread_local! {
    static ACTIVE: RefCell<Option<RecoveryAdmission>> = const { RefCell::new(None) };
}

#[derive(Clone)]
pub(super) struct RecoveryAdmission(Rc<Owner>);

struct Owner {
    ledger: RefCell<Ledger>,
    guard: Option<Guard>,
    stopped: Box<dyn Fn() -> bool>,
    source: Option<ay_core::term::TermStoreSnapshotStamp>,
}

struct Ledger {
    work_left: usize,
    bytes_left: usize,
    refused: bool,
}

pub(super) struct RecoveryScope {
    admission: RecoveryAdmission,
}

impl RecoveryScope {
    /// A nested transaction cannot install a fresh allowance over its caller.
    pub(super) fn enter(exec: &Executor, work: usize, bytes: usize) -> Option<Self> {
        if RecoveryAdmission::current().is_some() {
            return None;
        }
        let stop = FpStop::from_executor_for_term_construction(exec);
        let attempt = exec.evaluation_attempt();
        let original_stop = ay_core::resource::current_check_stop().ok()?;
        let admission = RecoveryAdmission::with_source(
            work,
            bytes,
            ay_core::resource::current_guard(),
            Box::new(move || {
                if let Some(origin) = attempt.stop_origin() {
                    attempt.record_stop(origin);
                    return true;
                }
                if let Err(origin) = stop.check() {
                    attempt.record_stop(origin);
                    return true;
                }
                if ay_core::resource::process_cancelled()
                    || original_stop.as_ref().is_some_and(|stop| stop())
                {
                    attempt.record_stop(crate::executor_types::UnknownOrigin::IncompleteSolverLane);
                    return true;
                }
                false
            }),
            Some(exec.ctx.terms.snapshot_stamp()),
        );
        ACTIVE.with(|active| *active.borrow_mut() = Some(admission.clone()));
        let scope = Self { admission };
        // Install the scope before polling the original callback: reentrant
        // recovery must already see this owner and cannot open a fresh meter.
        if !scope.admission.pay(0, 0) {
            return None;
        }
        Some(scope)
    }

    pub(super) fn admission(&self) -> RecoveryAdmission {
        self.admission.clone()
    }
}

impl Drop for RecoveryScope {
    fn drop(&mut self) {
        ACTIVE.with(|active| {
            let mut active = active.borrow_mut();
            if active
                .as_ref()
                .is_some_and(|value| Rc::ptr_eq(&value.0, &self.admission.0))
            {
                *active = None;
            }
        });
    }
}

impl RecoveryAdmission {
    #[cfg(test)]
    fn new(
        work: usize,
        bytes: usize,
        guard: Option<Guard>,
        stopped: Box<dyn Fn() -> bool>,
    ) -> Self {
        Self::with_source(work, bytes, guard, stopped, None)
    }

    fn with_source(
        work: usize,
        bytes: usize,
        guard: Option<Guard>,
        stopped: Box<dyn Fn() -> bool>,
        source: Option<ay_core::term::TermStoreSnapshotStamp>,
    ) -> Self {
        Self(Rc::new(Owner {
            ledger: RefCell::new(Ledger {
                work_left: work,
                bytes_left: bytes,
                refused: false,
            }),
            guard,
            stopped,
            source,
        }))
    }

    pub(super) fn current() -> Option<Self> {
        ACTIVE.with(|active| active.borrow().clone())
    }

    /// Resource ownership only. This equality grants no assertion, declaration
    /// or model authority and deliberately does not accept an appended prefix.
    pub(super) fn current_for(exec: &Executor) -> Option<Self> {
        Self::current().filter(|admission| {
            admission
                .0
                .source
                .as_ref()
                .is_some_and(|source| source == &exec.ctx.terms.snapshot_stamp())
        })
    }

    pub(super) fn pay(&self, work: usize, bytes: usize) -> bool {
        {
            let mut ledger = self.0.ledger.borrow_mut();
            if ledger.refused {
                return false;
            }
            let Some(work_left) = ledger.work_left.checked_sub(work) else {
                ledger.refused = true;
                return false;
            };
            let Some(bytes_left) = ledger.bytes_left.checked_sub(bytes) else {
                ledger.refused = true;
                return false;
            };
            // Debit BEFORE calling user controls. A finite reentrant read
            // spends the same ledger, and callback panic cannot refund work.
            ledger.work_left = work_left;
            ledger.bytes_left = bytes_left;
        }
        struct RefuseOnUnwind<'a> {
            owner: &'a RecoveryAdmission,
            armed: bool,
        }
        impl Drop for RefuseOnUnwind<'_> {
            fn drop(&mut self) {
                if self.armed {
                    self.owner.refuse();
                }
            }
        }
        let mut poll = RefuseOnUnwind {
            owner: self,
            armed: true,
        };
        let guarded = u64::try_from(work).ok().is_some_and(|work| {
            self.0
                .guard
                .as_ref()
                .is_none_or(|guard| guard.tick(work).is_ok())
        });
        let stopped = !guarded || (self.0.stopped)();
        let mut ledger = self.0.ledger.borrow_mut();
        if stopped {
            ledger.refused = true;
        }
        poll.armed = false;
        !ledger.refused
    }

    pub(super) fn refuse(&self) {
        self.0.ledger.borrow_mut().refused = true;
    }
}

/// Outside a private transaction this is exactly a no-op. Cloned handles in
/// parser budgets keep the same original ledger after its TLS frame is gone.
pub(super) fn pay_current(work: usize, bytes: usize) -> bool {
    super::evaluation_copies::pay(work, bytes)
        && RecoveryAdmission::current().is_none_or(|admission| admission.pay(work, bytes))
}

pub(super) fn pay_for(exec: &Executor, work: usize, bytes: usize) -> bool {
    super::evaluation_copies::validate(exec)
        && super::evaluation_copies::pay(work, bytes)
        && RecoveryAdmission::current_for(exec).is_none_or(|admission| admission.pay(work, bytes))
        && super::evaluation_copies::validate(exec)
}

pub(super) fn refuse_current() {
    if let Some(admission) = RecoveryAdmission::current() {
        admission.refuse();
    }
}

pub(super) fn pay_model_value_copy(value: &ay_model_check::ModelValue) -> bool {
    if RecoveryAdmission::current().is_none() {
        return true;
    }
    let admitted = super::rendered_dt_limits::model_value_work(value)
        .is_some_and(|amount| pay_current(amount, amount));
    if !admitted {
        refuse_current();
    }
    admitted
}

/// Preflight the producer's borrowed value BEFORE its conversion/clone. The
/// recovery protocol has no algebraic/FP owner; those payloads conservatively
/// decline here instead of rendering them just to estimate their size.
pub(super) fn pay_eval_value_copy(value: &super::EvalValue) -> bool {
    if super::evaluation_copies::active()
        && !admit_eval_value_copy(value, super::evaluation_copies::pay)
    {
        return false;
    }
    if RecoveryAdmission::current().is_none() {
        return true;
    }
    let admitted = pay_eval_value_copy_inner(value);
    if !admitted {
        refuse_current();
    }
    admitted
}

fn pay_eval_value_copy_inner(value: &super::EvalValue) -> bool {
    walk_eval_value_copy(value, 0, CopyPayloads::Recovery, &mut pay_current)
}

#[derive(Clone, Copy)]
enum CopyPayloads {
    Recovery,
    Native,
}

/// Inspect borrowed data before copying it, charging the caller's ORIGINAL
/// owner. No allowance is created here; a false callback stops the walk.
/// The depth bound is the existing recovery bound, also protecting the native
/// call stack. Counts retain recovery's conservative bit-as-byte pricing.
pub(super) fn admit_eval_value_copy(
    value: &super::EvalValue,
    mut pay: impl FnMut(usize, usize) -> bool,
) -> bool {
    walk_eval_value_copy(value, 0, CopyPayloads::Native, &mut pay)
}

fn walk_eval_value_copy(
    value: &super::EvalValue,
    depth: usize,
    policy: CopyPayloads,
    pay: &mut impl FnMut(usize, usize) -> bool,
) -> bool {
    use super::EvalValue;
    if depth > 32 || !pay(1, std::mem::size_of::<EvalValue>()) {
        return false;
    }
    let payload = match value {
        EvalValue::Bool(_) | EvalValue::Unknown => 1,
        EvalValue::FiniteField { .. } => {
            std::mem::size_of::<u32>() + std::mem::size_of::<ay_core::FiniteFieldSort>()
        }
        EvalValue::Element(value) | EvalValue::String(value) => value.len(),
        EvalValue::Rational(value) if matches!(policy, CopyPayloads::Native) => {
            if !pay_rational_copy(value, pay) {
                return false;
            }
            0
        }
        EvalValue::Rational(value) => {
            let Some(bits) = value.numer().bits().checked_add(value.denom().bits()) else {
                return false;
            };
            let Ok(bits) = usize::try_from(bits) else {
                return false;
            };
            bits
        }
        EvalValue::BitVec { value, width } => {
            let Ok(bits) = usize::try_from(value.bits().max(u64::from(*width))) else {
                return false;
            };
            bits
        }
        EvalValue::Complex { real, imaginary } => {
            if !pay(2, 2 * std::mem::size_of::<(&EvalValue, usize)>()) {
                return false;
            }
            if !walk_eval_value_copy(real, depth + 1, policy, pay)
                || !walk_eval_value_copy(imaginary, depth + 1, policy, pay)
            {
                return false;
            }
            0
        }
        EvalValue::Seq(values) => {
            let Some(bytes) = values
                .len()
                .checked_mul(std::mem::size_of::<(&EvalValue, usize)>())
            else {
                return false;
            };
            if !pay(values.len(), bytes) {
                return false;
            }
            for value in values {
                if !walk_eval_value_copy(value, depth + 1, policy, pay) {
                    return false;
                }
            }
            0
        }
        EvalValue::Fp(value) if matches!(policy, CopyPayloads::Native) => {
            let Some(bytes) = fp_copy_payload_bytes(value) else {
                return false;
            };
            bytes
        }
        EvalValue::Algebraic(value) if matches!(policy, CopyPayloads::Native) => {
            if !value.visit_copy_coefficients(|coefficient| pay_rational_copy(coefficient, pay)) {
                return false;
            }
            0
        }
        EvalValue::Algebraic(_) | EvalValue::Fp(_) => return false,
    };
    if !pay(payload, payload) {
        return false;
    }
    true
}

fn pay_rational_copy(
    value: &num_rational::BigRational,
    pay: &mut impl FnMut(usize, usize) -> bool,
) -> bool {
    let Some(bits) = value.numer().bits().checked_add(value.denom().bits()) else {
        return false;
    };
    let Ok(bits) = usize::try_from(bits) else {
        return false;
    };
    // Account each independently allocated limb even for tiny coefficients.
    let Some(limbs) = value
        .numer()
        .bits()
        .div_ceil(64)
        .checked_add(value.denom().bits().div_ceil(64))
    else {
        return false;
    };
    let Some(limb_bytes) = limbs.checked_mul(8).and_then(|n| usize::try_from(n).ok()) else {
        return false;
    };
    let Some(bytes) = bits
        .max(limb_bytes)
        .checked_add(std::mem::size_of::<num_rational::BigRational>())
    else {
        return false;
    };
    pay(bits.saturating_add(1), bytes)
}

/// SMT structural FP equality, including abstract NaN and distinct signed
/// zeros. Unlike `EvalValue::PartialEq`, this never renders dense bit strings.
/// Both borrowed operands are admitted before classification/field scans.
pub(super) fn admitted_fp_equal(
    left: &ay_fp::FpModelValue,
    right: &ay_fp::FpModelValue,
    mut pay: impl FnMut(usize, usize) -> bool,
) -> Option<bool> {
    for value in [left, right] {
        let bytes = fp_copy_payload_bytes(value)?;
        if !pay(bytes, bytes) {
            return None;
        }
    }
    if left.eb() != right.eb() || left.sb() != right.sb() {
        return pay(0, 0).then_some(false);
    }
    let left = fp_view(left)?;
    let right = fp_view(right)?;
    let equal = match (left, right) {
        (FpView::NaN, FpView::NaN) => true,
        (FpView::Zero(a), FpView::Zero(b)) | (FpView::Infinity(a), FpView::Infinity(b)) => a == b,
        (FpView::Finite(a, ae, af), FpView::Finite(b, be, bf)) => {
            a == b && ae.equals(be) && af.equals(bf)
        }
        _ => false,
    };
    pay(0, 0).then_some(equal)
}

/// Borrowed FP data admission is independent of arithmetic/term-encoding
/// format limits. Validate raw widths without constructing or rendering a
/// value, and conservatively price occupied limbs for copies and field scans.
pub(super) fn fp_copy_payload_bytes(value: &ay_fp::FpModelValue) -> Option<usize> {
    use ay_fp::FpModelValue;
    if value.eb() < 2 || value.sb() < 2 || value.eb().checked_add(value.sb()).is_none() {
        return None;
    }
    let (exponent_bits, fraction_bits) = match value {
        FpModelValue::Exact(fields) => (fields.exponent().bits(), fields.significand().bits()),
        FpModelValue::Fp {
            exponent,
            significand,
            ..
        } => (
            u64::from(u64::BITS - exponent.leading_zeros()),
            u64::from(u128::BITS - significand.leading_zeros()),
        ),
        _ => (0, 0),
    };
    if exponent_bits > u64::from(value.eb()) || fraction_bits >= u64::from(value.sb()) {
        return None;
    }
    let occupied = exponent_bits.checked_add(fraction_bits)?;
    usize::try_from(occupied.div_ceil(64))
        .ok()?
        .checked_mul(4 * std::mem::size_of::<u64>())?
        .checked_add(4096)
}

#[derive(Clone, Copy)]
enum Field<'a> {
    Native(u128),
    Exact(&'a num_bigint::BigUint),
}

impl Field<'_> {
    fn bits(self) -> u64 {
        match self {
            Self::Native(value) => u64::from(u128::BITS - value.leading_zeros()),
            Self::Exact(value) => value.bits(),
        }
    }

    fn all_ones(self, width: u32) -> bool {
        if self.bits() != u64::from(width) {
            return false;
        }
        match self {
            Self::Native(value) => {
                128u32
                    .checked_sub(width)
                    .and_then(|shift| u128::MAX.checked_shr(shift))
                    == Some(value)
            }
            Self::Exact(value) => value.iter_u64_digits().enumerate().all(|(index, digit)| {
                let remaining = u64::from(width) - index as u64 * 64;
                digit
                    == if remaining >= 64 {
                        u64::MAX
                    } else {
                        (1u64 << remaining) - 1
                    }
            }),
        }
    }

    fn equals(self, other: Self) -> bool {
        use num_traits::ToPrimitive;
        match (self, other) {
            (Self::Native(a), Self::Native(b)) => a == b,
            (Self::Exact(a), Self::Exact(b)) => a == b,
            (Self::Exact(a), Self::Native(b)) | (Self::Native(b), Self::Exact(a)) => {
                a.to_u128() == Some(b)
            }
        }
    }
}

enum FpView<'a> {
    NaN,
    Zero(bool),
    Infinity(bool),
    Finite(bool, Field<'a>, Field<'a>),
}

fn fp_view(value: &ay_fp::FpModelValue) -> Option<FpView<'_>> {
    use ay_fp::FpModelValue;
    let (sign, exponent, fraction) = match value {
        FpModelValue::NaN { .. } => return Some(FpView::NaN),
        FpModelValue::PosZero { .. } => return Some(FpView::Zero(false)),
        FpModelValue::NegZero { .. } => return Some(FpView::Zero(true)),
        FpModelValue::PosInf { .. } => return Some(FpView::Infinity(false)),
        FpModelValue::NegInf { .. } => return Some(FpView::Infinity(true)),
        FpModelValue::Fp {
            sign,
            exponent,
            significand,
            ..
        } => (
            *sign,
            Field::Native(u128::from(*exponent)),
            Field::Native(*significand),
        ),
        FpModelValue::Exact(fields) => (
            fields.sign(),
            Field::Exact(fields.exponent()),
            Field::Exact(fields.significand()),
        ),
    };
    if exponent.bits() > u64::from(value.eb()) || fraction.bits() >= u64::from(value.sb()) {
        return None;
    }
    Some(if exponent.all_ones(value.eb()) {
        if fraction.bits() == 0 {
            FpView::Infinity(sign)
        } else {
            FpView::NaN
        }
    } else if exponent.bits() == 0 && fraction.bits() == 0 {
        FpView::Zero(sign)
    } else {
        FpView::Finite(sign, exponent, fraction)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn borrowed_copy_pays_nested_fp_payload_and_shares_cumulative_refusal() {
        use super::super::EvalValue;
        use num_bigint::BigUint;
        let fp = ay_fp::FpModelValue::from_exact_fields(
            false,
            BigUint::from(127u32),
            BigUint::from(1u8) << 198usize,
            8,
            200,
        )
        .unwrap();
        let value = EvalValue::Seq(vec![EvalValue::Fp(fp)]);
        let mut total = 0usize;
        assert!(admit_eval_value_copy(&value, |_, bytes| {
            total = total.checked_add(bytes).unwrap();
            true
        }));
        assert!(total > 4096);
        let mut left = total;
        let mut refused = false;
        let mut pay = |_: usize, bytes: usize| {
            if refused || bytes > left {
                refused = true;
                false
            } else {
                left -= bytes;
                true
            }
        };
        assert!(admit_eval_value_copy(&value, &mut pay));
        assert!(!admit_eval_value_copy(&value, &mut pay));
        assert!(!admit_eval_value_copy(&value, &mut pay));
    }

    #[test]
    fn borrowed_copy_refuses_before_deep_or_variable_payload_walk() {
        use super::super::EvalValue;
        let value = EvalValue::String("retained payload".repeat(100));
        let mut calls = 0;
        assert!(!admit_eval_value_copy(&value, |_, _| {
            calls += 1;
            false
        }));
        assert_eq!(calls, 1);
        let mut deep = EvalValue::Bool(true);
        for _ in 0..34 {
            deep = EvalValue::Seq(vec![deep]);
        }
        assert!(!admit_eval_value_copy(&deep, |_, _| true));
    }

    #[test]
    fn admitted_fp_equality_preserves_nan_zero_and_wide_raw_fields() {
        use ay_fp::FpModelValue as Fp;
        use num_bigint::BigUint;
        let exact = Fp::from_exact_fields(
            false,
            BigUint::from(127u32),
            BigUint::from(1u8) << 198usize,
            8,
            200,
        )
        .unwrap();
        assert_eq!(admitted_fp_equal(&exact, &exact, |_, _| true), Some(true));
        assert_eq!(admitted_fp_equal(&exact, &exact, |_, _| false), None);
        assert_eq!(
            admitted_fp_equal(
                &Fp::PosZero { eb: 8, sb: 200 },
                &Fp::NegZero { eb: 8, sb: 200 },
                |_, _| true
            ),
            Some(false)
        );
        let raw_nan = Fp::Fp {
            sign: true,
            exponent: 255,
            significand: 7,
            eb: 8,
            sb: 129,
        };
        assert_eq!(
            admitted_fp_equal(&raw_nan, &Fp::NaN { eb: 8, sb: 129 }, |_, _| true),
            Some(true)
        );
        let exact_inf = Fp::from_exact_fields(
            false,
            (BigUint::from(1u8) << 80usize) - BigUint::from(1u8),
            BigUint::from(0u8),
            80,
            200,
        )
        .unwrap();
        assert_eq!(
            admitted_fp_equal(&exact_inf, &Fp::PosInf { eb: 80, sb: 200 }, |_, _| true),
            Some(true)
        );
        let mut polls = 0;
        assert_eq!(
            admitted_fp_equal(&exact, &exact, |_, _| {
                polls += 1;
                polls < 3
            }),
            None
        );
        let malformed = Fp::Fp {
            sign: false,
            exponent: 256,
            significand: 0,
            eb: 8,
            sb: 200,
        };
        assert_eq!(admitted_fp_equal(&malformed, &malformed, |_, _| true), None);
    }

    #[test]
    fn finite_field_copy_pays_its_original_storage_boundary_and_keeps_refusal_sticky() {
        use super::super::EvalValue;
        assert!(RecoveryAdmission::current().is_none());
        let field = ay_core::FiniteFieldSort::new(ay_core::MAX_FINITE_FIELD_MODULUS).unwrap();
        let value = EvalValue::FiniteField {
            value: field.modulus() - 1,
            field,
        };
        let copy_bytes = std::mem::size_of::<EvalValue>()
            + std::mem::size_of::<u32>()
            + std::mem::size_of::<ay_core::FiniteFieldSort>();
        for (bytes, expected) in [(copy_bytes - 1, false), (copy_bytes, true)] {
            let admission = RecoveryAdmission::new(100, bytes, None, Box::new(|| false));
            let retained = admission.clone();
            ACTIVE.with(|active| *active.borrow_mut() = Some(admission.clone()));
            let scope = RecoveryScope { admission };
            assert_eq!(pay_eval_value_copy(&value), expected);
            assert!(!pay_eval_value_copy(&value));
            assert!(!retained.pay(0, 0));
            drop(scope);
            assert!(RecoveryAdmission::current().is_none());
            assert!(!retained.pay(0, 0));
        }
        let admission = RecoveryAdmission::new(100, 1000, None, Box::new(|| true));
        ACTIVE.with(|active| *active.borrow_mut() = Some(admission.clone()));
        let _scope = RecoveryScope { admission };
        assert!(!pay_eval_value_copy(&value));
        assert!(!RecoveryAdmission::current().unwrap().pay(0, 0));
    }

    #[test]
    fn aggregate_refusal_is_shared_and_never_refunded() {
        let admission = RecoveryAdmission::new(3, 7, None, Box::new(|| false));
        let retry = admission.clone();
        assert!(admission.pay(2, 6));
        assert!(!retry.pay(2, 0));
        assert!(!admission.pay(0, 0));
    }

    #[test]
    fn a_stop_observed_once_stays_refused() {
        let stopped = Cell::new(true);
        let admission =
            RecoveryAdmission::new(30, 70, None, Box::new(move || stopped.replace(false)));
        assert!(!admission.pay(0, 0));
        assert!(!admission.clone().pay(0, 0));
    }

    #[test]
    fn scope_unwind_restores_tls_without_refunding_retained_budget() {
        assert!(RecoveryAdmission::current().is_none());
        let admission = RecoveryAdmission::new(3, 7, None, Box::new(|| false));
        let retained = admission.clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            ACTIVE.with(|active| *active.borrow_mut() = Some(admission.clone()));
            let _scope = RecoveryScope { admission };
            assert!(retained.pay(2, 6));
            panic!("private candidate unwind");
        }));
        assert!(result.is_err());
        assert!(RecoveryAdmission::current().is_none());
        assert!(!retained.pay(2, 0));
    }

    #[test]
    fn fresh_local_schema_budgets_share_one_aggregate_storage_limit() {
        use super::super::rendered_dt_limits::SchemaSourceBudget;
        assert!(RecoveryAdmission::current().is_none());
        let admission = RecoveryAdmission::new(100, 5, None, Box::new(|| false));
        ACTIVE.with(|active| *active.borrow_mut() = Some(admission.clone()));
        let scope = RecoveryScope { admission };
        let mut first = SchemaSourceBudget::new();
        assert!(first.charge_name(3));
        let mut retry = SchemaSourceBudget::new();
        assert!(!retry.charge_name(3));
        drop(scope);
        assert!(!first.charge_name(0));
        assert!(SchemaSourceBudget::new().charge_name(3));
    }

    #[test]
    fn a_finite_reentrant_stop_callback_debits_without_borrowing_the_ledger() {
        assert!(RecoveryAdmission::current().is_none());
        let entered = Cell::new(false);
        let admission = RecoveryAdmission::new(
            10,
            20,
            None,
            Box::new(move || {
                if !entered.replace(true) {
                    assert!(RecoveryAdmission::current().unwrap().pay(2, 1));
                }
                false
            }),
        );
        ACTIVE.with(|active| *active.borrow_mut() = Some(admission.clone()));
        let _scope = RecoveryScope {
            admission: admission.clone(),
        };
        assert!(admission.pay(3, 4));
        let ledger = admission.0.ledger.borrow();
        assert_eq!(ledger.work_left, 5);
        assert_eq!(ledger.bytes_left, 15);
        assert!(!ledger.refused);
    }

    #[test]
    fn a_callback_panic_keeps_the_prepaid_work_and_sticky_refusal() {
        let admission = RecoveryAdmission::new(
            10,
            20,
            None,
            Box::new(|| panic!("original stop callback panic")),
        );
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| admission.pay(3, 4)));
        assert!(result.is_err());
        let ledger = admission.0.ledger.borrow();
        assert_eq!(ledger.work_left, 7);
        assert_eq!(ledger.bytes_left, 16);
        assert!(ledger.refused);
        drop(ledger);
        assert!(!admission.pay(0, 0));
    }

    #[test]
    fn refused_owner_cannot_empty_an_unrelated_or_changed_source_window() {
        let mut owner = Executor::new();
        let owned_root = owner.ctx.terms.mk_var("owned_root", ay_core::Sort::Bool);
        owner.ctx.assertions.push(owned_root);
        let mut unrelated = Executor::new();
        let other_root = unrelated.ctx.terms.mk_bool(false);
        unrelated.ctx.assertions.push(other_root);
        let unrelated = Rc::new(unrelated);
        let observed = Rc::new(RefCell::new(Vec::new()));
        let captured_other = unrelated.clone();
        let captured_observed = observed.clone();
        let admission = RecoveryAdmission::with_source(
            1,
            100,
            None,
            Box::new(move || {
                // Exhaust the SAME owner through a genuine finite callback. The
                // different executor must still retain its complete false root.
                assert!(!RecoveryAdmission::current().unwrap().pay(1, 0));
                *captured_observed.borrow_mut() =
                    captured_other.independent_gate_query_roots().unwrap();
                false
            }),
            Some(owner.ctx.terms.snapshot_stamp()),
        );
        ACTIVE.with(|active| *active.borrow_mut() = Some(admission.clone()));
        let _scope = RecoveryScope {
            admission: admission.clone(),
        };
        assert!(!admission.pay(1, 0));
        assert_eq!(*observed.borrow(), [other_root]);
        assert_eq!(
            unrelated.independent_gate_query_roots().unwrap(),
            [other_root]
        );
        assert!(RecoveryAdmission::current_for(&owner).is_some());
        assert!(owner.independent_gate_query_roots().is_err());
        // Appending changes the EXACT snapshot identity. A prefix is not
        // enough to keep the source-bound Recovery ledger applicable.
        let _new_term = owner.ctx.terms.mk_var("new_entry", ay_core::Sort::Bool);
        // The failed read stays stopped; a genuinely new read may inspect the
        // changed source, to which the old Recovery owner does not apply.
        let _new_read = owner.begin_external_evaluation_read();
        assert!(RecoveryAdmission::current_for(&owner).is_none());
        assert_eq!(owner.independent_gate_query_roots().unwrap(), [owned_root]);
        let cloned = owner.ctx.terms.clone();
        owner.ctx.terms = cloned;
        assert!(RecoveryAdmission::current_for(&owner).is_none());
        assert_eq!(owner.independent_gate_query_roots().unwrap(), [owned_root]);
    }

    #[test]
    fn duplicate_generated_roots_pay_their_buffer_before_copying() {
        let mut exec = Executor::new();
        let root = exec.ctx.terms.mk_var("root", ay_core::Sort::Bool);
        exec.ctx.assertions = vec![root; 500];
        let admission = RecoveryAdmission::with_source(
            10_000,
            4,
            None,
            Box::new(|| false),
            Some(exec.ctx.terms.snapshot_stamp()),
        );
        ACTIVE.with(|active| *active.borrow_mut() = Some(admission.clone()));
        let _scope = RecoveryScope {
            admission: admission.clone(),
        };
        assert!(exec.independent_gate_query_roots().is_err());
        assert_eq!(exec.ctx.assertions.len(), 500);
        assert!(!admission.pay(0, 0));
    }
    #[test]
    fn unavailable_roots_withhold_array_and_independent_model_authority() {
        use crate::executor::model::Model;
        use crate::executor_types::UnknownOrigin;
        let mut exec = Executor::new();
        exec.execute_all(
            &ay_frontend::parse("(declare-const a (Array Int Int)) (assert (= (select a 0) 1))")
                .unwrap(),
        )
        .unwrap();
        exec.last_model = Some(Model::empty());
        let roots = exec.independent_gate_query_roots().unwrap();
        assert!(!roots.is_empty());
        assert_eq!(exec.problem_has_array(), Ok(true));
        let _scope = RecoveryScope::enter(&exec, 0, 0).unwrap();
        assert_eq!(
            exec.independent_gate_query_roots(),
            Err(UnknownOrigin::DeterministicResourceBudget)
        );
        assert_eq!(
            exec.problem_has_array(),
            Err(UnknownOrigin::DeterministicResourceBudget)
        );
        assert_eq!(
            exec.array_select_congruence_violated(exec.last_model.as_ref().unwrap()),
            Err(UnknownOrigin::DeterministicResourceBudget)
        );
        assert!(matches!(
            exec.confirm_sat_with_independent_gate(),
            ay_model_check::GateVerdict::CannotConfirm { .. }
        ));
        assert!(exec
            .gate_emit_reconstructions(exec.last_model.as_ref().unwrap())
            .is_err());
        assert_eq!(exec.ctx.assertions, roots);
    }
}
