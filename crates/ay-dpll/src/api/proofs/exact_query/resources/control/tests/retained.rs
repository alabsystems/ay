// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retained publication differs from the legacy completed-check contract.

use super::*;

struct Dropped<'a>(&'a Cell<bool>);

impl Drop for Dropped<'_> {
    fn drop(&mut self) {
        self.0.set(true);
    }
}

#[test]
fn retained_cleanup_refusal_drops_result_and_stays_sticky() {
    let temporary_dropped = Cell::new(false);
    let result_dropped = Cell::new(false);
    let calls = Cell::new(0);
    let mut progress = |work, bytes| {
        assert_eq!((work, bytes), (0, 0));
        calls.set(calls.get() + 1);
        !temporary_dropped.get()
    };
    let mut control = Control::new(&mut progress);
    let result = control.run_retained(|_| {
        let _temporary = Dropped(&temporary_dropped);
        Ok(Dropped(&result_dropped))
    });
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert!(temporary_dropped.get());
    assert!(
        result_dropped.get(),
        "late refusal must destroy the result owner"
    );
    assert_eq!(calls.get(), 2, "admission and retained publication only");
    assert_eq!(control.charge(0, 0), Err(ProofCheckError::ResourceLimit));
    assert_eq!(
        control.run_retained::<()>(|_| panic!("refused control cannot retry")),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(calls.get(), 2, "refusal must not call user code again");
}

#[test]
fn retained_control_keeps_live_results_and_observed_refusals() {
    let calls = Cell::new(0);
    let mut live = |_, _| {
        calls.set(calls.get() + 1);
        true
    };
    assert_eq!(Control::new(&mut live).run_retained(|_| Ok(17)), Ok(17));
    assert_eq!(calls.get(), 2);
    let genuine = ProofCheckError::NoClauseProducingSteps;
    assert_eq!(
        Control::new(&mut live).run_retained::<()>(|_| Err(genuine.clone())),
        Err(genuine)
    );
    assert_eq!(
        calls.get(),
        4,
        "live validation errors keep the same final control"
    );
    let mut refusing = |_, _| {
        calls.set(calls.get() + 1);
        calls.get() != 6
    };
    let mut control = Control::new(&mut refusing);
    assert_eq!(
        control.run_retained(|control| {
            assert_eq!(control.charge(1, 0), Err(ProofCheckError::ResourceLimit));
            Ok(17) // An inner guard cannot publish after swallowing refusal.
        }),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(calls.get(), 6);
    assert_eq!(control.charge(0, 0), Err(ProofCheckError::ResourceLimit));
    assert_eq!(calls.get(), 6);
}
