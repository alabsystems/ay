// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{CancellationToken, ChcParser, InvariantModel, PdrConfig};
use ay_core::resource::{enter_check_stop, ChildSpec, Guard, NodeLabel};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

fn fixture(config: PdrConfig) -> (PdrSolver, InvariantModel) {
    let problem = ChcParser::parse(
        "(set-logic HORN)
         (declare-fun Inv (Bool Bool) Bool)
         (assert (forall ((x Bool) (y Bool))
             (=> (and x y) (Inv x y))))
         (check-sat)",
    )
    .unwrap();
    assert_eq!(problem.clauses().len(), 1);
    let model = InvariantModel::parse_smtlib(
        "(define-fun Inv ((a Bool) (b Bool)) Bool (and a b))",
        &problem,
    )
    .unwrap();
    (PdrSolver::new(problem, config), model)
}

fn config(token: &CancellationToken, external: bool) -> PdrConfig {
    let mut config = PdrConfig::production(false);
    if external {
        config.external_cancellation_token = Some(token.clone());
    } else {
        config.cancellation_token = Some(token.clone());
    }
    config
}

#[test]
fn final_exact_transition_observes_config_only_cancellation() {
    for external in [false, true] {
        let token = CancellationToken::new();
        let (mut solver, model) = fixture(config(&token, external));
        let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(100_000)));
        let _guard = guard.enter();
        let work = guard.clone();
        let cancelled = token.clone();
        let observed = Arc::new(AtomicBool::new(false));
        let callback_observed = Arc::clone(&observed);
        let _callback = enter_check_stop(Arc::new(move || {
            // Capture and between-clause polls debit no structural work. The
            // first positive tick is inside the ONLY (and final) exact proof.
            if work.ticks() > 0 {
                callback_observed.store(true, Ordering::Release);
                cancelled.cancel();
            }
            false // Refusal comes from the config token, never the callback.
        }));
        assert!(!solver.verify_model(&model));
        assert!(observed.load(Ordering::Acquire));
        assert!(token.is_cancelled());
        assert!(guard.ticks() > 0);
    }
}

#[test]
fn healthy_config_tokens_preserve_direct_exact_model_validation() {
    for external in [false, true] {
        let token = CancellationToken::new();
        let (mut solver, model) = fixture(config(&token, external));
        let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(100_000)));
        let _guard = guard.enter();
        let work = guard.clone();
        let observed = Arc::new(AtomicBool::new(false));
        let callback_observed = Arc::clone(&observed);
        let _callback = enter_check_stop(Arc::new(move || {
            if work.ticks() > 0 {
                callback_observed.store(true, Ordering::Release);
            }
            false
        }));
        assert!(solver.verify_model(&model));
        assert!(observed.load(Ordering::Acquire));
        assert!(!token.is_cancelled());
    }
}

#[test]
fn configured_owner_retains_ambient_lane_and_raw_interrupt_after_scope_exit() {
    for raw in [false, true] {
        let configured = CancellationToken::new();
        let ambient = CancellationToken::new();
        let interrupt = Arc::new(AtomicBool::new(false));
        let (solver, _) = fixture(config(&configured, false));
        let lane = ScopedLaneCancellation::install(ambient.clone(), Some(interrupt.clone()));
        let mut owner = solver.structural_verification_owner().unwrap();
        drop(lane);
        if raw {
            interrupt.store(true, Ordering::Release);
        } else {
            ambient.cancel();
        }
        assert_eq!(owner.poll(), Err(Error::Stopped));
        interrupt.store(false, Ordering::Release);
        ambient.reset();
        assert_eq!(owner.poll(), Err(Error::Stopped));
        assert!(!configured.is_cancelled());
    }
}
