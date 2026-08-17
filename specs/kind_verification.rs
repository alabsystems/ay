// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Kind (k-induction) verification module.
//
// This file is derived from TLA2 codegen output for specs/kind_codegen.tla
// with Bug B fixed: `is_next` guard conditions now correctly reference
// `old.field` (pre-state) instead of the erroneous `state.field`.
//
// The TLA2 codegen bug was in tla-codegen/src/emit.rs `emit_is_next_method`:
// guard expressions used `expr_to_rust_with_state(g, true)` which emits
// `state.field`, but in `is_next(old, new)` the pre-state param is `old`.
// The fix applies `.replace("state.", "old.")` to guard parts, matching
// what was already done for primed assignment values.
//
// This file is self-contained (no tla-runtime dependency) so it can be
// compiled and tested standalone:
//   rustc --edition 2021 --test specs/kind_verification.rs -o /tmp/kind_test && /tmp/kind_test
//
// Part of #7914: TLA2 codegen pipeline for ay specs.

#![forbid(unsafe_code)]

use std::collections::HashSet;

// ---------------------------------------------------------------------------
// Minimal TLA runtime stubs (normally provided by tla-runtime crate)
// ---------------------------------------------------------------------------

/// Minimal state machine trait matching tla-runtime's `StateMachine`.
trait StateMachine {
    type State: Clone + std::fmt::Debug + PartialEq + Eq + std::hash::Hash;

    fn init(&self) -> Vec<Self::State>;
    fn next(&self, state: &Self::State) -> Vec<Self::State>;
    fn is_next(&self, old: &Self::State, new: &Self::State) -> Option<bool>;
    fn check_invariant(&self, state: &Self::State) -> Option<bool>;
}

fn range_set(lo: i64, hi: i64) -> HashSet<i64> {
    (lo..=hi).collect()
}

fn boolean_set() -> HashSet<bool> {
    let mut s = HashSet::new();
    s.insert(true);
    s.insert(false);
    s
}

macro_rules! tla_set {
    [$($elem:expr),* $(,)?] => {{
        let mut s = HashSet::new();
        $(s.insert($elem);)*
        s
    }};
}

// ---------------------------------------------------------------------------
// Generated state machine (from TLA2 codegen, Bug B fixed)
// ---------------------------------------------------------------------------

/// State for the k-induction trace contract.
///
/// Corresponds to the TLA+ VARIABLES: k, result, phase, baseCaseChecked.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct KindCodegenState {
    k: i64,
    result: String,
    phase: String,
    base_case_checked: bool,
}

struct KindCodegen;

impl StateMachine for KindCodegen {
    type State = KindCodegenState;

    fn init(&self) -> Vec<Self::State> {
        vec![Self::State {
            k: 0_i64,
            result: "Running".to_string(),
            phase: "idle".to_string(),
            base_case_checked: false,
        }]
    }

    fn next(&self, state: &Self::State) -> Vec<Self::State> {
        let mut next_states = Vec::new();

        // Action 1: CheckBaseCase
        if state.result == "Running" {
            next_states.push(Self::State {
                k: state.k,
                result: "Running".to_string(),
                phase: "base".to_string(),
                base_case_checked: true,
            });
        }

        // Action 2: CheckForwardInduction
        if state.result == "Running" && state.base_case_checked {
            next_states.push(Self::State {
                k: state.k,
                result: "Running".to_string(),
                phase: "forward".to_string(),
                base_case_checked: state.base_case_checked,
            });
        }

        // Action 3: CheckBackwardInduction
        if state.result == "Running" && state.base_case_checked {
            next_states.push(Self::State {
                k: state.k,
                result: "Running".to_string(),
                phase: "backward".to_string(),
                base_case_checked: state.base_case_checked,
            });
        }

        // Action 4: IncrementK
        if state.result == "Running" && state.k < 4_i64 && state.base_case_checked {
            next_states.push(Self::State {
                k: state.k + 1,
                result: "Running".to_string(),
                phase: "idle".to_string(),
                base_case_checked: false,
            });
        }

        // Action 5: DeclareSafe
        if state.result == "Running"
            && (state.phase == "idle"
                || (["forward", "backward"].contains(&state.phase.as_str())
                    && state.base_case_checked))
        {
            next_states.push(Self::State {
                k: state.k,
                result: "Safe".to_string(),
                phase: state.phase.clone(),
                base_case_checked: state.base_case_checked,
            });
        }

        // Action 6: DeclareUnsafe
        if state.result == "Running" && state.phase == "base" {
            next_states.push(Self::State {
                k: state.k,
                result: "Unsafe".to_string(),
                phase: state.phase.clone(),
                base_case_checked: state.base_case_checked,
            });
        }

        // Action 7: DeclareUnknown
        if state.result == "Running" {
            next_states.push(Self::State {
                k: state.k,
                result: "Unknown".to_string(),
                phase: state.phase.clone(),
                base_case_checked: state.base_case_checked,
            });
        }

        // Action 8: DeclareNotApplicable
        if state.result == "Running" {
            next_states.push(Self::State {
                k: state.k,
                result: "NotApplicable".to_string(),
                phase: state.phase.clone(),
                base_case_checked: state.base_case_checked,
            });
        }

        next_states
    }

    // Bug B fix: all guard conditions use `old.` (pre-state), not `state.`
    fn is_next(&self, old: &Self::State, new: &Self::State) -> Option<bool> {
        let result = false
            // CheckBaseCase
            || (old.result == "Running"
                && new.k == old.k
                && new.result == "Running"
                && new.phase == "base"
                && new.base_case_checked)
            // CheckForwardInduction
            || (old.result == "Running"
                && old.base_case_checked
                && new.k == old.k
                && new.result == "Running"
                && new.phase == "forward"
                && old.base_case_checked == new.base_case_checked)
            // CheckBackwardInduction
            || (old.result == "Running"
                && old.base_case_checked
                && new.k == old.k
                && new.result == "Running"
                && new.phase == "backward"
                && old.base_case_checked == new.base_case_checked)
            // IncrementK
            || (old.result == "Running"
                && old.k < 4_i64
                && old.base_case_checked
                && new.k == old.k + 1
                && new.result == "Running"
                && new.phase == "idle"
                && !new.base_case_checked)
            // DeclareSafe
            || (old.result == "Running"
                && (old.phase == "idle"
                    || (tla_set!["forward".to_string(), "backward".to_string()]
                        .contains(&old.phase)
                        && old.base_case_checked))
                && old.k == new.k
                && new.result == "Safe"
                && old.phase == new.phase
                && old.base_case_checked == new.base_case_checked)
            // DeclareUnsafe
            || (old.result == "Running"
                && old.phase == "base"
                && old.k == new.k
                && new.result == "Unsafe"
                && old.phase == new.phase
                && old.base_case_checked == new.base_case_checked)
            // DeclareUnknown
            || (old.result == "Running"
                && old.k == new.k
                && new.result == "Unknown"
                && old.phase == new.phase
                && old.base_case_checked == new.base_case_checked)
            // DeclareNotApplicable
            || (old.result == "Running"
                && old.k == new.k
                && new.result == "NotApplicable"
                && old.phase == new.phase
                && old.base_case_checked == new.base_case_checked);
        Some(result)
    }

    fn check_invariant(&self, state: &Self::State) -> Option<bool> {
        Some(self.check_type_invariant(state))
    }
}

impl KindCodegen {
    fn check_type_invariant(&self, state: &KindCodegenState) -> bool {
        range_set(0_i64, 4_i64).contains(&state.k)
            && tla_set![
                "Running".to_string(),
                "Safe".to_string(),
                "Unsafe".to_string(),
                "Unknown".to_string(),
                "NotApplicable".to_string()
            ]
            .contains(&state.result)
            && tla_set![
                "idle".to_string(),
                "base".to_string(),
                "forward".to_string(),
                "backward".to_string()
            ]
            .contains(&state.phase)
            && boolean_set().contains(&state.base_case_checked)
    }

    /// UnsafeFromBase: result = "Unsafe" => phase = "base"
    fn check_unsafe_from_base(&self, state: &KindCodegenState) -> bool {
        state.result != "Unsafe" || state.phase == "base"
    }

    /// SafeNotFromBase: result = "Safe" => phase != "base"
    fn check_safe_not_from_base(&self, state: &KindCodegenState) -> bool {
        state.result != "Safe" || state.phase != "base"
    }

    /// SafeFromInductionRequiresBaseCheck:
    ///   (result = "Safe" /\ phase in {"forward","backward"}) => baseCaseChecked
    fn check_safe_from_induction_requires_base_check(&self, state: &KindCodegenState) -> bool {
        !(state.result == "Safe" && ["forward", "backward"].contains(&state.phase.as_str()))
            || state.base_case_checked
    }
}

// ---------------------------------------------------------------------------
// Tests: exhaustive state-space exploration + invariant verification
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_init_satisfies_all_invariants() {
        let machine = KindCodegen;
        for state in &machine.init() {
            assert!(
                machine.check_type_invariant(state),
                "TypeInvariant violated in init: {:?}",
                state
            );
            assert!(
                machine.check_unsafe_from_base(state),
                "UnsafeFromBase violated in init: {:?}",
                state
            );
            assert!(
                machine.check_safe_not_from_base(state),
                "SafeNotFromBase violated in init: {:?}",
                state
            );
            assert!(
                machine.check_safe_from_induction_requires_base_check(state),
                "SafeFromInductionRequiresBaseCheck violated in init: {:?}",
                state
            );
        }
    }

    /// Exhaustive BFS exploration of the state space.
    ///
    /// This is the Rust equivalent of TLC model checking: starting from Init,
    /// explore all reachable states via Next, checking all invariants at each
    /// state.
    #[test]
    fn test_exhaustive_exploration() {
        let machine = KindCodegen;
        let mut seen: HashSet<KindCodegenState> = HashSet::new();
        let mut frontier: Vec<KindCodegenState> = machine.init();
        let mut transitions_checked: u64 = 0;

        while let Some(state) = frontier.pop() {
            if !seen.insert(state.clone()) {
                continue;
            }

            // Check all invariants
            assert!(
                machine.check_type_invariant(&state),
                "TypeInvariant violated: {:?}",
                state
            );
            assert!(
                machine.check_unsafe_from_base(&state),
                "UnsafeFromBase violated: {:?}",
                state
            );
            assert!(
                machine.check_safe_not_from_base(&state),
                "SafeNotFromBase violated: {:?}",
                state
            );
            assert!(
                machine.check_safe_from_induction_requires_base_check(&state),
                "SafeFromInductionRequiresBaseCheck violated: {:?}",
                state
            );

            // Generate and enqueue successors
            let next_states = machine.next(&state);
            transitions_checked += next_states.len() as u64;
            frontier.extend(next_states);
        }

        // With MaxK=4, the state space is small and finite.
        // Verify we explored a non-trivial number of states.
        assert!(
            seen.len() > 10,
            "Expected >10 reachable states, got {}",
            seen.len()
        );
        assert!(transitions_checked > 0, "No transitions checked");
        eprintln!(
            "Exhaustive exploration: {} states, {} transitions",
            seen.len(),
            transitions_checked
        );
    }

    /// Verify is_next is consistent with next(): every state produced by
    /// next(old) should satisfy is_next(old, new) == Some(true).
    #[test]
    fn test_is_next_consistent_with_next() {
        let machine = KindCodegen;
        let mut seen: HashSet<KindCodegenState> = HashSet::new();
        let mut frontier: Vec<KindCodegenState> = machine.init();
        let mut checked = 0_u64;

        while let Some(state) = frontier.pop() {
            if !seen.insert(state.clone()) {
                continue;
            }

            let next_states = machine.next(&state);
            for ns in &next_states {
                let result = machine.is_next(&state, ns);
                assert_eq!(
                    result,
                    Some(true),
                    "is_next({:?}, {:?}) returned {:?}, expected Some(true)",
                    state,
                    ns,
                    result
                );
                checked += 1;
            }
            frontier.extend(next_states);
        }

        assert!(checked > 0, "No transitions checked");
        eprintln!("is_next consistency: {} transitions verified", checked);
    }

    /// Verify is_next rejects invalid transitions.
    #[test]
    fn test_is_next_rejects_invalid_transitions() {
        let machine = KindCodegen;

        let init = &machine.init()[0]; // k=0, Running, idle, false

        // A transition that sets result to Safe while k increments is invalid.
        let invalid = KindCodegenState {
            k: 1,
            result: "Safe".to_string(),
            phase: "idle".to_string(),
            base_case_checked: false,
        };
        let result = machine.is_next(init, &invalid);
        assert_eq!(
            result,
            Some(false),
            "is_next should reject invalid transition from init to {:?}",
            invalid
        );

        // A transition that goes to Unsafe from idle phase is invalid.
        let invalid2 = KindCodegenState {
            k: 0,
            result: "Unsafe".to_string(),
            phase: "idle".to_string(),
            base_case_checked: false,
        };
        let result2 = machine.is_next(init, &invalid2);
        assert_eq!(
            result2,
            Some(false),
            "is_next should reject Unsafe from idle phase: {:?}",
            invalid2
        );
    }

    /// K-induction style verification: check the invariant holds for
    /// k steps of induction.
    ///
    /// Base case: Init states satisfy the invariant.
    /// Inductive step: For all states reachable in 0..MAX_K steps,
    ///   if the invariant holds, then all successors also satisfy it.
    #[test]
    fn test_k_induction_invariant_preservation() {
        let machine = KindCodegen;
        let max_steps = 10;

        // Base case
        let mut current_layer: Vec<KindCodegenState> = machine.init();
        for state in &current_layer {
            assert!(
                machine.check_invariant(state) == Some(true),
                "Invariant violated in initial state: {:?}",
                state
            );
        }

        // Inductive steps
        let mut seen: HashSet<KindCodegenState> = current_layer.iter().cloned().collect();
        for step in 0..max_steps {
            let mut next_layer = Vec::new();
            for state in &current_layer {
                for ns in machine.next(state) {
                    assert!(
                        machine.check_invariant(&ns) == Some(true),
                        "Invariant violated at step {} in state: {:?} (from {:?})",
                        step + 1,
                        ns,
                        state
                    );
                    if seen.insert(ns.clone()) {
                        next_layer.push(ns);
                    }
                }
            }
            if next_layer.is_empty() {
                eprintln!(
                    "State space fully explored after {} induction steps ({} states)",
                    step + 1,
                    seen.len()
                );
                return;
            }
            current_layer = next_layer;
        }
        eprintln!(
            "K-induction: {} steps, {} states explored",
            max_steps,
            seen.len()
        );
    }

    /// Terminal states: once result != "Running", no further transitions
    /// should change the result (it becomes a fixpoint on result).
    #[test]
    fn test_terminal_states_are_stable() {
        let machine = KindCodegen;
        let mut seen: HashSet<KindCodegenState> = HashSet::new();
        let mut frontier: Vec<KindCodegenState> = machine.init();

        while let Some(state) = frontier.pop() {
            if !seen.insert(state.clone()) {
                continue;
            }

            let next_states = machine.next(&state);

            // If result is terminal, next should produce no successors
            // (since all guards require result == "Running")
            if state.result != "Running" {
                assert!(
                    next_states.is_empty(),
                    "Terminal state {:?} has {} successors",
                    state,
                    next_states.len()
                );
            }

            frontier.extend(next_states);
        }
    }
}
