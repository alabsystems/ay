// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fingerprinting of one direct ground-pin replay plan.

use super::*;

fn fingerprint_mix(state: &mut u64, value: u64) {
    *state ^= value;
    *state = state.wrapping_mul(0x100_0000_01b3);
}

impl Executor {
    /// Fingerprint the exact ordered direct-replay plan. A collision can only
    /// skip a completeness attempt; every accepted proof is still strict.
    pub(super) fn ground_pin_input_fingerprint(
        plans: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
        instances: &[TermId],
    ) -> u64 {
        let mut state = 0xcbf2_9ce4_8422_2325;
        fingerprint_mix(&mut state, instances.len() as u64);
        for instance in instances {
            fingerprint_mix(&mut state, u64::from(instance.0));
            match plans.get(instance) {
                Some(ConsequencePlan::ForallInstance {
                    quantifier,
                    binding,
                }) => {
                    fingerprint_mix(&mut state, 1);
                    fingerprint_mix(&mut state, u64::from(quantifier.0));
                    fingerprint_mix(&mut state, binding.len() as u64);
                    for value in binding {
                        fingerprint_mix(&mut state, u64::from(value.0));
                    }
                    // A recorded forall instance may be authorized through a
                    // negated-existential dual plan stored under its source
                    // quantifier. Include that transitive authority edge so a
                    // newly admitted dual plan receives its own bounded scan.
                    match plans.get(quantifier) {
                        Some(ConsequencePlan::NegatedExistsDual {
                            not_exists_root,
                            exists,
                            ..
                        }) => {
                            fingerprint_mix(&mut state, 5);
                            fingerprint_mix(&mut state, u64::from(not_exists_root.0));
                            fingerprint_mix(&mut state, u64::from(exists.0));
                        }
                        Some(_) => fingerprint_mix(&mut state, 6),
                        None => fingerprint_mix(&mut state, 7),
                    }
                }
                Some(ConsequencePlan::SkolemInstance {
                    source,
                    quantified,
                    witness,
                    instance,
                    positive,
                }) => {
                    fingerprint_mix(&mut state, 2 + u64::from(*positive));
                    for term in [source, quantified, witness, instance] {
                        fingerprint_mix(&mut state, u64::from(term.0));
                    }
                }
                Some(ConsequencePlan::NegatedExistsDual {
                    not_exists_root,
                    exists,
                    ..
                }) => {
                    fingerprint_mix(&mut state, 4);
                    fingerprint_mix(&mut state, u64::from(not_exists_root.0));
                    fingerprint_mix(&mut state, u64::from(exists.0));
                }
                Some(ConsequencePlan::ImpliedConsequent {
                    implication,
                    antecedent,
                }) => {
                    fingerprint_mix(&mut state, 8);
                    fingerprint_mix(&mut state, u64::from(implication.0));
                    fingerprint_mix(&mut state, u64::from(antecedent.0));
                }
                Some(ConsequencePlan::ClausalInstance { source, literals }) => {
                    fingerprint_mix(&mut state, 9);
                    fingerprint_mix(&mut state, u64::from(source.0));
                    fingerprint_mix(&mut state, literals.len() as u64);
                }
                Some(ConsequencePlan::QuantifierJoin {
                    source,
                    joined,
                    nested,
                    positive,
                }) => {
                    fingerprint_mix(&mut state, 10 + u64::from(*positive));
                    for term in [source, joined, nested] {
                        fingerprint_mix(&mut state, u64::from(term.0));
                    }
                }
                Some(ConsequencePlan::CongruenceEquality { equality }) => {
                    fingerprint_mix(&mut state, 12);
                    fingerprint_mix(&mut state, u64::from(equality.0));
                }
                None => fingerprint_mix(&mut state, 0),
            }
        }
        state
    }
}
