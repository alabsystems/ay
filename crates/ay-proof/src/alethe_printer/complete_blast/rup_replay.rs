// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AY's own replay of a printed `drup` step (`selfcheck.rs`).
//!
//! The consumer checks `(step n C :rule drup :premises (P1 .. Pk) :args (C))`
//! by reverse unit propagation: `C`'s literals are assumed false, and unit
//! propagation over the premises — literals read by parity, as every other
//! term — must reach a conflicting premise. This replays exactly that over
//! the premises' PRINTED clauses, so a `drup` step the consumer would refuse
//! is refused here first, and its document never printed.
//!
//! Literals are the self-check's parity literals: `id * 2 | negated`, whose
//! complement is `literal ^ 1`.

use ay_core::kani_compat::DetHashMap;

/// Whether `claimed` follows from `premises` by reverse unit propagation.
///
/// A tautological `claimed` is refused rather than accepted as trivially
/// true: the transport never prints one, so meeting one means the document
/// is not what AY built.
pub(super) fn rup_replays(premises: &[&[u32]], claimed: &[u32]) -> bool {
    // Each variable's value, keyed by `literal >> 1`.
    let mut value: DetHashMap<u32, bool> = DetHashMap::default();
    let holds = |value: &DetHashMap<u32, bool>, literal: u32| {
        value
            .get(&(literal >> 1))
            .map(|&assigned| assigned == (literal & 1 == 0))
    };
    for &literal in claimed {
        // Assume the literal false.
        if holds(&value, literal) == Some(true) {
            return false;
        }
        value.insert(literal >> 1, literal & 1 == 1);
    }
    // The transport lists a chain's premises from the conflicting clause
    // back, so they propagate last to first; every pass that propagates
    // nothing ends the replay.
    loop {
        let mut propagated = false;
        for premise in premises.iter().rev() {
            let mut open = None;
            let mut open_count = 0_usize;
            let mut satisfied = false;
            for &literal in *premise {
                match holds(&value, literal) {
                    Some(true) => {
                        satisfied = true;
                        break;
                    }
                    Some(false) => {}
                    None => {
                        if open != Some(literal) {
                            open_count += 1;
                        }
                        open = Some(literal);
                    }
                }
            }
            if satisfied {
                continue;
            }
            match (open, open_count) {
                (None, _) => return true,
                (Some(unit), 1) => {
                    value.insert(unit >> 1, unit & 1 == 0);
                    propagated = true;
                }
                _ => {}
            }
        }
        if !propagated {
            return false;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::rup_replays;

    const fn pos(id: u32) -> u32 {
        id * 2
    }
    const fn neg(id: u32) -> u32 {
        id * 2 + 1
    }

    #[test]
    fn a_resolution_chain_replays_and_a_stronger_claim_does_not() {
        // (a b c), (not a), (not b c)  ⊢  (c)  but not  ()  or  (b).
        let first = [pos(0), pos(1), pos(2)];
        let second = [neg(0)];
        let third = [neg(1), pos(2)];
        let premises: [&[u32]; 3] = [&first, &second, &third];
        assert!(rup_replays(&premises, &[pos(2)]));
        assert!(rup_replays(&premises, &[pos(2), pos(3)]));
        assert!(!rup_replays(&premises, &[]));
        assert!(!rup_replays(&premises, &[pos(1)]));
        // A premise order that needs a second pass still replays.
        let reversed: [&[u32]; 3] = [&third, &second, &first];
        assert!(rup_replays(&reversed, &[pos(2)]));
        // A tautological claim is refused.
        assert!(!rup_replays(&premises, &[pos(3), neg(3)]));
    }
}
