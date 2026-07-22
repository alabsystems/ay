// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exhaustive cargo-test tie pinning the REAL shipped `lemma_admitted_inductive`
//! to the bounded no-false-accept property that `offline deductive checker check` discharges
//! over the same source in the development proof harness.
//!
//! The Trust harness inlines the core's body byte-identically so the obligation
//! grounds for the finite-route SMT verifier (a function call would route to the
//! slow PDR engine). THIS test closes the loop on the SHIPPED bytes: it calls the
//! real `lemma_admitted_inductive` over EVERY 3-state transition system and
//! asserts the same accept-implies-safe property. Corrupting the core (dropping a
//! conjunct so a non-inductive candidate is admitted) makes a Bad-reaching system
//! a counterexample and this test fails — exactly as the Trust harness fails.

use super::inductive_accept_core::lemma_admitted_inductive;

const N: usize = 3;

/// The shipped admit decision never false-accepts: if `lemma_admitted_inductive`
/// admits a candidate (consecution & init-validity & safety, in the shipped
/// argument order), the Bad state is genuinely unreachable — over ALL 2^18
/// three-state transition systems (free Init, Bad, candidate Inv, and T).
#[test]
fn admit_decision_never_false_accepts_over_all_3state_systems() {
    let bit = |bits: u32, i: u32| (bits >> i) & 1 == 1;
    for bits in 0u32..(1 << 18) {
        let mut init = [false; N];
        let mut bad = [false; N];
        let mut inv = [false; N];
        let mut t = [[false; N]; N];
        let mut b = 0u32;
        for slot in &mut init {
            *slot = bit(bits, b);
            b += 1;
        }
        for slot in &mut bad {
            *slot = bit(bits, b);
            b += 1;
        }
        for slot in &mut inv {
            *slot = bit(bits, b);
            b += 1;
        }
        for row in &mut t {
            for cell in row.iter_mut() {
                *cell = bit(bits, b);
                b += 1;
            }
        }

        // The validator's three per-obligation checks (independent re-derivation).
        let mut init_ok = true;
        for s in 0..N {
            init_ok &= !init[s] || inv[s];
        }
        let mut cons_ok = true;
        for j in 0..N {
            for k in 0..N {
                cons_ok &= !(inv[j] && t[j][k]) || inv[k];
            }
        }
        let mut safe_ok = true;
        for s in 0..N {
            safe_ok &= !inv[s] || !bad[s];
        }

        // THE REAL SHIPPED CORE decision; shipped arg order (self_ind, init_valid,
        // entry_ind), mapped here to (cons_ok, init_ok, safe_ok).
        let accept = lemma_admitted_inductive(cons_ok, init_ok, safe_ok);

        // INDEPENDENT reachability fixpoint (exact at depth N for N states).
        let mut reach = init;
        for _ in 0..N {
            let mut next = reach;
            for j in 0..N {
                if reach[j] {
                    for k in 0..N {
                        if t[j][k] {
                            next[k] = true;
                        }
                    }
                }
            }
            reach = next;
        }
        let mut bad_reachable = false;
        for s in 0..N {
            bad_reachable |= reach[s] && bad[s];
        }

        assert!(
            !accept || !bad_reachable,
            "false-accept: non-inductive candidate admitted yet Bad is reachable (bits={bits})"
        );
    }
}

/// The core is exactly the three-way conjunction (structural contract).
#[test]
fn admit_is_exactly_the_three_way_and() {
    for m in 0u8..8 {
        let a = m & 1 != 0;
        let b = m & 2 != 0;
        let c = m & 4 != 0;
        assert_eq!(lemma_admitted_inductive(a, b, c), a && b && c);
    }
}
