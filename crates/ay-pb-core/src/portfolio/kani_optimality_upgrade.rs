//! VerifierConsumer / Kani proof harness for the post-solve optimality-upgrade gate
//! (model-checked by model-checker-consumer; see proofs/2026-06-16-pb-trust-soundness-harnesses.md).
//! Proves the DQ-critical property that the gate (which sets OptimumFound when a
//! feasible incumbent's value <= a sound lower bound) NEVER declares a suboptimal
//! incumbent optimal. Two harnesses: one driving the REAL structural floor, one
//! over a fully-symbolic sound bound F (capturing what the gate needs from ANY
//! bound source — structural, exact-LP, safe-LP, or branch-and-bound).
//! `#[cfg(kani)]` gates it out of normal builds.
//!
//! # BMC second-engine bring-up status (W6, 2026-06-27)
//!
//! The outer/inner `Iterator::all` (`verify_all_constraints` and `eval_term`) is
//! now SOUNDLY bounded-unrolled to a CONCRETE range by model-checker-consumer (branch
//! `ay-verify/wf6-bmc`): the `slice.iter().all(..)` iterator resolves to its
//! constructor and `fld_pos=0` / `fld_len=1` fold to literals. This closed the 3
//! `iter_all_unmodeled: non-concrete iterator range` fallbacks that previously
//! demoted `gate_lemma_any_sound_bound`. The model-checker-consumer fixes: (1) peel an SSA
//! first-definition `ite(pc, ctor, __ssa_init)` to its then-branch; (2) fold
//! `selector-over-constructor` positionally (the pinned `ay-bindings` rev's
//! `field_select` never folds); (3) recover the `vec![..]` length through the
//! `Box<[T;N]> -> Box<[T]>` unsize (`std::boxed::Box` name match).
//!
//! NOT YET A REAL PROOF — DO NOT TRUST A GREEN HERE WITHOUT THE GAP BELOW CLOSED.
//! `eval_objective` / `eval_terms` use `.filter().map().sum()` and
//! `.filter().try_fold()`. model-checker-consumer cannot recover the per-element fold closure at
//! the `sum`/`fold` call site (it is captured into the opaque `Filter`/`Map`
//! adapter value), so the accumulator is HAVOCED — and for `try_fold` the havoc is
//! a symbolic multi-variant `Result` enum whose variant-0 defaulting made the
//! consuming path VACUOUSLY infeasible (a spurious "VERIFICATION SUCCESSFUL" with
//! `assert!(false)` UNREACHABLE — verified by probe). model-checker-consumer `wf6-bmc` now
//! FAILS CLOSED on these havocs (records `iter_fold_unmodeled` /
//! `iter_sum_unmodeled`), so the verdict honestly DEMOTES instead of vacuously
//! passing. Closing this to a genuine green requires modelling the
//! filter+map+sum / filter+try_fold chains by bounded element-wise unroll with
//! the closures threaded through the adapter values (architectural work in
//! model-checker-consumer's `Filter`/`Map` iterator encoding).
//!
//! # W3 / wf7 progress (2026-06-27) — closure threading LANDED; slice range is the wall
//!
//! model-checker-consumer `ay-verify/wf7-bmc` now THREADS the `Filter`/`Map` closures through a
//! side-channel (`adapter_closures` keyed by adapter base SSA name) and replays
//! them element-wise at the terminal `sum`/`fold`/`try_fold`
//! (`resolve_adapter_elements` + `try_iter_sum_unroll` / `try_iter_fold_unroll`),
//! mirroring `codegen_iter_all_any`. The recovery is VERIFIED correct: for the 9
//! `eval_terms_checked`/`eval_terms_saturating` try_fold/fold sites the chain
//! resolves with `n_stages == wrapper_depth` (== 1, the `Filter`), the
//! rust-call–tupled `call_once` closure form (`[env, (acc, item)]`) is handled,
//! and a `Result<i128,E>` `?`-short-circuit accumulator is modelled.
//!
//! It is STILL not green: every site now fail-closes at
//! `resolve_adapter_elements: bail non-concrete range` because the backing slice
//! of `eval_terms_checked(terms: &[PbTerm], ..)` is a SYMBOLIC pointee
//! (`fld_vec = Var(eval_terms_checked::arg_pointee_1_0)`, `fld_pos = 0`). The
//! concrete `objective.terms` `vec![..]` is NOT threaded through the multi-level
//! inline chain (`eval_objective` -> `eval_objective_checked` ->
//! `eval_objective_exact` -> `eval_terms_checked`), so `resolve_iter_concrete_range`
//! cannot fold a concrete `[0,len)` range and the bounded unroll fail-closes.
//! This is the SAME concrete-slice mechanism wf5/wf6 landed for the 1-level
//! `verify_all_constraints` `all` (which IS concrete here), not yet reaching the
//! deeper objective-eval chain through a field-projected (`&objective.terms`)
//! reborrowed slice arg.
//!
//! SMALLEST NEXT FIX: extend the wf5/wf6 "thread Vec->slice concrete length" so a
//! field-projected slice argument (`&objective.terms`) keeps its concrete backing
//! Vec across nested mini-inlines; then the (already-working) closure-threaded
//! `try_fold`/`fold` unroll completes and `gate_lemma_any_sound_bound` becomes the
//! FIRST BMC green on a real AY soundness fn (2nd independent OPTIMUM engine).

use super::*;
use crate::cdcl::objective_lower_bound_from_constraints;
use crate::types::{PbConstraint, PbLit, PbObjective, PbRel, PbTerm};

fn pos(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

/// Drives the REAL structural lower-bound function: for all small bounded
/// 2-var instances, the floor never overshoots and the gate condition
/// `value <= floor` implies the incumbent is optimal.
#[kani::proof]
fn gate_soundness_structural_floor() {
    let c1: i128 = kani::any();
    let c2: i128 = kani::any();
    kani::assume((1..=3).contains(&c1));
    kani::assume((1..=3).contains(&c2));
    let a1: i128 = kani::any();
    let a2: i128 = kani::any();
    let rhs: i128 = kani::any();
    kani::assume((1..=3).contains(&a1));
    kani::assume((1..=3).contains(&a2));
    kani::assume((1..=3).contains(&rhs));

    let obj = PbObjective {
        terms: vec![
            PbTerm {
                coeff: c1,
                lits: vec![pos(1)],
            },
            PbTerm {
                coeff: c2,
                lits: vec![pos(2)],
            },
        ],
    };
    let cs = vec![PbConstraint {
        terms: vec![
            PbTerm {
                coeff: a1,
                lits: vec![pos(1)],
            },
            PbTerm {
                coeff: a2,
                lits: vec![pos(2)],
            },
        ],
        rel: PbRel::Ge,
        rhs,
    }];

    let mut opt: Option<i128> = None;
    let mut mask = 0u8;
    while mask < 4 {
        let x = [mask & 1 == 1, mask & 2 == 2];
        if verify_all_constraints(&cs, &x) {
            let v = eval_objective(&obj, &x);
            opt = Some(match opt {
                Some(o) => {
                    if v < o {
                        v
                    } else {
                        o
                    }
                }
                None => v,
            });
        }
        mask += 1;
    }

    if let Some(f) = objective_lower_bound_from_constraints(&cs, &obj, &|| false) {
        if let Some(o) = opt {
            assert!(f <= o); // bound never overshoots
        }
        let mut m = 0u8;
        while m < 4 {
            let a = [m & 1 == 1, m & 2 == 2];
            if verify_all_constraints(&cs, &a) {
                let value = eval_objective(&obj, &a);
                if value <= f {
                    assert_eq!(value, opt.unwrap()); // gate fires => optimal
                }
            }
            m += 1;
        }
    }
}

/// Pure gate lemma with a FULLY-SYMBOLIC sound bound F (assumed valid: F <=
/// objective over all feasible points). Captures what the gate needs from ANY
/// bound source: a feasible incumbent V with V <= F must equal the optimum.
#[kani::proof]
fn gate_lemma_any_sound_bound() {
    let c1: i128 = kani::any();
    let c2: i128 = kani::any();
    kani::assume((1..=3).contains(&c1));
    kani::assume((1..=3).contains(&c2));
    let a1: i128 = kani::any();
    let a2: i128 = kani::any();
    let rhs: i128 = kani::any();
    kani::assume((1..=3).contains(&a1));
    kani::assume((1..=3).contains(&a2));
    kani::assume((1..=3).contains(&rhs));

    let obj = PbObjective {
        terms: vec![
            PbTerm {
                coeff: c1,
                lits: vec![pos(1)],
            },
            PbTerm {
                coeff: c2,
                lits: vec![pos(2)],
            },
        ],
    };
    let cs = vec![PbConstraint {
        terms: vec![
            PbTerm {
                coeff: a1,
                lits: vec![pos(1)],
            },
            PbTerm {
                coeff: a2,
                lits: vec![pos(2)],
            },
        ],
        rel: PbRel::Ge,
        rhs,
    }];

    let mut opt: Option<i128> = None;
    let mut mask = 0u8;
    while mask < 4 {
        let x = [mask & 1 == 1, mask & 2 == 2];
        if verify_all_constraints(&cs, &x) {
            let v = eval_objective(&obj, &x);
            opt = Some(match opt {
                Some(o) => {
                    if v < o {
                        v
                    } else {
                        o
                    }
                }
                None => v,
            });
        }
        mask += 1;
    }

    // Fully-symbolic candidate bound, ASSUMED valid (F <= obj over feasible).
    let f: i128 = kani::any();
    kani::assume((-10..=10).contains(&f));
    let mut mx = 0u8;
    while mx < 4 {
        let x = [mx & 1 == 1, mx & 2 == 2];
        if verify_all_constraints(&cs, &x) {
            kani::assume(f <= eval_objective(&obj, &x));
        }
        mx += 1;
    }

    // Symbolic feasible incumbent.
    let sel: u8 = kani::any();
    kani::assume(sel < 4);
    let a = [sel & 1 == 1, sel & 2 == 2];
    kani::assume(verify_all_constraints(&cs, &a));
    let value = eval_objective(&obj, &a);

    if value <= f {
        assert_eq!(value, opt.unwrap()); // gate fires => declared optimum is true
    }
}
