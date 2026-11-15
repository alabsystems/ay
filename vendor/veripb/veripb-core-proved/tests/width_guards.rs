//! Regression tests for the width-guard discipline of the proved core.
//!
//! These pin the class of defect that VeriPB bug C is an instance of: an `i64`
//! degree computation that wraps and turns a satisfiable formula into
//! `s VERIFIED UNSATISFIABLE`. The release profile now aborts on such a wrap
//! rather than letting it through, but that is a backstop: the guards below
//! are what let the rule produce the RIGHT answer instead of no answer.
//!
//! In `veripb-core-proved` every degree crosses into the machine width through
//! a guard that recomputes the value in `i128`. A wrapped value cannot pass.
//! Each test below is the executable image of a Clean hypothesis:
//!
//! | test | Clean obligation |
//! |---|---|
//! | `add_degree_overflow_is_refused`     | `entails_add_checked` (`fitsI64 s`) |
//! | `weaken_degree_underflow_is_refused` | `entails_weaken_checked` (`fitsI64 r`; the `eqOkB (r+w) d` witness is additionally re-checked in-code) |
//! | `multiply_coeff_overflow_is_refused` | `entails_multiply` at machine width |
//! | `negate_degree_overflow_is_refused`  | `entails_of_negation_unsat` (`nd + d = coeffSum + 1`) |
//! | `divide_output_satisfies_both_side_conditions_it_is_proved_under` | `CoeffsDominated` / `k * f d < d + k` |
//!
//! ## The two coefficient domains
//!
//! Every test above is about the **narrow** domain, where the guards have
//! content. The kernel is also instantiated at [`Big`] — unbounded `Int`, the
//! width the Clean theorems are actually stated over — where
//! `CoeffDomain::narrow` is total and the guards are vacuous. The tests at the
//! end of this file pin the two facts that relationship must have:
//!
//! | test | claim |
//! |---|---|
//! | `every_rule_that_refuses_on_width_fires_at_the_complete_domain` | a narrow refusal is a *width* refusal, and one domain up the same rule fires |
//! | `the_two_domains_agree_wherever_the_narrow_one_accepts` | where both compute, they compute the same constraint — randomized over every rule the bridge dispatches at both tiers: ADD, MULTIPLY, DIVIDE, SATURATE, WEAKEN, NEGATE, NORMALIZE and the two MIR forms |
//! | `the_complete_domain_computes_the_value_a_wrap_would_have_destroyed` | and the value it computes is not the wrapped one |

use std::collections::BTreeMap;
use veripb_core_proved::mir::{mir, mir_variable};
use veripb_core_proved::normalize::normalize;
use veripb_core_proved::{
    Big, Coeff, Constraint, GuardError, Lit, Term, Wide, add, divide, divide_with, guard,
    literal_axiom, multiply, negate, saturate, weaken_degree,
};

fn c(terms: Vec<Term>, degree: Coeff) -> Constraint {
    Constraint::new(terms, degree)
}

/// One rule applied in both domains: the narrow `i64` result and the
/// complete `Big` result, which must agree whenever the narrow one
/// produced anything at all.
type DomainPair = (
    Result<Constraint, GuardError>,
    Result<Constraint<Big>, GuardError>,
);

#[test]
fn add_degree_overflow_is_refused() {
    let a = c(
        vec![Term {
            coeff: 1,
            lit: Lit::pos(0),
        }],
        Coeff::MAX,
    );
    let b = c(
        vec![Term {
            coeff: 1,
            lit: Lit::pos(1),
        }],
        1,
    );
    // Unchecked i64 addition here would wrap to i64::MIN, which is <= every
    // possible left-hand side, i.e. a trivially true constraint derived from
    // two non-trivial ones. The guard refuses instead.
    assert_eq!(add(&a, &b), Err(GuardError::DegreeOverflow));
    assert_eq!(
        Coeff::MAX.wrapping_add(1),
        Coeff::MIN,
        "the wrap this guard prevents"
    );
}

#[test]
fn weaken_degree_underflow_is_refused() {
    // This is bug C verbatim: degree i64::MIN, decremented by 1.
    let a = c(
        vec![Term {
            coeff: 1,
            lit: Lit::pos(0),
        }],
        Coeff::MIN,
    );
    assert_eq!(weaken_degree(&a, 1), Err(GuardError::DegreeOverflow));
    // Unguarded, the decrement wraps to i64::MAX: a constraint no assignment
    // can satisfy, i.e. an immediate (bogus) refutation.
    assert_eq!(
        Coeff::MIN.wrapping_sub(1),
        Coeff::MAX,
        "the wrap this guard prevents"
    );
}

#[test]
fn weaken_degree_in_range_is_allowed_and_exact() {
    let a = c(
        vec![Term {
            coeff: 1,
            lit: Lit::pos(0),
        }],
        5,
    );
    let w = weaken_degree(&a, 3).unwrap();
    assert_eq!(w.degree, 2);
    // The Clean hypothesis `eqOkB (r + w) c.degree`.
    assert!(guard::eq_ok(
        a.degree,
        Wide::from(w.degree) + Wide::from(3 as Coeff)
    ));
}

#[test]
fn multiply_coeff_overflow_is_refused() {
    let a = c(
        vec![Term {
            coeff: Coeff::MAX,
            lit: Lit::pos(0),
        }],
        1,
    );
    assert_eq!(multiply(2, &a), Err(GuardError::CoeffOverflow));
}

#[test]
fn multiply_rejects_non_positive_factors() {
    let a = c(
        vec![Term {
            coeff: 1,
            lit: Lit::pos(0),
        }],
        1,
    );
    assert_eq!(multiply(0, &a), Err(GuardError::NonPositiveFactor));
    assert_eq!(multiply(-1, &a), Err(GuardError::NonPositiveFactor));
}

/// WEAKEN rejects a negative factor.
///
/// This test exists because an audit found it missing while every sibling
/// had one: `multiply`, `divide` and `mir` each assert their
/// `NonPositiveFactor` refusal, and `weaken_degree` -- whose factor is
/// PROOF-SUPPLIED on the live path (`Instruction::LowerRHS(amount)` reaches
/// it straight from the proof file) -- asserted only `DegreeOverflow`. The
/// only thing standing behind its sign guard was a text pin that a dead-code
/// rewrite satisfied, so the guard could be disabled with the whole suite
/// green while `weaken_degree(x >= 1, -5)` turned a SATISFIABLE constraint
/// into `x >= 6` -- WEAKEN manufacturing a contradiction, which is a wrong
/// verdict.
///
/// The kernel side is `entails_weaken_checked`, whose hypothesis is
/// `Int.le 0 w`; with a negative `w` the Clean proof does not apply at all,
/// so this refusal is what keeps the executable rule inside the theorem.
#[test]
fn weaken_degree_rejects_negative_factors() {
    let a = c(
        vec![Term {
            coeff: 1,
            lit: Lit::pos(0),
        }],
        1,
    );
    assert_eq!(weaken_degree(&a, -1), Err(GuardError::NonPositiveFactor));
    assert_eq!(weaken_degree(&a, -5), Err(GuardError::NonPositiveFactor));
    // ...and still ACCEPTS the non-negative factors the rule is for, so the
    // test cannot be satisfied by a guard that refuses everything.
    assert!(weaken_degree(&a, 0).is_ok());
    assert!(weaken_degree(&a, 3).is_ok());
}

#[test]
fn negate_degree_overflow_is_refused() {
    // coeffSum - degree + 1 overflows when the degree is very negative.
    let a = c(
        vec![Term {
            coeff: Coeff::MAX,
            lit: Lit::pos(0),
        }],
        Coeff::MIN,
    );
    assert_eq!(negate(&a), Err(GuardError::DegreeOverflow));
}

#[test]
fn divide_rejects_non_positive_divisors() {
    let a = c(
        vec![Term {
            coeff: 4,
            lit: Lit::pos(0),
        }],
        2,
    );
    assert_eq!(divide(0, &a), Err(GuardError::NonPositiveFactor));
    assert_eq!(divide(-2, &a), Err(GuardError::NonPositiveFactor));
}

#[test]
fn divide_by_an_oversized_divisor_still_rounds_up() {
    // Bug D's shape: divisor larger than every coefficient. The correct answer
    // is 1 for each positive coefficient and 1 for the degree, and `divide`
    // must PROVE that via its own guards rather than hard-coding it.
    let a = c(
        vec![Term {
            coeff: 3,
            lit: Lit::pos(0),
        }],
        2,
    );
    let d = divide(1000, &a).unwrap();
    assert_eq!(d.terms[0].coeff, 1);
    assert_eq!(d.degree, 1);
    // Non-trivially-true: 1*x >= 1 is falsified by x = false.
    assert!(!d.holds(&|_| false));
}

#[test]
fn divide_of_a_trivially_true_constraint_stays_trivially_true() {
    // Bug D produced a contradiction from a trivially true constraint. Here
    // the degree is <= 0, so ceil(d/k) <= 0 and the result stays trivially true.
    let a = c(
        vec![Term {
            coeff: 3,
            lit: Lit::pos(0),
        }],
        0,
    );
    let d = divide(1000, &a).unwrap();
    assert_eq!(d.degree, 0);
    assert!(d.holds(&|_| false));
}

#[test]
fn divide_output_satisfies_both_side_conditions_it_is_proved_under() {
    // The `QuotientNotCeiling` branches inside `divide` are unreachable by any
    // *input* while `ceil_div` is correct -- they re-check `ceil_div`'s own
    // output. What they defend against is a WRONG `ceil_div`, which is why
    // `divide_with` exists and why the three tests below drive those branches
    // through a deliberately wrong quotient map rather than through a hostile
    // constraint. This test states the positive half: the side conditions the
    // proof needs hold on the map the checker actually runs, over the signs
    // and boundaries bug D got wrong:
    //   intCeilDiv_ub  : c_i <= k * ceil(c_i / k)
    //   intCeilDiv_min : k * ceil(c_i / k) < c_i + k     (least such quotient)
    for k in [1 as Coeff, 2, 3, 7, 1000] {
        for degree in [-7 as Coeff, -1, 0, 1, 2, 6, 7, 8, 999, 1000, 1001] {
            for coeff in [-5 as Coeff, -1, 0, 1, 3, 6, 7, 20] {
                let before = c(
                    vec![Term {
                        coeff,
                        lit: Lit::pos(0),
                    }],
                    degree,
                );
                let after =
                    divide(k, &before).expect("divide must accept a well-formed constraint");

                let kw = Wide::from(k);
                let qc = Wide::from(after.terms[0].coeff);
                let qd = Wide::from(after.degree);
                assert!(
                    kw * qc >= Wide::from(coeff),
                    "ub at the coeff: k={k} c={coeff}"
                );
                assert!(
                    kw * qc < Wide::from(coeff) + kw,
                    "min at the coeff: k={k} c={coeff}"
                );
                assert!(
                    kw * qd >= Wide::from(degree),
                    "ub at the degree: k={k} d={degree}"
                );
                assert!(
                    kw * qd < Wide::from(degree) + kw,
                    "min at the degree: k={k} d={degree}"
                );
            }
        }
    }
}

/// A quotient map that OVERSHOOTS by one is refused at the first coefficient.
///
/// This is the branch that was invisible before the minimality bound was
/// applied per coefficient: `ceil(c/k) + 1` still satisfies `c <= k*q`, so the
/// old guard accepted it and the output was not `divC (intCeilDiv . k) c` at
/// all. `VeriPbCore.ceilQuotient_unique` is the statement this test protects.
#[test]
fn divide_with_refuses_an_overshooting_quotient_map() {
    let a = c(
        vec![Term {
            coeff: 7,
            lit: Lit::pos(0),
        }],
        7,
    );
    assert_eq!(
        divide_with(
            2,
            |x: &Wide, k: &Wide| x.div_euclid(*k) + if x.rem_euclid(*k) == 0 { 1 } else { 2 },
            &a
        ),
        Err(GuardError::QuotientNotCeiling)
    );
}

/// The other side: a map that UNDERSHOOTS violates `x <= k*q`.
#[test]
fn divide_with_refuses_an_undershooting_quotient_map() {
    let a = c(
        vec![Term {
            coeff: 7,
            lit: Lit::pos(0),
        }],
        7,
    );
    assert_eq!(
        divide_with(2, |x: &Wide, k: &Wide| x.div_euclid(*k), &a),
        Err(GuardError::QuotientNotCeiling)
    );
}

/// Upstream defect 4 verbatim: the oversized-divisor fallback that hard-coded
/// `ceil(A/d) = 1`. It must be refused on a value where `1` is *not* the
/// ceiling -- a non-positive one, since for `0 < A <= d` the constant `1` is
/// the correct answer and a test there would pass for the wrong reason.
#[test]
fn divide_with_refuses_the_hardcoded_quotient_of_upstream_defect_4() {
    let a = c(
        vec![Term {
            coeff: 0,
            lit: Lit::pos(0),
        }],
        0,
    );
    assert_eq!(
        divide_with(1000, |_: &Wide, _: &Wide| 1, &a),
        Err(GuardError::QuotientNotCeiling)
    );
    // ...and the correct map accepts the same constraint.
    assert!(divide(1000, &a).is_ok());
}

/// The tightened guard must be NEUTRAL on the map the checker runs: adding the
/// per-coefficient minimality bound may not reject anything `ceil_div`
/// produces, or it would change verdicts. Randomised over the full `i64`
/// range plus the boundaries.
#[test]
fn the_tightened_guard_never_rejects_the_real_quotient_map() {
    // xorshift64*, so the test is deterministic and dependency-free.
    let mut s: u64 = 0x2545_F491_4F6C_DD1D;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s as i64
    };
    for _ in 0..200_000 {
        let x = next();
        let k = next().saturating_abs().max(1);
        let a = c(
            vec![Term {
                coeff: x,
                lit: Lit::pos(0),
            }],
            x,
        );
        match divide(k, &a) {
            Ok(out) => assert_eq!(out.terms[0].coeff, out.degree),
            // `narrow` may still refuse: ceil(i64::MIN / 1) is representable,
            // but the guard layer, not the ceiling check, owns that decision.
            Err(e) => assert_ne!(e, GuardError::QuotientNotCeiling, "x={x} k={k}"),
        }
    }
    for x in [i64::MIN, i64::MIN + 1, -1, 0, 1, i64::MAX - 1, i64::MAX] {
        for k in [1_i64, 2, i64::MAX] {
            let a = c(
                vec![Term {
                    coeff: x,
                    lit: Lit::pos(0),
                }],
                x,
            );
            if let Err(e) = divide(k, &a) {
                assert_ne!(e, GuardError::QuotientNotCeiling, "boundary x={x} k={k}");
            }
        }
    }
}

#[test]
fn divide_rejects_a_non_positive_divisor() {
    // The one `divide` rejection that IS reachable from a caller.
    let a = c(
        vec![Term {
            coeff: 3,
            lit: Lit::pos(0),
        }],
        3,
    );
    assert_eq!(divide(0, &a), Err(GuardError::NonPositiveFactor));
    assert_eq!(divide(-2, &a), Err(GuardError::NonPositiveFactor));
}

#[test]
fn literal_axiom_is_a_tautology_under_every_assignment() {
    for b in [true, false] {
        let ax: Constraint = literal_axiom(Lit::pos(7));
        assert!(ax.holds(&|_| b));
    }
}

#[test]
fn contradiction_is_falsified_by_every_assignment() {
    let bot: Constraint = Constraint::contradiction();
    assert!(bot.is_contradiction());
    assert!(!bot.holds(&|_| true));
    assert!(!bot.holds(&|_| false));
}

#[test]
fn fits_i64_boundaries_match_the_clean_controls() {
    // Mirrors VeriPbCore.ctrl_fits_max / ctrl_fits_overflow / ctrl_fits_min /
    // ctrl_fits_underflow.
    assert!(guard::fits_i64(Wide::from(Coeff::MAX)));
    assert!(!guard::fits_i64(Wide::from(Coeff::MAX) + 1));
    assert!(guard::fits_i64(Wide::from(Coeff::MIN)));
    assert!(!guard::fits_i64(Wide::from(Coeff::MIN) - 1));
}

#[test]
fn eq_ok_rejects_a_wrapped_value() {
    // Mirrors VeriPbCore.ctrl_eq_guard_rejects_wrap: i64::MIN - 1 wraps to
    // i64::MAX, and the guard compares against the true (wide) value.
    let wrapped = Coeff::MIN.wrapping_sub(1);
    assert_eq!(wrapped, Coeff::MAX);
    assert!(!guard::eq_ok(wrapped, Wide::from(Coeff::MIN) - 1));
    assert!(guard::eq_ok(41, 40 + 1));
}

/// The machine `ceil_div` computes `VeriPbCore.intCeilDiv`.
///
/// These are the kernel-evaluated controls of the Clean division theory
/// (`ctrl_intCeilDiv_*`), executed here: if the machine function ever stops
/// agreeing with the proved one, `entails_divide_concrete` stops being the
/// theorem that describes what this crate runs. `divide` is the observable
/// entry point (`ceil_div` is private), so each case is driven through it on
/// a one-term constraint, where the derived coefficient *is* the quotient.
#[test]
fn ceil_div_matches_the_clean_controls() {
    // (dividend, divisor, expected ceiling) — the Clean controls verbatim.
    for (x, k, expected) in [
        (7_i64, 2_i64, 4_i64),
        (6, 2, 3),
        (-7, 2, -3),
        (-6, 2, -3),
        (0, 5, 0),
    ] {
        let out = divide(
            k,
            &c(
                vec![Term {
                    coeff: x,
                    lit: Lit::pos(0),
                }],
                x,
            ),
        )
        .unwrap();
        assert_eq!(
            out.terms[0].coeff, expected,
            "ceil({x}/{k}) must be {expected}, the value VeriPbCore.intCeilDiv computes"
        );
        assert_eq!(out.degree, expected, "the degree quotient must agree too");
    }
}

/// The two defining inequalities of `ceil`, over the sign and boundary cases
/// the proof covers: `x <= k*q` (`intCeilDiv_ub`) and `k*q < x + k`
/// (`intCeilDiv_min`). Together these pin `q` uniquely, so a quotient that
/// satisfies both IS the ceiling.
#[test]
fn divide_output_satisfies_the_proved_ceiling_bounds() {
    for k in [1_i64, 2, 3, 7, 1_000_000] {
        for x in [-1_000_001_i64, -7, -1, 0, 1, 7, 1_000_001, i64::MAX / 2] {
            let out = divide(
                k,
                &c(
                    vec![Term {
                        coeff: x,
                        lit: Lit::pos(0),
                    }],
                    x,
                ),
            )
            .unwrap();
            let q = Wide::from(out.degree);
            let (xw, kw) = (Wide::from(x), Wide::from(k));
            assert!(xw <= kw * q, "intCeilDiv_ub violated at x={x}, k={k}");
            assert!(kw * q < xw + kw, "intCeilDiv_min violated at x={x}, k={k}");
        }
    }
}

/// The MIR module reproduces the kernel-evaluated MIR controls.
///
/// Same discipline as `ceil_div_matches_the_clean_controls`: every assertion
/// below is one `rfl`-proved Clean theorem, driven through the public entry
/// points of `veripb_core_proved::mir` on a one-term constraint where that is
/// possible, so the test pins the *rule* and not just a helper. Clean names in
/// the comments; the values are transcribed from `clean/veripb_kernel.lean`.
#[test]
fn mir_matches_the_clean_controls() {
    use veripb_core_proved::mir::{floor_div, floor_mod, mir_f};

    // ctrl_ifd_7_2 / ctrl_ifm_7_2, ctrl_ifd_neg7_2 / ctrl_ifm_neg7_2,
    // ctrl_ifd_0_5 / ctrl_ifm_0_5.
    assert_eq!(floor_div::<Wide>(&7, &2), 3);
    assert_eq!(floor_mod::<Wide>(&7, &2), 1);
    assert_eq!(floor_div::<Wide>(&-7, &2), -4);
    assert_eq!(floor_mod::<Wide>(&-7, &2), 1);
    assert_eq!(floor_div::<Wide>(&0, &5), 0);
    assert_eq!(floor_mod::<Wide>(&0, &5), 0);

    // ctrl_mirF_7_2_1 / ctrl_mirF_neg7_2_1, and the monotone triple
    // ctrl_mirF_3_2_1 / _2 / _3.
    assert_eq!(mir_f::<Wide>(&2, &1, &7), Some(4));
    assert_eq!(mir_f::<Wide>(&2, &1, &-7), Some(-3));
    assert_eq!(mir_f::<Wide>(&3, &2, &1), Some(1));
    assert_eq!(mir_f::<Wide>(&3, &2, &2), Some(2));
    assert_eq!(mir_f::<Wide>(&3, &2, &3), Some(2));

    // ctrl_mirF_not_superadd / ctrl_mirF_subadd_witness: mirF is SUBadditive,
    // mirF(1) + mirF(2) = 3 > 2 = mirF(3).
    assert!(
        mir_f::<Wide>(&3, &2, &1).unwrap() + mir_f::<Wide>(&3, &2, &2).unwrap()
            > mir_f::<Wide>(&3, &2, &3).unwrap()
    );

    // ctrl_mir_5_3_r / _coeff / _deg, promoted to the rule: 5x >= 5 with
    // k = 3 gives r = 2, coefficient mirF(5) = 4 and degree (1 + 1) * 2 = 4.
    assert_eq!(floor_mod::<Wide>(&5, &3), 2);
    assert_eq!(mir_f::<Wide>(&3, &2, &5), Some(4));
    let base = c(
        vec![Term {
            coeff: 5,
            lit: Lit::pos(0),
        }],
        5,
    );
    let cut = mir(3, &base).expect("the normalized-form rule must fire here");
    assert_eq!(
        cut.terms,
        vec![Term {
            coeff: 4,
            lit: Lit::pos(0)
        }]
    );
    assert_eq!(cut.degree, 4);

    // The variable-form controls, on `ctrlVfC = 3x + 2~y >= 4`:
    // ctrl_vf_negSum (2), ctrl_vf_degree_var (A = 2), ctrl_vf_r (r = 2),
    // ctrl_vf_mirF_pos / _neg, ctrl_vf_terms and ctrl_vf_new_degree (3).
    assert_eq!(floor_mod::<Wide>(&2, &3), 2);
    assert_eq!(mir_f::<Wide>(&3, &2, &3), Some(2));
    assert_eq!(mir_f::<Wide>(&3, &2, &-2), Some(-1));
    let vf = c(
        vec![
            Term {
                coeff: 3,
                lit: Lit::pos(0),
            },
            Term {
                coeff: 2,
                lit: Lit::neg(1),
            },
        ],
        4,
    );
    let vf_cut = mir_variable(3, &vf).expect("the variable-form rule must fire here");
    assert_eq!(
        vf_cut.terms,
        vec![
            Term {
                coeff: 2,
                lit: Lit::pos(0)
            },
            Term {
                coeff: 1,
                lit: Lit::neg(1)
            }
        ]
    );
    assert_eq!(vf_cut.degree, 3);
}

// ---------------------------------------------------------------------------
// The complete (`Big`) domain
// ---------------------------------------------------------------------------

fn big(x: i64) -> Big {
    Big::from(x)
}

fn widen(c: &Constraint) -> Constraint<Big> {
    Constraint::new(
        c.terms
            .iter()
            .map(|t| Term {
                coeff: big(t.coeff),
                lit: t.lit,
            })
            .collect(),
        big(c.degree),
    )
}

/// Every rule whose only failure mode is width refuses at [`Coeff`] on the
/// boundary case and **fires** at [`Big`] — which is the whole reason the
/// second instantiation exists. `veripb-checker`'s bridge turns exactly this
/// difference into "replay one tier up" rather than "count a skip".
#[test]
fn every_rule_that_refuses_on_width_fires_at_the_complete_domain() {
    // ADD: degree i64::MAX + 1.
    let a = c(
        vec![Term {
            coeff: 1,
            lit: Lit::pos(0),
        }],
        Coeff::MAX,
    );
    let b = c(
        vec![Term {
            coeff: 1,
            lit: Lit::pos(1),
        }],
        1,
    );
    assert_eq!(add(&a, &b), Err(GuardError::DegreeOverflow));
    assert!(add(&widen(&a), &widen(&b)).is_ok());

    // MULTIPLY: coefficient 2 * i64::MAX.
    let m = c(
        vec![Term {
            coeff: Coeff::MAX,
            lit: Lit::pos(0),
        }],
        1,
    );
    assert_eq!(multiply(2, &m), Err(GuardError::CoeffOverflow));
    assert!(multiply(big(2), &widen(&m)).is_ok());

    // WEAKEN: bug C verbatim, i64::MIN - 1.
    let w = c(
        vec![Term {
            coeff: 1,
            lit: Lit::pos(0),
        }],
        Coeff::MIN,
    );
    assert_eq!(weaken_degree(&w, 1), Err(GuardError::DegreeOverflow));
    assert!(weaken_degree(&widen(&w), big(1)).is_ok());

    // NEGATE: coeffSum - degree + 1 leaves i64.
    let n = c(
        vec![Term {
            coeff: Coeff::MAX,
            lit: Lit::pos(0),
        }],
        Coeff::MIN,
    );
    assert_eq!(negate(&n), Err(GuardError::DegreeOverflow));
    assert!(negate(&widen(&n)).is_ok());

    // NORMALIZE: the cancellation that shifts the degree below i64::MIN.
    let z = c(
        vec![
            Term {
                coeff: 1,
                lit: Lit::pos(0),
            },
            Term {
                coeff: 1,
                lit: Lit::neg(0),
            },
        ],
        Coeff::MIN,
    );
    assert_eq!(normalize(&z), Err(GuardError::DegreeOverflow));
    assert!(normalize(&widen(&z)).is_ok());

    // DIVIDE: ceil(i64::MIN / 1) is representable, so the boundary here is
    // the *multiply-then-divide* shape the live checker promotes through.
    let d = c(
        vec![Term {
            coeff: Coeff::MAX,
            lit: Lit::pos(0),
        }],
        1,
    );
    assert_eq!(multiply(4, &d), Err(GuardError::CoeffOverflow));
    let wide = multiply(big(4), &widen(&d)).unwrap();
    let back = divide(big(4), &wide).unwrap();
    assert_eq!(
        back,
        widen(&d),
        "multiply out of i64 and divide back in is exact"
    );
}

/// ...and what the complete domain computes is the *right* value, not the
/// wrapped one a machine word would have produced. A test that only checked
/// "it fires" would pass on a kernel that wrapped just as badly one tier up.
#[test]
fn the_complete_domain_computes_the_value_a_wrap_would_have_destroyed() {
    let a = c(
        vec![Term {
            coeff: 1,
            lit: Lit::pos(0),
        }],
        Coeff::MAX,
    );
    let b = c(
        vec![Term {
            coeff: 1,
            lit: Lit::pos(1),
        }],
        1,
    );
    let sum = add(&widen(&a), &widen(&b)).unwrap();
    assert_eq!(sum.degree, big(Coeff::MAX) + big(1));
    assert_ne!(
        sum.degree,
        big(Coeff::MIN),
        "i64::MAX + 1 wraps to i64::MIN"
    );

    let w = c(
        vec![Term {
            coeff: 1,
            lit: Lit::pos(0),
        }],
        Coeff::MIN,
    );
    let low = weaken_degree(&widen(&w), big(1)).unwrap();
    assert_eq!(low.degree, big(Coeff::MIN) - big(1));
    assert_ne!(
        low.degree,
        big(Coeff::MAX),
        "i64::MIN - 1 wraps to i64::MAX"
    );

    // The `pol_add_degree_underflow` regression instance, as kernel calls:
    // degree i64::MIN + 2, plus 5 x1 cancelling 5 ~x1, is i64::MIN - 3.
    let base = c(
        vec![
            Term {
                coeff: 5,
                lit: Lit::pos(0),
            },
            Term {
                coeff: 1,
                lit: Lit::pos(1),
            },
        ],
        Coeff::MIN + 2,
    );
    let axiom = c(
        vec![Term {
            coeff: 5,
            lit: Lit::neg(0),
        }],
        0,
    );
    assert_eq!(
        normalize(&add(&base, &axiom).unwrap()),
        Err(GuardError::DegreeOverflow),
        "the narrow domain must refuse rather than wrap"
    );
    let merged = normalize(&add(&widen(&base), &widen(&axiom)).unwrap()).unwrap();
    assert_eq!(merged.degree, big(Coeff::MIN) - big(3));
    assert_eq!(
        merged.terms,
        vec![Term {
            coeff: big(1),
            lit: Lit::pos(1)
        }]
    );
}

/// Wherever the narrow domain accepts, the complete one computes the same
/// constraint. Randomized over every rule `kernel_bridge` instantiates at
/// both tiers: ADD, MULTIPLY, DIVIDE, SATURATE, WEAKEN, NEGATE, NORMALIZE
/// and the two MIR forms, with magnitudes chosen so the narrow guards fire
/// often.
///
/// This is the regression guard that the two instantiations of a rule cannot
/// drift apart. It is *not* what makes the two-tier dispatch safe — that is
/// enforced by `tiered_step`'s control flow, which escalates only on a
/// width-limited skip, so a verdict the narrow tier reached is never
/// re-litigated, and each tier is independently sound.
///
/// The MIR forms are replayed **composed with `normalize`**, because that is
/// how the bridge dispatches them (`shadow_mir`'s `Ok(cut) => shadow_norm(cut)`).
/// Bare `mir`/`mir_variable` would look like coverage and not be: their
/// output is bounded by their input (`mirF(a) <= a`, and
/// `(floorDiv(A,k)+1)*r <= A`), so the narrow width-refusal arm is never
/// reached for them — measured 0 and 0 over this seed stream. Composed with
/// the normalization the bridge applies next it fires 39 and 808 times, and
/// the width arm is half the reason this test exists.
///
/// Per-rule floors, not just the global ones: MIR is the rule whose
/// accepting arm can silently vanish (a generator drift towards negative
/// coefficients sends every `mir` case to `NotNormalized`) while the global
/// counter still passes on the other seven.
#[test]
fn the_two_domains_agree_wherever_the_narrow_one_accepts() {
    // xorshift64, so the test is deterministic and dependency-free.
    let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };

    let mut narrow_accepts = 0usize;
    let mut narrow_refusals = 0usize;
    let mut accepts_by_rule: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut refusals_by_rule: BTreeMap<&'static str, usize> = BTreeMap::new();
    for _ in 0..20_000 {
        let coeff = |r: u64| -> Coeff {
            match r % 5 {
                0 => Coeff::MAX - (r >> 8) as i64 % 3,
                1 => Coeff::MIN + (r >> 8) as i64 % 3,
                2 => 0,
                _ => (r >> 8) as i64 % 2001 - 1000,
            }
        };
        let width = (next() % 4) as usize;
        let terms: Vec<Term> = (0..width)
            .map(|_| {
                let r = next();
                let var = (r % 3) as u32;
                let lit = if r % 2 == 0 {
                    Lit::pos(var)
                } else {
                    Lit::neg(var)
                };
                Term {
                    coeff: coeff(next()),
                    lit,
                }
            })
            .collect();
        let x = c(terms, coeff(next()));
        let y = {
            let r = next();
            c(
                vec![Term {
                    coeff: coeff(next()),
                    lit: Lit::pos((r % 3) as u32),
                }],
                coeff(next()),
            )
        };
        let k = (next() % 1000) as i64 + 1;
        let w = (next() % 1000) as i64;

        // Each entry is (rule name, narrow result, complete result); the two
        // results must agree whenever the narrow one produced anything at all.
        // The MIR forms are composed with `normalize` because that is what
        // `shadow_mir` does with their output; see the doc comment.
        let pairs: Vec<(&'static str, DomainPair)> = vec![
            ("add", (add(&x, &y), add(&widen(&x), &widen(&y)))),
            ("multiply", (multiply(k, &x), multiply(big(k), &widen(&x)))),
            ("divide", (divide(k, &x), divide(big(k), &widen(&x)))),
            ("saturate", (saturate(&x), saturate(&widen(&x)))),
            (
                "weaken",
                (weaken_degree(&x, w), weaken_degree(&widen(&x), big(w))),
            ),
            ("negate", (negate(&x), negate(&widen(&x)))),
            ("normalize", (normalize(&x), normalize(&widen(&x)))),
            (
                "mir",
                (
                    mir(k, &x).and_then(|cut| normalize(&cut)),
                    mir(big(k), &widen(&x)).and_then(|cut| normalize(&cut)),
                ),
            ),
            (
                "mir_variable",
                (
                    mir_variable(k, &x).and_then(|cut| normalize(&cut)),
                    mir_variable(big(k), &widen(&x)).and_then(|cut| normalize(&cut)),
                ),
            ),
        ];
        for (rule, (narrow, wide)) in pairs {
            match (&narrow, &wide) {
                (Ok(n), Ok(b)) => {
                    narrow_accepts += 1;
                    *accepts_by_rule.entry(rule).or_insert(0) += 1;
                    assert_eq!(widen(n), *b, "domains disagreed on {x:?} / {y:?}");
                }
                // A narrow refusal on width; the complete domain has no width
                // to refuse on, so it must have produced something.
                (Err(GuardError::DegreeOverflow | GuardError::CoeffOverflow), b) => {
                    narrow_refusals += 1;
                    *refusals_by_rule.entry(rule).or_insert(0) += 1;
                    assert!(b.is_ok(), "the complete domain refused on width: {b:?}");
                }
                // Every other refusal is a rule hypothesis, which is
                // width-independent and must fail identically at both.
                (Err(e), Err(f)) => assert_eq!(e, f),
                (Err(e), Ok(b)) => {
                    panic!("narrow refused with {e:?} but complete produced {b:?}")
                }
                (Ok(n), Err(f)) => panic!("complete refused with {f:?} but narrow gave {n:?}"),
            }
        }
    }
    // Both arms must actually be reached, or the test proves nothing.
    assert!(
        narrow_accepts > 1000,
        "only {narrow_accepts} narrow accepts"
    );
    assert!(
        narrow_refusals > 100,
        "only {narrow_refusals} narrow width refusals"
    );
    // ... and reached for every rule, not just in aggregate. Measured
    // 2026-08-23 over these 20_000 seeds (debug profile, overflow-checks and
    // debug-assertions on); every floor below is about half its measurement,
    // so ordinary reshuffling of the generator passes and a collapse does not:
    //
    //   accepts   add 15214  multiply  6560  divide 20000  saturate 6514
    //             weaken 15980  negate 13822  normalize 15107
    //             mir 8523  mir_variable 16637
    //   width     add  4786  multiply 13440  divide     0  saturate    0
    //   refusals  weaken  4020  negate  6178  normalize 4893
    //             mir 39  mir_variable 808
    //
    // `divide` and `saturate` never refuse on width — their output is bounded
    // by their input — so they carry an accept floor only; a floor of 0 would
    // assert nothing. The two MIR width-refusal counts are the ones the
    // composition with `normalize` exists to reach: with the bare rules they
    // are 0 and 0, measured on this same seed stream.
    for (rule, floor) in [
        ("add", 7500),
        ("multiply", 3000),
        ("divide", 10000),
        ("saturate", 3000),
        ("weaken", 8000),
        ("negate", 6500),
        ("normalize", 7500),
        ("mir", 4000),
        ("mir_variable", 8000),
    ] {
        let got = accepts_by_rule.get(rule).copied().unwrap_or(0);
        assert!(
            got >= floor,
            "the generator has stopped exercising {rule}: {got} narrow accepts, \
             expected at least {floor}. Full profile: {accepts_by_rule:?}"
        );
    }
    for (rule, floor) in [
        ("add", 2300),
        ("multiply", 6500),
        ("weaken", 2000),
        ("negate", 3000),
        ("normalize", 2400),
        ("mir", 15),
        ("mir_variable", 400),
    ] {
        let got = refusals_by_rule.get(rule).copied().unwrap_or(0);
        assert!(
            got >= floor,
            "the generator has stopped reaching {rule}'s narrow width refusal: {got}, \
             expected at least {floor}. Full profile: {refusals_by_rule:?}"
        );
    }
}
