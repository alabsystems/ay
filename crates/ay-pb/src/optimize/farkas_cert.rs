// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Farkas certificate format and a fast, machine-faithful CHECKER for the
//! exact-rational LP lower bound ([`crate::optimize::lp_bound`]).
//!
//! # What this is
//!
//! Today the LP bound is trusted because it is re-derived / re-checked at runtime
//! with exact arithmetic. This module lets the bound carry a **Farkas
//! certificate** — the non-negative dual multipliers `mu` plus the lifted
//! premises and the conclusion `obj >= L` — that is validated by a single fast
//! integer pass instead of by re-running the simplex.
//!
//! [`check_slack`] validates the supplied certificate with exact integer
//! arithmetic. Acceptance means the non-negative multipliers recombine the
//! premises into the claimed conclusion within the stated slack; this is the
//! runtime boundary used by the LP-bound path. It does not, by itself, establish
//! that the premises faithfully encode the original optimization problem.
//!
//! # Soundness posture (NON-NEGOTIABLE: never weaker than today)
//!
//! - The checker NEVER re-derives `mu`; it only re-checks the supplied `mu`. A
//!   wrong (too-high) bound cannot pass: step 3 forces `mu >= 0`, step 7 forces
//!   the `mu`-weighted premise coefficients to EQUAL the conclusion coefficients
//!   exactly (zero residual per variable), and step 8 forces
//!   `combConst <= conclConst + sigma` with `0 <= sigma < margin`. These are
//!   exactly the hypotheses of `slack_farkas`.
//! - **All checker arithmetic is [`num_bigint::BigInt`]** (NOT `i128`). Cross
//!   products multiply two denominators; an overflowing fixed-width integer would
//!   silently wrap and could turn a false certificate into an accept. BigInt makes
//!   that impossible. No `unsafe`, no float.
//! - The emit path (`lp_bound::lp_lower_bound_with_cert`) is gated behind
//!   `AY_PB_FARKAS_CERT` and is, by itself, a pure add-on: the certificate is
//!   built from data already in hand and validated; on a failed check the caller
//!   keeps today's exact path verbatim.
//!
//! # Trust boundary (unchanged)
//!
//! The certificate proves `mu` entails `obj >= L` from THESE premises. It does NOT
//! prove the premises faithfully encode the PB instance (the
//! [`crate::optimize::lp_bound`] `LpModel::build` mapping). That encoding trust is
//! identical to today; the witness backstop in
//! [`crate::optimize::native_oll`] still re-checks any claimed optimum against the
//! ORIGINAL constraints.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Serialize};

/// An unreduced rational as a `(num, den)` integer pair with `den > 0`.
///
/// This pair is **never reduced**: the checker compares values by exact cross
/// multiplication. Decimal-string serialization preserves the same integers
/// across a persistence and replay round trip.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct QPair {
    #[serde(with = "bigint_decimal")]
    pub(crate) num: BigInt,
    #[serde(with = "bigint_decimal")]
    pub(crate) den: BigInt,
}

impl QPair {
    /// Construct a pair. Does not enforce `den > 0` (the checker's step 1 does).
    pub(crate) fn new(num: BigInt, den: BigInt) -> Self {
        Self { num, den }
    }

    /// The integer `n` as `n / 1`.
    pub(crate) fn from_int(n: &BigInt) -> Self {
        Self {
            num: n.clone(),
            den: BigInt::one(),
        }
    }
}

/// Serde helper: serialize `BigInt` as a decimal string (portable, lossless).
mod bigint_decimal {
    use num_bigint::BigInt;
    use serde::{Deserialize, Deserializer, Serializer};
    use std::str::FromStr;

    pub(super) fn serialize<S: Serializer>(v: &BigInt, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&v.to_string())
    }

    pub(super) fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<BigInt, D::Error> {
        let s = String::deserialize(d)?;
        BigInt::from_str(&s).map_err(serde::de::Error::custom)
    }
}

/// Relation kind of a linear constraint.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum Kind {
    /// `coeffs . x <= const`.
    Le,
    /// `coeffs . x >= const`.
    Ge,
    /// `coeffs . x  = const` (REJECTED by the checker, as in Lean).
    Eq,
}

/// A linear constraint over named variables with integer-pair data.
///
/// Variables are identified by `String` (the LP column index rendered as text),
/// matching the Lean `LinConZ` whose variables are `String`. This keeps the
/// collapse / `addEntry` map algebra byte-identical to the Lean port.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct LinConZ {
    pub(crate) coeffs: Vec<(String, QPair)>,
    pub(crate) kind: Kind,
    pub(crate) constant: QPair,
}

/// An exact entailment certificate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CertZ {
    pub(crate) premises: Vec<LinConZ>,
    pub(crate) multipliers: Vec<QPair>,
    pub(crate) conclusion: LinConZ,
}

/// A slack-tolerant certificate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SCertZ {
    pub(crate) base: CertZ,
    pub(crate) slack: QPair,
    pub(crate) margin: QPair,
}

/// The Farkas certificate emitted alongside an LP lower bound.
///
/// `cert` is the checkable object; `claimed_bound` is the integer floor `L` the LP
/// path returns today. `num_vars` is provenance only (NOT trusted by the checker);
/// it binds the certificate to the call that produced it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct LpFarkasCert {
    pub(crate) cert: SCertZ,
    pub(crate) claimed_bound: i128,
    pub(crate) num_vars: u32,
}

// ---------------------------------------------------------------------------
// Integer-pair primitives (mirror CertCheckerZ.lean:79-96, SlackCertZ.lean:64).
// `den > 0` is assumed (checked by step 1 of `check_slack`); these preserve the
// comparison direction because cross-multiplying by positive denominators does.
// ALL arithmetic is BigInt: cross-products never overflow.
// ---------------------------------------------------------------------------

/// `0 <= num/den`  <=>  `0 <= num`  (given `den > 0`). Mirrors `nonnegZ`.
fn nonneg(p: &QPair) -> bool {
    !p.num.is_negative()
}

/// `toQ a <= toQ b`  <=>  `a.num*b.den <= b.num*a.den`. Mirrors `leZ`.
fn le(a: &QPair, b: &QPair) -> bool {
    &a.num * &b.den <= &b.num * &a.den
}

/// `toQ a < toQ b`  <=>  `a.num*b.den < b.num*a.den`. Mirrors `ltZ`.
fn lt(a: &QPair, b: &QPair) -> bool {
    &a.num * &b.den < &b.num * &a.den
}

/// `toQ a = 0`  <=>  `a.num = 0`. Mirrors `isZeroZ`.
fn is_zero(a: &QPair) -> bool {
    a.num.is_zero()
}

/// Unreduced sum `(a.num*b.den + b.num*a.den, a.den*b.den)`. Mirrors `addZ`.
fn add(a: &QPair, b: &QPair) -> QPair {
    QPair::new(&a.num * &b.den + &b.num * &a.den, &a.den * &b.den)
}

/// Unreduced product `(a.num*b.num, a.den*b.den)`. Mirrors `mulZ`.
fn mul(a: &QPair, b: &QPair) -> QPair {
    QPair::new(&a.num * &b.num, &a.den * &b.den)
}

/// Negation `(-num, den)`. Mirrors `negZ`.
fn neg(a: &QPair) -> QPair {
    QPair::new(-&a.num, a.den.clone())
}

// ---------------------------------------------------------------------------
// Map algebra, ported one-to-one from CertCheckerZ.lean:164-218.
// ---------------------------------------------------------------------------

/// `scaleMapZ k m`: multiply every coefficient by `k`.
fn scale_map(k: &QPair, m: &[(String, QPair)]) -> Vec<(String, QPair)> {
    m.iter().map(|(v, c)| (v.clone(), mul(k, c))).collect()
}

/// `negMapZ m`: negate every coefficient.
fn neg_map(m: &[(String, QPair)]) -> Vec<(String, QPair)> {
    m.iter().map(|(v, c)| (v.clone(), neg(c))).collect()
}

/// `normalizeZ lc`: rewrite a constraint into a list of `<=`-form `(coeffs, const)`
/// rows. `Ge` flips signs (one row); `Eq` produces two rows; `Le` is identity.
fn normalize_rows(lc: &LinConZ) -> Vec<(Vec<(String, QPair)>, QPair)> {
    match lc.kind {
        Kind::Le => vec![(lc.coeffs.clone(), lc.constant.clone())],
        Kind::Ge => vec![(neg_map(&lc.coeffs), neg(&lc.constant))],
        Kind::Eq => vec![
            (lc.coeffs.clone(), lc.constant.clone()),
            (neg_map(&lc.coeffs), neg(&lc.constant)),
        ],
    }
}

/// `rowCoeffsZ mu lc`: the multiplier-scaled, `<=`-normalized coefficient map of a
/// single premise (flattened over normalize rows).
fn row_coeffs(mu: &QPair, lc: &LinConZ) -> Vec<(String, QPair)> {
    let mut out = Vec::new();
    for (coeffs, _) in normalize_rows(lc) {
        out.extend(scale_map(mu, &coeffs));
    }
    out
}

/// `combCoeffsZ pairs`: concatenation of every premise's `row_coeffs`.
fn comb_coeffs(pairs: &[(&LinConZ, &QPair)]) -> Vec<(String, QPair)> {
    let mut out = Vec::new();
    for (lc, mu) in pairs {
        out.extend(row_coeffs(mu, lc));
    }
    out
}

/// `rowConstZ mu lc`: `Sum mu * row.const` over normalize rows, via repeated `add`
/// from `(0, 1)`. Mirrors the `foldr addZ (0,1)` order exactly.
fn row_const(mu: &QPair, lc: &LinConZ) -> QPair {
    let consts: Vec<QPair> = normalize_rows(lc)
        .into_iter()
        .map(|(_, c)| mul(mu, &c))
        .collect();
    // foldr addZ (0,1): fold from the right.
    let mut acc = QPair::new(BigInt::zero(), BigInt::one());
    for c in consts.into_iter().rev() {
        acc = add(&c, &acc);
    }
    acc
}

/// `combConstZ pairs`: `add (row_const ..) (comb_const rest)`, right-associated,
/// from `(0, 1)`. Mirrors the Lean recursion order exactly.
fn comb_const(pairs: &[(&LinConZ, &QPair)]) -> QPair {
    let mut acc = QPair::new(BigInt::zero(), BigInt::one());
    for (lc, mu) in pairs.iter().rev() {
        acc = add(&row_const(mu, lc), &acc);
    }
    acc
}

/// `addEntryZ acc v c`: insert/accumulate `c` at key `v` in an assoc list,
/// preserving first-seen order. Mirrors the Lean recursion.
fn add_entry(acc: &mut Vec<(String, QPair)>, v: &str, c: &QPair) {
    for entry in acc.iter_mut() {
        if entry.0 == v {
            entry.1 = add(&entry.1, c);
            return;
        }
    }
    acc.push((v.to_string(), c.clone()));
}

/// `collapseZ m`: left-fold `m` into one entry per variable via `add_entry`.
fn collapse(m: &[(String, QPair)]) -> Vec<(String, QPair)> {
    let mut acc: Vec<(String, QPair)> = Vec::new();
    for (v, c) in m {
        add_entry(&mut acc, v, c);
    }
    acc
}

/// `normalizeConclusionZ lc`: `Le` -> identity; `Ge` -> sign-flipped; `Eq` -> None.
fn normalize_conclusion(lc: &LinConZ) -> Option<(Vec<(String, QPair)>, QPair)> {
    match lc.kind {
        Kind::Le => Some((lc.coeffs.clone(), lc.constant.clone())),
        Kind::Ge => Some((neg_map(&lc.coeffs), neg(&lc.constant))),
        Kind::Eq => None,
    }
}

/// `diffMapZ pairs conclCoeffs`: `combCoeffs pairs ++ negMap conclCoeffs`.
fn diff_map(
    pairs: &[(&LinConZ, &QPair)],
    concl_coeffs: &[(String, QPair)],
) -> Vec<(String, QPair)> {
    let mut out = comb_coeffs(pairs);
    out.extend(neg_map(concl_coeffs));
    out
}

/// Every denominator is `> 0` (`allDenPos` + slack/margin denominators).
fn all_den_pos(sc: &SCertZ) -> bool {
    let cz = &sc.base;
    cz.premises.iter().all(|lc| {
        lc.coeffs.iter().all(|(_, c)| c.den.is_positive()) && lc.constant.den.is_positive()
    }) && cz.multipliers.iter().all(|mu| mu.den.is_positive())
        && cz
            .conclusion
            .coeffs
            .iter()
            .all(|(_, c)| c.den.is_positive())
        && cz.conclusion.constant.den.is_positive()
        && sc.slack.den.is_positive()
        && sc.margin.den.is_positive()
}

/// **The exact-rational slack checker.**
///
/// Returns `true` only when all eight checks below pass: positive
/// denominators, one non-negative multiplier per premise, non-negative slack,
/// strict slack margin, exact coefficient recombination, exact right-hand-side
/// recombination, and exact conclusion matching.
///
/// A `true` result is the runtime acceptance boundary for this certificate.
/// Its public trust base is this Rust implementation and the exact integer /
/// rational arithmetic it calls. The maintained tests exercise accepted and
/// rejected certificates; `verification/lean/FarkasAnchor.lean` is a
/// fixed-fixture cross-check, not an end-to-end machine proof of this function.
/// Independent consumers should recombine the inequalities themselves when a
/// separate trust boundary is required.
///
#[must_use]
pub(crate) fn check_slack(sc: &SCertZ) -> bool {
    let cz = &sc.base;

    // 1. All denominators positive.
    if !all_den_pos(sc) {
        return false;
    }
    // 2. One multiplier per premise.
    if cz.premises.len() != cz.multipliers.len() {
        return false;
    }
    // 3. Every multiplier >= 0 (Farkas sign condition).
    if !cz.multipliers.iter().all(nonneg) {
        return false;
    }
    // 4. sigma >= 0.
    if !nonneg(&sc.slack) {
        return false;
    }
    // 5. sigma < margin (strict headroom).
    if !lt(&sc.slack, &sc.margin) {
        return false;
    }
    // 6. Conclusion normalizes (Eq is rejected).
    let Some((concl_coeffs, concl_const)) = normalize_conclusion(&cz.conclusion) else {
        return false;
    };

    let pairs: Vec<(&LinConZ, &QPair)> = cz.premises.iter().zip(cz.multipliers.iter()).collect();

    // 7. Coefficients cancel exactly (no slack on coefficients).
    if !collapse(&diff_map(&pairs, &concl_coeffs))
        .iter()
        .all(|(_, c)| is_zero(c))
    {
        return false;
    }

    // 8. combConst <= conclConst + sigma  (the ONE slack site).
    le(&comb_const(&pairs), &add(&concl_const, &sc.slack))
}

/// Is the emit-cert path enabled? Gated behind `AY_PB_FARKAS_CERT`. Default OFF,
/// so the certificate machinery is a pure opt-in add-on that cannot perturb the
/// existing (already-sound) bound path until explicitly enabled.
#[must_use]
pub(crate) fn cert_emit_enabled() -> bool {
    std::env::var_os("AY_PB_FARKAS_CERT").is_some()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn qp(n: i128, d: i128) -> QPair {
        QPair::new(BigInt::from(n), BigInt::from(d))
    }

    fn qi(n: i128) -> QPair {
        QPair::from_int(&BigInt::from(n))
    }

    fn var(name: &str, c: QPair) -> (String, QPair) {
        (name.to_string(), c)
    }

    // --- Faithful port of the Lean demoSlackCert (SlackCertZ.lean:401-410). ---
    // P0: x <= 1 (mu0=1), P1: y <= 2 (mu1=1); conclusion x + y <= 4.
    // combConst 3 <= conclConst 4 + slack 1/4; slack 1/4 < margin 1/2.
    fn demo_slack_cert() -> SCertZ {
        SCertZ {
            base: CertZ {
                premises: vec![
                    LinConZ {
                        coeffs: vec![var("x", qi(1))],
                        kind: Kind::Le,
                        constant: qi(1),
                    },
                    LinConZ {
                        coeffs: vec![var("y", qi(1))],
                        kind: Kind::Le,
                        constant: qi(2),
                    },
                ],
                multipliers: vec![qi(1), qi(1)],
                conclusion: LinConZ {
                    coeffs: vec![var("x", qi(1)), var("y", qi(1))],
                    kind: Kind::Le,
                    constant: qi(4),
                },
            },
            slack: qp(1, 4),
            margin: qp(1, 2),
        }
    }

    #[test]
    fn demo_slack_cert_accepts() {
        // Bit-identical to the Lean `demoSlackCert_checks : ... = true` (by decide).
        assert!(check_slack(&demo_slack_cert()));
    }

    #[test]
    fn exact_cert_with_zero_slack_accepts() {
        // The exact case: slack 0, the demo bound 3 <= 4 holds outright.
        let mut sc = demo_slack_cert();
        sc.slack = qi(0);
        sc.margin = qi(1);
        assert!(check_slack(&sc));
    }

    // ----------------------- ADVERSARIAL: must REJECT -----------------------

    #[test]
    fn adversarial_tampered_multiplier_rejected() {
        // Inflate mu1 from 1 to 2. Now combCoeffs = x + 2y, which no longer cancels
        // the conclusion functional x + y -> step 7 fails.
        let mut sc = demo_slack_cert();
        sc.base.multipliers[1] = qi(2);
        assert!(
            !check_slack(&sc),
            "a tampered multiplier that breaks coefficient cancellation MUST be rejected"
        );
    }

    #[test]
    fn adversarial_negative_multiplier_rejected() {
        // A negative Farkas multiplier violates the sign condition (step 3).
        let mut sc = demo_slack_cert();
        sc.base.multipliers[0] = qi(-1);
        assert!(
            !check_slack(&sc),
            "a negative multiplier MUST be rejected (Farkas sign condition)"
        );
    }

    #[test]
    fn adversarial_inflated_bound_rejected() {
        // Inflate the claimed bound: change conclusion constant so combConst (3)
        // exceeds conclConst + slack. With a Le conclusion x+y <= B, lowering B to 2
        // means 3 <= 2 + 1/4 is false -> step 8 fails. (A too-TIGHT upper-bound
        // conclusion is the analogue of a too-HIGH lower bound.)
        let mut sc = demo_slack_cert();
        sc.base.conclusion.constant = qi(2);
        assert!(
            !check_slack(&sc),
            "an inflated/over-tight bound that exceeds the slack budget MUST be rejected"
        );
    }

    #[test]
    fn adversarial_ge_inflated_lower_bound_rejected() {
        // The real LP use: a Ge lower-bound conclusion. Premises x>=0, y>=0 with
        // mu = 1,1 prove x + y >= 0. Claiming x + y >= 5 (too HIGH) must be rejected:
        // normalized combConst = 0, conclConst(normalized) = -5; step 8 needs
        // 0 <= -5 + slack, i.e. slack >= 5, but slack is small -> reject.
        let sc = SCertZ {
            base: CertZ {
                premises: vec![
                    LinConZ {
                        coeffs: vec![var("x", qi(1))],
                        kind: Kind::Ge,
                        constant: qi(0),
                    },
                    LinConZ {
                        coeffs: vec![var("y", qi(1))],
                        kind: Kind::Ge,
                        constant: qi(0),
                    },
                ],
                multipliers: vec![qi(1), qi(1)],
                conclusion: LinConZ {
                    coeffs: vec![var("x", qi(1)), var("y", qi(1))],
                    kind: Kind::Ge,
                    constant: qi(5), // INFLATED: x+y >= 5 is NOT entailed by x,y >= 0.
                },
            },
            slack: qi(0),
            margin: qi(1),
        };
        assert!(
            !check_slack(&sc),
            "a too-HIGH lower bound (the soundness-critical case) MUST be rejected"
        );
    }

    #[test]
    fn ge_valid_lower_bound_accepts() {
        // Same shape but a VALID lower bound: x + y >= 0 is entailed by x,y >= 0.
        let sc = SCertZ {
            base: CertZ {
                premises: vec![
                    LinConZ {
                        coeffs: vec![var("x", qi(1))],
                        kind: Kind::Ge,
                        constant: qi(0),
                    },
                    LinConZ {
                        coeffs: vec![var("y", qi(1))],
                        kind: Kind::Ge,
                        constant: qi(0),
                    },
                ],
                multipliers: vec![qi(1), qi(1)],
                conclusion: LinConZ {
                    coeffs: vec![var("x", qi(1)), var("y", qi(1))],
                    kind: Kind::Ge,
                    constant: qi(0),
                },
            },
            slack: qi(0),
            margin: qi(1),
        };
        assert!(
            check_slack(&sc),
            "a valid Farkas lower bound MUST be accepted"
        );
    }

    #[test]
    fn adversarial_eq_conclusion_rejected() {
        // The checker rejects Eq conclusions (normalizeConclusionZ -> None).
        let mut sc = demo_slack_cert();
        sc.base.conclusion.kind = Kind::Eq;
        assert!(!check_slack(&sc), "an Eq conclusion MUST be rejected");
    }

    #[test]
    fn adversarial_negative_slack_rejected() {
        // sigma < 0 would weaken in the wrong direction; step 4 rejects it.
        let mut sc = demo_slack_cert();
        sc.slack = qp(-1, 4);
        assert!(!check_slack(&sc), "a negative slack MUST be rejected");
    }

    #[test]
    fn adversarial_slack_exceeds_margin_rejected() {
        // sigma must be strictly below margin (step 5).
        let mut sc = demo_slack_cert();
        sc.slack = qp(1, 2);
        sc.margin = qp(1, 2); // sigma == margin, not strictly less.
        assert!(
            !check_slack(&sc),
            "slack not strictly below margin MUST be rejected"
        );
    }

    #[test]
    fn adversarial_zero_denominator_rejected() {
        // A non-positive denominator breaks the cross-multiplication contract.
        let mut sc = demo_slack_cert();
        sc.base.premises[0].coeffs[0].1 = qp(1, 0);
        assert!(
            !check_slack(&sc),
            "a non-positive denominator MUST be rejected"
        );
    }

    #[test]
    fn adversarial_negative_denominator_rejected() {
        // Negative denominators would flip comparison directions; reject them.
        let mut sc = demo_slack_cert();
        sc.base.conclusion.constant = qp(-4, -1); // value 4 but den < 0.
        assert!(
            !check_slack(&sc),
            "a negative denominator MUST be rejected (den > 0 required)"
        );
    }

    #[test]
    fn adversarial_length_mismatch_rejected() {
        // More premises than multipliers (or vice versa) is rejected (step 2).
        let mut sc = demo_slack_cert();
        sc.base.multipliers.pop();
        assert!(
            !check_slack(&sc),
            "premise/multiplier length mismatch MUST be rejected"
        );
    }

    #[test]
    fn unreduced_pairs_accepted_like_lean() {
        // The checker NEVER reduces fractions. Encode the demo with deliberately
        // unreduced pairs (2/2 = 1, 8/2 = 4) and confirm acceptance is unchanged.
        let mut sc = demo_slack_cert();
        sc.base.multipliers = vec![qp(2, 2), qp(3, 3)]; // both == 1, unreduced.
        sc.base.conclusion.constant = qp(8, 2); // == 4, unreduced.
        assert!(
            check_slack(&sc),
            "unreduced equivalent pairs MUST behave identically (no gcd reduction)"
        );
    }

    #[test]
    fn slack_absorbs_small_rounding_gap() {
        // The slack's purpose: accept a bound that misses the exact threshold by a
        // hair but stays within sigma. Conclusion x+y <= 2 (too tight by 1) but
        // slack 1 absorbs it: combConst 3 <= 2 + 1.
        let mut sc = demo_slack_cert();
        sc.base.conclusion.constant = qi(2);
        sc.slack = qi(1);
        sc.margin = qi(2);
        assert!(check_slack(&sc));
        // ...but slack 1/2 does NOT cover a gap of 1: 3 <= 2 + 1/2 is false.
        sc.slack = qp(1, 2);
        sc.margin = qi(1);
        assert!(!check_slack(&sc));
    }

    #[test]
    fn big_multiplier_no_overflow() {
        // A multiplier whose numerator far exceeds i128 must be handled by BigInt
        // without wrapping. x <= 1 with mu = 10^40, conclusion 10^40 x <= 10^40.
        let big: BigInt = BigInt::from(10u8).pow(40);
        let sc = SCertZ {
            base: CertZ {
                premises: vec![LinConZ {
                    coeffs: vec![var("x", qi(1))],
                    kind: Kind::Le,
                    constant: qi(1),
                }],
                multipliers: vec![QPair::from_int(&big)],
                conclusion: LinConZ {
                    coeffs: vec![var("x", QPair::from_int(&big))],
                    kind: Kind::Le,
                    constant: QPair::from_int(&big),
                },
            },
            slack: qi(0),
            margin: qi(1),
        };
        assert!(
            check_slack(&sc),
            "huge multipliers must be exact via BigInt (no overflow)"
        );
        // And an inflated huge bound is still rejected: 10^40 x <= 10^40 - 1.
        let mut bad = sc;
        bad.base.conclusion.constant = QPair::from_int(&(&big - BigInt::one()));
        assert!(
            !check_slack(&bad),
            "an inflated huge bound must still be rejected exactly"
        );
    }

    #[test]
    fn serde_round_trip_preserves_decision() {
        let sc = demo_slack_cert();
        let json = serde_json::to_string(&sc).expect("serialize");
        let back: SCertZ = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(sc, back);
        assert_eq!(check_slack(&sc), check_slack(&back));
        // Decimal-string encoding of BigInt is present in the JSON.
        assert!(json.contains('"'));
    }

    /// Rust<->Lean kernel-anchor agreement on the REAL emitted fixtures. The
    /// `verification/lean/FarkasAnchor.lean` theorems
    /// `demoRealCert_accepts`/`demoTamperedCert_rejects` (proven `by decide`, no
    /// axioms) say the Lean kernel checker ACCEPTS `valid_cert.json` and REJECTS
    /// `tampered_cert.json`. This test confirms the REAL `check_slack` (the one
    /// used by the certificate path) agrees on the same on-disk bytes
    /// — the Rust side of the per-fixture coupling the kernel re-checker relies
    /// on. (Honest caveat: the JSON->cert deserialization is not itself in the
    /// Lean kernel; what is kernel-checked is that the transcribed literal
    /// reduces to the same `Bool`.)
    #[test]
    fn check_slack_agrees_with_lean_anchor_on_emitted_fixtures() {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../verification/lean/farkas_anchor");
        let valid_path = dir.join("valid_cert.json");
        let tampered_path = dir.join("tampered_cert.json");
        if !valid_path.exists() || !tampered_path.exists() {
            eprintln!(
                "SKIP check_slack_agrees_with_lean_anchor_on_emitted_fixtures: fixtures absent \
                 ({})",
                dir.display()
            );
            return;
        }
        let valid: SCertZ = serde_json::from_str(
            &std::fs::read_to_string(&valid_path).expect("read valid_cert.json"),
        )
        .expect("deserialize valid_cert.json");
        let tampered: SCertZ = serde_json::from_str(
            &std::fs::read_to_string(&tampered_path).expect("read tampered_cert.json"),
        )
        .expect("deserialize tampered_cert.json");

        // Lean `demoRealCert_accepts`: the genuine cert is ACCEPTED.
        assert!(
            check_slack(&valid),
            "valid_cert.json must be ACCEPTED (matches Lean demoRealCert_accepts)"
        );
        // Lean `demoTamperedCert_rejects`: the inflated bound is REJECTED.
        assert!(
            !check_slack(&tampered),
            "tampered_cert.json must be REJECTED (matches Lean demoTamperedCert_rejects)"
        );
    }

    #[test]
    fn duplicate_var_entries_collapse() {
        // Two coefficient entries for the same var must collapse (add_entry), so a
        // conclusion that splits x into x+x cancels a combined 2x premise.
        let sc = SCertZ {
            base: CertZ {
                premises: vec![LinConZ {
                    coeffs: vec![var("x", qi(2))],
                    kind: Kind::Le,
                    constant: qi(2),
                }],
                multipliers: vec![qi(1)],
                conclusion: LinConZ {
                    // 2x written as x + x; collapse must merge to 2x and cancel.
                    coeffs: vec![var("x", qi(1)), var("x", qi(1))],
                    kind: Kind::Le,
                    constant: qi(2),
                },
            },
            slack: qi(0),
            margin: qi(1),
        };
        assert!(
            check_slack(&sc),
            "duplicate-var entries must collapse and cancel"
        );
    }
}
