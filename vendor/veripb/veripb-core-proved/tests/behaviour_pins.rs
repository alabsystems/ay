//! The functions the island claims about are the functions that *run*.
//!
//! `tests/island_sync.rs` pins the correspondence between this crate and the
//! `clean { }` island textually: it reads `src/lib.rs` and
//! `src/trust_surface.rs` and compares bodies, citation sites and theorem
//! names. That is the right shape for a claim about *text* — the island body
//! must be the `.lean` file, the `ensures` clause must sit on the function it
//! is about — but it is the wrong shape for a claim about *behaviour*, and an
//! adversarial re-read found three ways to satisfy every textual pin while
//! changing what the checker computes:
//!
//! 1. **Retype the twin.** The body pin captures the text from the opening
//!    brace onward, so the signature was outside it. Changing
//!    `trust_surface::cap_coeff_i64` to take and return `u64` left the pinned
//!    body identical while making it compute an *unsigned* minimum — a
//!    different function, discharging an island theorem stated over `Int`.
//! 2. **Move the real body elsewhere.** The pin requires exactly one line
//!    declaring `pub fn cap_coeff(`, which a decoy inside `#[cfg(any())]`
//!    satisfies while never being compiled. The pinned text then constrains
//!    nothing, and the live code is free: `cap_coeff(3, -1)` returning `3`
//!    passed every test.
//! 3. **Cut the path.** SATURATE does not call `cap_coeff` directly. It goes
//!    through `<C as CoeffDomain>::cap_coeff`, a one-line delegation that no
//!    pin covered, and `<Coeff as Exact>::cap_coeff` beside it. Rewriting both
//!    to return the coefficient unchanged stopped SATURATE capping anything
//!    above a degree of 1000 — with the whole suite green *and*
//!    `scripts/verify-proofs.sh` reporting OK.
//!
//! The third is the serious one. SATURATE is unsound without capping, and the
//! `ensures` clause on `cap_coeff_i64` is the one compiler-checked contract
//! this crate puts on soundness-critical code; an attack that leaves the
//! contract in place and reroutes around it defeats the whole apparatus.
//!
//! What all three have in common is that they are invisible to a test that
//! reads source. So this file reads none. Every test here *calls* the code and
//! compares against a minimum computed in the test itself, which is immune to
//! how the callee is spelled, which width it is typed at, which module it
//! lives in, and how many delegations sit between the entry point and the
//! arithmetic. The textual pins stay — they catch things behaviour cannot, like
//! a citation migrating to the wrong function — but they are no longer the only
//! thing standing between an edit and a silent falsehood.
//!
//! The oracle is deliberately not `std::cmp::min`: it is written out as a
//! comparison so that this file states the property rather than delegating it
//! to a function that could itself be the thing under test.

use veripb_core_proved::{
    Big, Coeff, CoeffDomain, Constraint, Exact, Lit, Term, Wide, cap_coeff, cap_coeff_wide,
    saturate,
};

/// `min`, written out. The property SATURATE needs, stated independently of
/// anything in the crate under test.
fn expected_cap(degree: i128, coeff: i128) -> i128 {
    if coeff <= degree { coeff } else { degree }
}

/// A deterministic, dependency-free xorshift64*, as the rest of this crate's
/// randomized tests use.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    /// A value that is small often and extreme sometimes, so the interesting
    /// region around the degree is sampled as well as the boundaries.
    fn coeff(&mut self) -> Coeff {
        let raw = self.next();
        match raw % 4 {
            0 => (raw >> 2) as Coeff,
            1 => ((raw >> 2) % 2_001) as Coeff - 1_000,
            2 => Coeff::MAX - ((raw >> 2) % 8) as Coeff,
            _ => Coeff::MIN + ((raw >> 2) % 8) as Coeff,
        }
    }
}

/// Every `i64` boundary that has ever mattered here, plus the values either
/// side of them.
const EDGES: &[Coeff] = &[
    Coeff::MIN,
    Coeff::MIN + 1,
    -1_000_001,
    -1_000,
    -2,
    -1,
    0,
    1,
    2,
    1_000,
    1_000_001,
    Coeff::MAX - 1,
    Coeff::MAX,
];

/// The narrow `cap_coeff` — the one function of this crate carrying a
/// compiler-checked `ensures` contract — computes `min`, on every boundary
/// pair and at random.
///
/// A body pin cannot see this. A decoy under `#[cfg(any())]` cannot answer a
/// call, and a retyped signature would not compile against these `Coeff`
/// arguments.
#[test]
fn cap_coeff_is_the_minimum() {
    for &degree in EDGES {
        for &coeff in EDGES {
            assert_eq!(
                i128::from(cap_coeff(degree, coeff)),
                expected_cap(i128::from(degree), i128::from(coeff)),
                "cap_coeff({degree}, {coeff}) is not min(coeff, degree)"
            );
        }
    }
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    for _ in 0..200_000 {
        let (degree, coeff) = (rng.coeff(), rng.coeff());
        assert_eq!(
            i128::from(cap_coeff(degree, coeff)),
            expected_cap(i128::from(degree), i128::from(coeff)),
            "cap_coeff({degree}, {coeff}) is not min(coeff, degree)"
        );
    }
}

/// The same for the `Wide` twin, which `mir::mir_f` uses inside the guard
/// arithmetic where the value is bounded only by the divisor.
#[test]
fn cap_coeff_wide_is_the_minimum() {
    for &degree in EDGES {
        for &coeff in EDGES {
            let (d, c) = (Wide::from(degree), Wide::from(coeff));
            assert_eq!(
                cap_coeff_wide(d, c),
                expected_cap(d, c),
                "cap_coeff_wide({d}, {c}) is not min(coeff, degree)"
            );
        }
    }
    // The `Wide` domain reaches past `i64`, which is the whole reason it
    // exists, so sample there too.
    let mut rng = Rng(0x1234_5678_9ABC_DEF1);
    for _ in 0..200_000 {
        let d = Wide::from(rng.coeff()) * Wide::from(rng.coeff() % 4 + 1);
        let c = Wide::from(rng.coeff()) * Wide::from(rng.coeff() % 4 + 1);
        assert_eq!(
            cap_coeff_wide(d, c),
            expected_cap(d, c),
            "cap_coeff_wide({d}, {c}) is not min(coeff, degree)"
        );
    }
}

/// Both `CoeffDomain` delegations compute `min` too.
///
/// These are the one-line forwards that attack 3 rewrote. Pinning them by
/// behaviour rather than by text means it does not matter what they forward
/// to, or whether they forward at all.
#[test]
fn the_coeff_domain_delegations_are_the_minimum() {
    for &degree in EDGES {
        for &coeff in EDGES {
            assert_eq!(
                i128::from(<Coeff as CoeffDomain>::cap_coeff(&degree, &coeff)),
                expected_cap(i128::from(degree), i128::from(coeff)),
                "<i64 as CoeffDomain>::cap_coeff({degree}, {coeff}) is not min"
            );
            let (bd, bc) = (Big::from(degree), Big::from(coeff));
            assert_eq!(
                <Big as CoeffDomain>::cap_coeff(&bd, &bc),
                Big::from(expected_cap(i128::from(degree), i128::from(coeff))),
                "<Big as CoeffDomain>::cap_coeff({degree}, {coeff}) is not min"
            );
            assert_eq!(
                <Wide as Exact>::cap_coeff(&Wide::from(degree), &Wide::from(coeff)),
                expected_cap(i128::from(degree), i128::from(coeff)),
                "<i128 as Exact>::cap_coeff({degree}, {coeff}) is not min"
            );
            assert_eq!(
                <Big as Exact>::cap_coeff(&bd, &bc),
                Big::from(expected_cap(i128::from(degree), i128::from(coeff))),
                "<Big as Exact>::cap_coeff({degree}, {coeff}) is not min"
            );
        }
    }
}

/// A normalized constraint whose coefficients straddle the degree.
///
/// `saturate` refuses anything not normalized, so the degree and every
/// coefficient are non-negative; that is not a weakening of the test, because
/// capping only has content above the degree and the normalized case is the
/// only one the rule accepts.
fn straddling(degree: Coeff, coeffs: &[Coeff]) -> Constraint {
    Constraint::new(
        coeffs
            .iter()
            .enumerate()
            .map(|(i, &coeff)| Term {
                coeff,
                lit: Lit::pos(i as u32),
            })
            .collect(),
        degree,
    )
}

/// **The load-bearing test.** SATURATE caps every coefficient at the degree,
/// end to end, whatever path it takes to get there.
///
/// This is the property `VeriPbCore.entails_saturate` is proved under and
/// `entails_saturate_of_key` consumes, and the one that attack 3 broke while
/// leaving every other test and `scripts/verify-proofs.sh` green. Nothing here
/// mentions `cap_coeff`: the test asserts what the *rule* does, so rerouting
/// the rule around the pinned function does not help.
#[test]
fn saturate_caps_every_coefficient_at_the_degree() {
    let cases: &[(Coeff, &[Coeff])] = &[
        (0, &[0, 1, 2]),
        (1, &[0, 1, 2, 1_000]),
        (5, &[4, 5, 6]),
        (1_000, &[999, 1_000, 1_001, Coeff::MAX]),
        (1_001, &[1_000, 1_001, 1_002]),
        (Coeff::MAX, &[0, 1, Coeff::MAX - 1, Coeff::MAX]),
        (
            Coeff::MAX - 1,
            &[Coeff::MAX - 2, Coeff::MAX - 1, Coeff::MAX],
        ),
        // Wide. A capping bug does not have to apply to every constraint: an
        // early return above some width is enough, and one at `> 6` terms
        // survived every test in this crate while stopping SATURATE capping.
        // Randomized widths below reach past that too, but a fixed wide case
        // means the blind spot cannot come back by a change to the generator.
        (
            3,
            &[
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
            ],
        ),
    ];
    for (degree, coeffs) in cases {
        let input = straddling(*degree, coeffs);
        let out = saturate(&input).expect("saturate refused a normalized constraint");
        assert_eq!(
            out.degree, *degree,
            "saturate changed the degree of {input:?}"
        );
        assert_eq!(out.terms.len(), coeffs.len());
        for (term, &coeff) in out.terms.iter().zip(coeffs.iter()) {
            assert_eq!(
                i128::from(term.coeff),
                expected_cap(i128::from(*degree), i128::from(coeff)),
                "saturate at degree {degree} left the coefficient {coeff} as \
                 {}, which is not min(coeff, degree)",
                term.coeff
            );
        }
    }

    // Randomized, so that no future capping bug has to be anticipated by a
    // hand-written case. Non-negative to stay inside the rule's precondition.
    let mut rng = Rng(0xDEAD_BEEF_CAFE_F00D);
    let mut capped_at_least_once = 0usize;
    let mut widest = 0usize;
    for _ in 0..50_000 {
        let degree = (rng.next() % 4_096) as Coeff;
        // Widths reach well past the point where a per-width early return
        // would hide: 1..=32 terms rather than 1..=6.
        let coeffs: Vec<Coeff> = (0..1 + rng.next() % 32)
            .map(|_| (rng.next() % 8_192) as Coeff)
            .collect();
        widest = widest.max(coeffs.len());
        let out = saturate(&straddling(degree, &coeffs)).expect("saturate refused");
        for (term, &coeff) in out.terms.iter().zip(coeffs.iter()) {
            let want = expected_cap(i128::from(degree), i128::from(coeff));
            assert_eq!(i128::from(term.coeff), want);
            if coeff > degree {
                capped_at_least_once += 1;
            }
        }
    }
    // Floors, so that a generator which stopped producing over-degree
    // coefficients -- or stopped producing wide constraints -- would fail here
    // rather than pass vacuously. The width floor is not decoration: an early
    // return at `> 6` terms stopped SATURATE capping and survived every test in
    // this crate, because nothing here was wider than six.
    assert!(
        capped_at_least_once > 10_000,
        "only {capped_at_least_once} coefficients actually exceeded the degree, \
         so this test barely exercised capping at all"
    );
    assert!(
        widest >= 32,
        "the widest constraint tested had {widest} terms; a capping bug that \
         only applies above some width would not be seen"
    );
}

/// The same rule at the complete domain, where the Clean theorems are stated.
///
/// The existing cross-domain differential in `tests/width_guards.rs` compares
/// the two domains against *each other*, which is exactly what attack 3
/// survived: patching both delegations left them agreeing. This compares each
/// against the property.
#[test]
fn saturate_caps_at_the_complete_domain_too() {
    let mut rng = Rng(0x0BAD_F00D_1234_5678);
    let mut capped = 0usize;
    for _ in 0..20_000 {
        let degree = (rng.next() % 4_096) as Coeff;
        let coeffs: Vec<Coeff> = (0..1 + rng.next() % 32)
            .map(|_| (rng.next() % 8_192) as Coeff)
            .collect();
        let big: Constraint<Big> = Constraint::new(
            coeffs
                .iter()
                .enumerate()
                .map(|(i, &coeff)| Term {
                    coeff: Big::from(coeff),
                    lit: Lit::pos(i as u32),
                })
                .collect(),
            Big::from(degree),
        );
        let out = saturate(&big).expect("saturate refused at the complete domain");
        for (term, &coeff) in out.terms.iter().zip(coeffs.iter()) {
            assert_eq!(
                term.coeff,
                Big::from(expected_cap(i128::from(degree), i128::from(coeff)))
            );
            if coeff > degree {
                capped += 1;
            }
        }
    }
    assert!(
        capped > 4_000,
        "only {capped} coefficients exceeded the degree"
    );
}
