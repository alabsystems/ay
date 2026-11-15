//! # `veripb-core-proved` — the soundness-critical kernel of the VeriPB checker
//!
//! Every item in this crate is the Rust image of a definition or theorem in
//! [`clean/veripb_kernel.lean`], which is machine-checked by the Clean kernel
//! (`clean check clean/veripb_kernel.lean` — 912 declarations, 0 failed).
//! The design note is the development design notes.
//!
//! ## The one invariant this crate exists to enforce
//!
//! The proved semantics lives in **unbounded `Int`**. A checker runs on
//! machine values. Those two agree only while nothing overflows, so every
//! value that enters a rule is admitted through a *guard* that re-establishes
//! the mathematical fact in a width that cannot wrap.
//!
//! A wrapped value is never silently used: it fails the guard and the rule
//! refuses to fire. This is the structural fix for VeriPB bug C (the `i64`
//! degree decrement that wraps in `weaken` / variable-form `div` / MIR).
//!
//! ## Two instantiations of one kernel
//!
//! The rules are written **once**, generically over a [`CoeffDomain`]: the
//! type coefficients and degrees are *stored* in, together with the exact
//! arithmetic [`CoeffDomain::Exact`] the rule *computes* in and the guarded
//! narrowing [`CoeffDomain::narrow`] that admits a computed value back into
//! storage. Two domains are instantiated:
//!
//! | domain | storage | exact width | `narrow` | mirrors |
//! |---|---|---|---|---|
//! | [`Coeff`] (`i64`) | one machine word | [`Wide`] (`i128`) | `VeriPbCore.fitsI64` — can fail | the Clean statements *plus* their width side conditions |
//! | [`Big`] (`BigInt`) | arbitrary precision | itself | `Some`, always | the Clean statements **verbatim** |
//!
//! This is the point of the generic form, and it is worth stating plainly:
//! the Clean development is stated over `Int`, so the **`Big` instantiation
//! is the more faithful mirror**, not the less. It discharges no width side
//! condition because the theorems it mirrors have none. The `i64`
//! instantiation is the fast one, and it is exactly where the width guards
//! ([`guard::fits_i64`], [`guard::eq_ok`], mirroring `VeriPbCore.fitsI64` /
//! `eqOkB`) have content: a value must land in a machine word, and the guard
//! is the proof obligation that it did.
//!
//! Because both instantiations run the *same* rule bodies, an audit of a rule
//! is an audit of both. Where the two differ is confined to the two
//! [`CoeffDomain`] impls, which are a few lines each.
//!
//! The live checker promotes its own arithmetic from `i64` to `i128` to
//! `BigInt` as values grow. Before the `Big` instantiation existed, the
//! proved kernel stood down at exactly the widths the live checker had just
//! promoted into — so a wrap above `i64` was an uncounted *skip* rather than
//! a detected divergence. It no longer is: see the development design notes §7.3 and
//! `veripb-checker/src/kernel_bridge.rs`.
//!
//! ### On the one dependency
//!
//! This crate was deliberately dependency-free, and it now has exactly one:
//! `malachite-bigint`, for [`Big`]. That is a deliberate trade and not a
//! loosening. `Big` adds no *algorithm* to the trust surface — the rules,
//! the normalizer and the RUP replay are the same generic code the `i64`
//! instantiation runs — it only supplies an integer type. It is the same type
//! `veripb-formula` already computes the live checker's constraints in, so it
//! is a dependency the checker's answers rested on already, and it introduces
//! no new package into the workspace lockfile. What it buys is that the
//! kernel can mirror the `Int` statements *without* a width hypothesis; what
//! it costs is trusting that `malachite` implements the integers, which is
//! strictly weaker than the alternative of trusting that no value ever
//! exceeds `i64`.
//!
//! ## Map from Rust to Clean
//!
//! | Rust | Clean |
//! |---|---|
//! | [`Lit`], [`Term`], [`Constraint`] | `VeriPbCore.Lit`, `.Term`, `.Constraint` |
//! | [`Constraint::eval`] | `VeriPbCore.evalTerms` |
//! | [`Constraint::holds`] | `VeriPbCore.Holds` |
//! | [`CoeffDomain`], [`Exact`] | the ambient `Int` of the whole development |
//! | [`add`] | `VeriPbCore.entails_add` / `entails_add_checked` |
//! | [`multiply`] | `VeriPbCore.entails_multiply` |
//! | [`divide`] | `VeriPbCore.entails_divide` |
//! | [`mir::mir`], [`mir::mir_variable`] | `VeriPbCore.entails_mir` / `entails_mir_variable` |
//! | [`saturate`] | `VeriPbCore.entails_saturate` |
//! | [`literal_axiom`] | `VeriPbCore.entails_literal` |
//! | [`weaken_degree`] | `VeriPbCore.entails_weaken_checked` |
//! | [`negate`] | `VeriPbCore.entails_of_negation_unsat` |
//! | [`CONTRADICTION_DEGREE`] | `VeriPbCore.contradiction` |
//! | [`guard::fits_i64`] | `VeriPbCore.fitsI64` / `inI64_of_fitsI64` |
//! | [`guard::eq_ok`] | `VeriPbCore.eqOkB` / `eq_of_eqOkB` |
//! | [`cap_coeff`], [`Exact::cap_coeff`] | `VeriPbCore.capCoeff` |
//! | [`normalize::normalize`] | `VeriPbCore.normC` (+ `holds_normC_of_holds` / `holds_of_holds_normC` / `normC_nonneg`) |
//! | [`rup::check_rup`] | `VeriPbCore.PropTrail` / `entails_of_rup` |
//! | [`db::Db`], [`db::Op`] | `VeriPbCore.DbOk` / `DStep` / `checker_sound` |
//! | [`db::formula_satisfied`] | `VeriPbCore.holdsAllB` / `sat_of_witness` |
//!
//! [`clean/veripb_kernel.lean`]: ../../clean/veripb_kernel.lean

#![forbid(unsafe_code)]
#![deny(missing_docs)]

#[cfg(feature = "trust-surface")]
// rustfmt resolves cfg'd modules regardless of the cfg, and stock rustfmt
// could not lex the Clean island (`(fun c' i =>`): without this attribute the
// fmt run aborted on the whole workspace and `--check` exited 1 even on an
// already-formatted tree. trustfmt (1.9.0-trust, measured 2026-09-28) lexes
// the island and leaves it untouched, but would re-lay the hand-written Rust
// after it, so the skip keeps `targo fmt` off this file for now.
#[rustfmt::skip]
pub mod trust_surface;

pub mod db;
pub mod mir;
pub mod normalize;
pub mod rup;
pub mod subst;

/// The **narrow** coefficient domain: coefficients and degrees as the live
/// checker stores them in a machine word, and the default instantiation of
/// every generic item here.
pub type Coeff = i64;

/// Wide arithmetic used *only* inside the [`Coeff`] domain's guards. `i128`
/// holds every product and sum of two `i64` values exactly, so a guard
/// computation cannot itself wrap.
pub type Wide = i128;

/// The **complete** coefficient domain: unbounded integers, i.e. the `Int`
/// the Clean development is stated over, with no width side condition left to
/// discharge.
///
/// This is `veripb-formula`'s own integer type, so a live constraint crosses
/// into this domain without changing representation.
pub type Big = malachite_bigint::BigInt;

/// Decidable guards of the **narrow** ([`Coeff`]) domain. Each is the Rust
/// image of a Clean `Bool`-valued check together with the lemma that lifts it
/// to the corresponding `Prop`.
///
/// These live here, unparameterized, because that is what they are about: a
/// value landing in a machine word. `<Coeff as CoeffDomain>::narrow` is
/// [`narrow`](guard::narrow) itself; the [`Big`] domain has no counterpart
/// because the theorems it mirrors carry no width hypothesis.
pub mod guard {
    use super::{Coeff, Wide};

    /// Mirrors `VeriPbCore.fitsI64` / `VeriPbCore.inI64_of_fitsI64`.
    #[cfg_attr(
        feature = "trust-surface",
        trust::ensures(
            (!result || (x >= -9223372036854775808 && x <= 9223372036854775807))
                && (result || (x < -9223372036854775808 || x > 9223372036854775807))
                by guard_fits_exact
        )
    )]
    pub fn fits_i64(x: Wide) -> bool {
        x >= Wide::from(Coeff::MIN) && x <= Wide::from(Coeff::MAX)
    }

    /// Mirrors `VeriPbCore.eqOkB` / `VeriPbCore.eq_of_eqOkB`.
    ///
    /// `machine` is whatever the fixed-width arithmetic produced; `truth` is
    /// the same quantity recomputed in [`Wide`]. A wrapped `machine` value
    /// cannot pass.
    /// **This function carries a compiler-checked contract on the REAL body.**
    /// The clause says the body IS the island definition `eqOkW`, and the
    /// proof is definitional equality against the E6-admitted body -- no
    /// theorem is needed or applicable, so it is deliberately UNCITED.
    /// (`eq_of_eqOkW` states the value-level consequence, that the two sides
    /// denote the same integer; that lives in Clean and is what
    /// `entails_add_checked` consumes.)
    ///
    /// The cast is a SIGN extension, and the island models it as one
    /// (`sextWide v = ofInt128 (toInt64 v)`, exact on all 2^64 inputs). The
    /// mutation this guards against is comparing the TRUNCATION instead --
    /// `machine == truth as Coeff` -- which is the wrap bug `eq_ok` exists to
    /// catch, and which now turns the build red.
    #[cfg_attr(
        feature = "trust-surface",
        trust::ensures(result == eqOkW(machine, truth))
    )]
    pub fn eq_ok(machine: Coeff, truth: Wide) -> bool {
        Wide::from(machine) == truth
    }

    /// Admit a wide value as a machine coefficient, or fail closed.
    ///
    /// **This function carries a compiler-checked contract on the REAL body** —
    /// not on a twin. Under `--cfg feature="trust-surface"` compiler_consumer admits this
    /// body through its GuardedNarrow lane, mints the `x as Coeff` cast as
    /// what it is (two's-complement truncation, unconditionally), and requires
    /// the island theorem `narrowWide_isSome_of_fits` to prove the clause: a
    /// value the guard accepts is never rejected. Stock rustc never sees the
    /// attribute, so the crate builds unchanged without the toolchain.
    ///
    /// Both callees are module-qualified deliberately. Bare `narrow` is owned
    /// by three items in this crate (this one and two `CoeffDomain` impls), so
    /// it is genuinely ambiguous and stays fail-closed; `guard::narrow` names
    /// exactly one. Qualifying `fits_i64` too — though it is unique today —
    /// keeps the contract robust against a future collision.
    #[cfg_attr(
        feature = "trust-surface",
        trust::ensures(
            guard::fits_i64(x) ==> guard::narrow(x) != None by narrowWide_isSome_of_fits
        )
    )]
    pub fn narrow(x: Wide) -> Option<Coeff> {
        if fits_i64(x) { Some(x as Coeff) } else { None }
    }
}

// ---------------------------------------------------------------------------
// The exact-arithmetic leaves.
//
// The rules themselves are generic, `Vec`-carrying, loop-carrying bodies that
// no admission fragment reaches — that is measured and settled. What CAN carry
// a compiler-checked contract is the concrete-typed *scalar decision* each
// rule makes, and these three are the arithmetic ones: the sum, the difference
// and the product a rule forms in [`Wide`] before [`guard::narrow`] admits the
// result back into storage.
//
// They are not twins. `<Wide as Exact>::checked_add` / `checked_sub` /
// `checked_mul` are one-line delegations to exactly these functions, and every
// rule below computes through those methods — so at the [`Coeff`] domain the
// bodies the checker runs ARE these bodies.
//
// WHAT THE CONTRACTS DO NOT SAY. Each clause is a *totality* statement:
// arguments already known to fit in `i64` never make the operation refuse.
// It says nothing about the value returned, and — this matters — the theorem
// it cites lives in the kernel's machine layer (`BitVec 128`, `guardFitsW`,
// `checkedAdd128`), which is NOT yet joined to the rule layer
// (`entails_add_checked` and friends, stated over unbounded `Int` with
// `fitsI64` / `eqOkB`). So a green citation here is a proved fact about the
// machine operation, not a discharge of the rule theorem's hypothesis.
// ---------------------------------------------------------------------------

/// **Overflow-checked wide addition** — the sum every rule's degree
/// arithmetic forms before narrowing, at the width it forms it in.
///
/// **This function carries a compiler-checked contract on the REAL body** —
/// the body `<Wide as Exact>::checked_add` calls, which is the body [`add`],
/// [`negate`], [`weaken_degree`], [`divide_with`] and both [`mir`] entry
/// points reach. compiler_consumer admits it through the `CheckedArithmetic` lane and
/// requires `checkedAdd128_isSome_of_inI64` to prove the clause.
///
/// The clause: two operands that pass [`guard::fits_i64`] can never make the
/// addition refuse. That is the *non-degeneracy* half of the guard story — the
/// half that says the rule does not fail closed on inputs it is supposed to
/// accept. The complementary half (a sum that does NOT fit is refused rather
/// than wrapped) is what `checked_add` is for structurally, and is stated but
/// not yet citable (`checkedAdd128_some` / `_none`; see the staging note on
/// [`trust_surface::cadd_wide`](crate::trust_surface)).
#[cfg_attr(
    feature = "trust-surface",
    trust::ensures(
        guard::fits_i64(a) ==> guard::fits_i64(b) ==> add_degree_wide(a, b) != None
            by checkedAdd128_isSome_of_inI64
    )
)]
pub fn add_degree_wide(a: Wide, b: Wide) -> Option<Wide> {
    a.checked_add(b)
}

/// **Overflow-checked wide subtraction** — the decrement at the site of VeriPB
/// bug C, as a concrete-typed leaf.
///
/// **This function carries a compiler-checked contract on the REAL body** —
/// the body `<Wide as Exact>::checked_sub` calls, which is the body
/// [`weaken_degree`] runs on the very subtraction the upstream defect wrapped.
/// The citation is `checkedSub128_isSome_of_inI64`.
///
/// `i64::MIN - 1` is the value bug C loses: at `i64` it wraps to `i64::MAX` and
/// passes every upper bound. Here the difference is formed at `i128`, where
/// `checked_sub` cannot wrap at all, and the clause says the operation never
/// refuses a difference of two `i64`-representable operands — so the only
/// thing that can reject `i64::MIN - 1` downstream is [`guard::narrow`],
/// which is exactly where the rejection belongs.
#[cfg_attr(
    feature = "trust-surface",
    trust::ensures(
        guard::fits_i64(a) ==> guard::fits_i64(b) ==> sub_degree_wide(a, b) != None
            by checkedSub128_isSome_of_inI64
    )
)]
pub fn sub_degree_wide(a: Wide, b: Wide) -> Option<Wide> {
    a.checked_sub(b)
}

/// **Overflow-checked wide multiplication** — MULTIPLY's scaling, DIVIDE's
/// quotient re-check and MIR's cut arithmetic, as a concrete-typed leaf.
///
/// **This function carries a compiler-checked contract on the REAL body** —
/// the body `<Wide as Exact>::checked_mul` calls, which is the body
/// [`multiply`], [`divide_with`]'s two ceiling bounds and
/// [`mir::mir_f`](crate::mir::mir_f) all reach. The citation is
/// `checkedMul128_isSome_of_inI64`.
///
/// Note what the hypothesis buys and what it does not: MULTIPLY's factor and
/// coefficient are both stored `i64`, so the clause applies there and says the
/// scaling never spuriously refuses. [`divide_with`] multiplies by an
/// *arbitrary* quotient, which need not fit `i64` — the clause is silent on
/// that call, and the `None` branch is precisely the fail-closed behaviour
/// that case wants.
#[cfg_attr(
    feature = "trust-surface",
    trust::ensures(
        guard::fits_i64(a) ==> guard::fits_i64(b) ==> mul_coeff_wide(a, b) != None
            by checkedMul128_isSome_of_inI64
    )
)]
pub fn mul_coeff_wide(a: Wide, b: Wide) -> Option<Wide> {
    a.checked_mul(b)
}

/// **The sign side condition every scaling rule is gated on**, as a
/// concrete-typed leaf.
///
/// **This function carries a compiler-checked contract on the REAL body** —
/// the body `<Coeff as CoeffDomain>::is_nonneg` calls, which is the body
/// [`multiply`], [`divide_with`], [`weaken_degree`],
/// [`mir::mir`](crate::mir::mir), [`mir::mir_variable`](crate::mir::mir_variable)
/// and [`Constraint::all_nonneg`] all reach at the narrow domain. The citation
/// is `weaken_factor_sign_exact`.
///
/// The clause is a **complete characterisation** of the test, not a one-way
/// implication:
///
/// * `!result || w >= 0` — the test never accepts a negative factor. This is
///   the direction `entails_weaken_checked` / `entails_multiply` consume
///   (`Int.le 0 _`); a negative factor makes WEAKEN *raise* a degree, which
///   strengthens a constraint the premise never entailed.
/// * `result || w < 0` — and never rejects a non-negative one, so the test
///   cannot be satisfied by a constant `false`.
///
/// Each conjunct alone is satisfied by a wrong body (`w >= 1` never accepts a
/// negative factor either); only the two together force the comparison to
/// change sense at exactly zero.
///
/// MULTIPLY and DIVIDE need `k > 0`, which is strictly stronger than what this
/// decides; they spell it as this test *and* a separate `k != 0`, so the sign
/// half — the half a kernel theorem is cited about — is the one that runs
/// here. The `!= 0` half carries no width or sign subtlety and is not cited.
#[cfg_attr(
    feature = "trust-surface",
    trust::ensures(
        (!result || w >= 0) && (result || w < 0) by weaken_factor_sign_exact
    )
)]
pub fn factor_nonneg(w: Coeff) -> bool {
    w >= 0
}
/// **A rule's output constraint, at the stored width.**
///
/// The degree twin of [`weaken_apply`], and the same tier: it says the
/// constraint a rule hands back carries the degree that rule's guarded
/// arithmetic computed. ADD, MULTIPLY, DIVIDE, SATURATE, NEGATE and both
/// MIR forms all package their result through it, so on the `Coeff` width
/// every one of them has a compiler-checked output degree. It says NOTHING about the terms -- a clause naming a `Vec`,
/// even only its length, comes back `unknown` -- so `terms == c1.terms ++
/// c2.terms` remains carried by the pinned-source tests.
///
/// The terms arrive already built, which is not cosmetic. Measured on the
/// three constructions, contracting the same clause:
///
/// | body                                    | obligations             |
/// |-----------------------------------------|-------------------------|
/// | `with_capacity` + 2x `extend_from_slice` | 2 proved, 4 FAILED, 15 unknown |
/// | `clone` + `extend_from_slice`            | 2 proved, 1 FAILED,  8 unknown |
/// | `[a, b].concat()`                        | 2 proved, 0 failed,  1 unknown |
/// | terms supplied by the caller             | 2 proved, 0 failed,  0 unknown |
///
/// So the allocation tail is where ADD's unproved obligations live, and
/// keeping it out of the contracted body is what makes this leaf clean.
/// `add` itself now builds the terms with `concat`, which alone removes
/// four failing and fourteen unknown obligations from the crate.
///
/// Concrete at `Coeff` deliberately -- see [`weaken_apply`] for why a
/// generic body would make this contract silently inert.
#[cfg_attr(feature = "trust-surface",
    trust::ensures(move |ret: &Constraint<Coeff>| ret.degree == d))]
pub fn pack_constraint(terms: Vec<Term<Coeff>>, d: Coeff) -> Constraint<Coeff> {
    Constraint { terms, degree: d }
}

/// **WEAKEN's output constraint, at the stored width.**
///
/// The first contract in this crate on a function returning a `Constraint`
/// rather than a scalar. It says the constraint WEAKEN hands back carries
/// the degree the guarded arithmetic computed -- the degree half of
/// `VeriPbCore.weakenC r c = { terms := c.terms, degree := r }`.
///
/// Three things it is NOT, because the shape invites over-reading:
///
/// * It says NOTHING about the terms. `ret.terms == c.terms` is not
///   expressible: measured, a clause mentioning a `Vec` -- even only its
///   length -- comes back `unknown`. The terms half of `weakenC` stays
///   unverified, carried by the pinned-source tests as before.
/// * It is NATIVE-VERIFIED, not kernel-cited: the same tier as the
///   `zero`/`one` constants (see `UNCITED_NATIVE_ONLY`). One of its two
///   obligations is re-checked by the clean CIC kernel; the authored clause
///   is discharged by compiler_consumer's own verifier. It does NOT discharge a
///   hypothesis of `entails_weaken_from_guards`, which lives in the kernel.
/// * It is CONCRETE at `Coeff` DELIBERATELY. Measured: the same body
///   generic over `C` reports `0 proved, 0 failed, 0 unknown out of 0
///   obligation(s)` -- an INERT contract, and silently so. Extraction is
///   pre-monomorphization, so a generic body has no concrete type to verify
///   against and the clause quietly does nothing rather than failing. Do
///   not "simplify" this back to a generic.
///
/// The clause uses the CLOSURE form. The signature form
/// `ensures(result.degree == r)` is refused outright ("unsupported contract
/// predicate expression"); only the closure form can bind a projection off
/// an aggregate result.
#[cfg_attr(feature = "trust-surface",
    trust::ensures(move |ret: &Constraint<Coeff>| ret.degree == r))]
pub fn weaken_apply(c: &Constraint<Coeff>, r: Coeff) -> Constraint<Coeff> {
    Constraint {
        terms: c.terms.clone(),
        degree: r,
    }
}

/// **The sign test at the EXACT-ARITHMETIC width**, as a concrete-typed leaf.
///
/// **This function carries a compiler-checked contract on the REAL body** —
/// the body `<Wide as Exact>::is_nonneg` calls, and therefore the body behind
/// every `is_negative()` the rules run at the narrow domain:
/// [`mir::mir`](crate::mir::mir)'s `mirF_nonneg` re-check on the coefficient
/// it just produced, [`mir`](crate::mir)'s `intFloorMod_nonneg` re-check on
/// the remainder, and [`normalize`](crate::normalize)'s flip/drop test. The
/// citation is `wide_sign_exact`.
///
/// [`factor_nonneg`] is the same test at the *stored* width, and is not a
/// substitute: these decisions are taken on values that live only inside the
/// guard arithmetic — a floor-remainder, a `mirF` image — which have not been
/// narrowed and need not fit `i64` at all. A contract about them has to be
/// stated at `i128`, which is what `wide_sign_exact` (`decide_le_exact` at the
/// `key128` sign-flip order key) says.
///
/// The clause is a **complete characterisation**, both directions, for the
/// same reason as [`factor_nonneg`]'s: `!result || x >= 0` alone is satisfied
/// by `x >= 1`, and `result || x < 0` alone by `x >= -1`; only the pair forces
/// the comparison to change sense at exactly zero.

#[cfg_attr(
    feature = "trust-surface",
    trust::ensures(
        (!result || x >= 0) && (result || x < 0) by wide_sign_exact
    )
)]
pub fn wide_nonneg(x: Wide) -> bool {
    x >= 0
}

/// **A two-operand order test at the exact-arithmetic width**, as a
/// concrete-typed leaf.
///
/// **This function carries a compiler-checked contract on the REAL body** —
/// the body `<Wide as Exact>::at_least` calls, which is the body behind
/// [`divide_with`]'s two ceiling bounds (`x <= k*q` and `k*q < x + k`, the
/// `intCeilDiv_ub` / `intCeilDiv_min` re-checks that reject a quotient which
/// is not *the* ceiling) and [`mir`](crate::mir)'s `intFloorMod_lt` order test
/// `r < k`. The citation is `wide_le_exact`.
///
/// Unlike [`wide_nonneg`] this compares two *computed* values rather than one
/// value against zero, which is why it needs its own theorem: the mint is
/// `Nat.le (key128 b) (key128 a)` — the operands swap, `a >= b` being `b <= a`
/// — and the citation lane matches a theorem's statement against the goal
/// rather than instantiating a general lemma at it.
///
/// The clause is a **complete characterisation**, both directions. That
/// matters more here than anywhere else in this file, because both call sites
/// use *both* directions: [`divide_with`] accepts on `prod >= x` and on
/// `!(prod >= bound)`, so a one-sided contract would leave the strict half of
/// the ceiling test — the half that rules out an *overshooting* quotient, the
/// shape of upstream defect 4 — uncovered.
#[cfg_attr(
    feature = "trust-surface",
    trust::ensures(
        (!result || a >= b) && (result || a < b) by wide_le_exact
    )
)]
pub fn wide_at_least(a: Wide, b: Wide) -> bool {
    a >= b
}

/// The sealing supertrait for [`Exact`] and [`CoeffDomain`].
///
/// Private, and deliberately so: it makes the two traits IMPLEMENTABLE ONLY
/// IN THIS CRATE. That is not API tidiness, it is what makes the crate's
/// central verification claim true rather than assumed.
///
/// Every proved rule here is generic over `C: CoeffDomain`, and its
/// panic-freedom is a statement about `C::add`, `C::narrow` and the rest. For
/// an OPEN trait that statement is quantified over impls that do not exist
/// yet, including a downstream `impl CoeffDomain` whose `add` panics -- so the
/// verifier is right to refuse it, and refusing it is the honest answer. The
/// closed-world premise cannot be asserted; it has to be made true. Sealing
/// makes it true: the set of coefficient domains is exactly `Coeff` and
/// `Big`, both in this file, both verified.
///
/// Nothing is lost. The coefficient domain is not an extension point -- it is
/// the choice between "the width the live checker stores" and "the width the
/// Clean theorems are stated at", and a third answer would need its own
/// theorems, not just its own impl.
mod sealed {
    /// Implemented, in this crate only, by the two coefficient domains and
    /// the two exact widths.
    pub trait Sealed {}
}

impl sealed::Sealed for Coeff {}
impl sealed::Sealed for Wide {}
impl sealed::Sealed for Big {}

/// Exact integer arithmetic: the width a rule *computes* in, chosen so that
/// no intermediate of that rule can wrap.
///
/// Every method here is the image of an `Int` operation of the Clean
/// development (`Int.add`, `Int.sub`, `Int.mul`, `Int.neg`, `intFloorDiv`,
/// `intFloorMod`, `capCoeff`), and both implementations compute it exactly on
/// every input the rules admit — that is the whole contract. [`Wide`]
/// (`i128`) is exact for the [`Coeff`] domain because the largest quantity
/// any rule forms there is a product or a bounded sum of `i64` values;
/// [`Big`] is exact unconditionally.
pub trait Exact: sealed::Sealed + Clone + core::fmt::Debug + Eq + Ord + Sized {
    /// `0`.
    fn zero() -> Self;

    /// `1`.
    fn one() -> Self;

    /// `Int.add`.
    fn add(&self, rhs: &Self) -> Self;

    /// `Int.sub`.
    fn sub(&self, rhs: &Self) -> Self;

    /// `Int.mul`.
    fn mul(&self, rhs: &Self) -> Self;

    /// `Int.neg`.
    fn neg(&self) -> Self;

    /// `Int.add`, refusing rather than wrapping.
    ///
    /// A sum this width cannot hold is not a value any Clean theorem talks
    /// about, so the only correct answer is `None`. Unbounded implementations
    /// always return `Some`.
    ///
    /// At [`Wide`] this is [`add_degree_wide`], the concrete-typed leaf that
    /// carries the compiler-checked contract — so every rule that adds through
    /// this method runs a body a kernel theorem is cited about.
    fn checked_add(&self, rhs: &Self) -> Option<Self>;

    /// `Int.sub`, refusing rather than wrapping. At [`Wide`] this is
    /// [`sub_degree_wide`]; see [`Exact::checked_add`].
    fn checked_sub(&self, rhs: &Self) -> Option<Self>;

    /// `Int.mul`, refusing rather than wrapping.
    ///
    /// A product this width cannot hold is not a value any Clean theorem
    /// talks about, so the only correct answer is `None`. Unbounded
    /// implementations always return `Some`.
    ///
    /// At [`Wide`] this is [`mul_coeff_wide`]; see [`Exact::checked_add`].
    fn checked_mul(&self, rhs: &Self) -> Option<Self>;

    /// Floor division and its remainder in one step, for a **strictly
    /// positive** divisor: `(intFloorDiv self k, intFloorMod self k)`.
    ///
    /// Returning the pair matters: `intFloorMod` is defined as
    /// `self - k * intFloorDiv self k`, so computing the two together is what
    /// makes the division witness `q * k + m = x` — which [`mir`] re-checks —
    /// an identity of the same division rather than of two.
    ///
    /// Behaviour for `k <= 0` is unspecified; every caller checks the sign
    /// first (it is the `hk` hypothesis of the theorems that use it).
    fn div_mod_floor(&self, k: &Self) -> (Self, Self);

    /// Sum of an iterator, `Int.add`-folded from zero.
    fn sum<I: Iterator<Item = Self>>(items: I) -> Self {
        items.fold(Self::zero(), |acc, x| acc.add(&x))
    }

    /// `Int.le 0 self` — the sign side condition, at the width the rules
    /// *compute* in rather than the width they store in.
    ///
    /// At [`Wide`] this is [`wide_nonneg`], the concrete-typed leaf that
    /// carries the compiler-checked contract — so every rule that tests a sign
    /// inside the guard arithmetic runs a body a kernel theorem is cited
    /// about. At [`Big`] it is the same comparison against an unbounded zero,
    /// with nothing to discharge.
    fn is_nonneg(&self) -> bool {
        *self >= Self::zero()
    }

    /// `Int.le rhs self` — the two-operand order test, at the exact width.
    ///
    /// At [`Wide`] this is [`wide_at_least`]; see [`Exact::is_nonneg`].
    fn at_least(&self, rhs: &Self) -> bool {
        *self >= *rhs
    }

    /// `Int.lt self 0`.
    ///
    /// Spelled as the negation of [`Exact::is_nonneg`] rather than as its own
    /// comparison: `<` and `>=` are complementary on a total order, so this
    /// way the decision is taken by the *contracted* comparison, and
    /// `wide_sign_exact`'s second conjunct (`result || x < 0` — the test never
    /// rejects a non-negative value) is exactly the direction this reading
    /// needs.
    fn is_negative(&self) -> bool {
        !self.is_nonneg()
    }

    /// `Int.lt 0 self`.
    ///
    /// Spelled `1 <= self`, which over the integers is the same test — and is
    /// the spelling [`Exact::at_least`] carries a contract about. There is no
    /// strict-comparison theorem at this width to cite, and inventing a third
    /// leaf for `> 0` would state something the two existing ones already
    /// decide.
    fn is_positive(&self) -> bool {
        self.at_least(&Self::one())
    }

    /// `VeriPbCore.capCoeff` at this width — see [`cap_coeff`], the machine
    /// twin that carries the compiler-checked contract.
    fn cap_coeff(degree: &Self, coeff: &Self) -> Self;
}

/// A coefficient domain the proved rules are instantiated at: where values
/// are **stored**, plus the [`Exact`] width they are **computed** in and the
/// guarded narrowing between the two.
///
/// [`narrow`](CoeffDomain::narrow) *is* the width guard. For [`Coeff`] it is
/// `VeriPbCore.fitsI64` and it can fail, which is what makes a rule refuse to
/// fire rather than store a wrapped value. For [`Big`] it is `Some`, always,
/// because the Clean theorems being mirrored have no width hypothesis at all.
pub trait CoeffDomain: sealed::Sealed + Clone + core::fmt::Debug + Eq + Ord + Sized {
    /// The width this domain's rules compute in.
    type Exact: Exact;

    /// How this domain is named in diagnostics.
    const NAME: &'static str;

    /// `0`.
    fn zero() -> Self;

    /// `1`.
    fn one() -> Self;

    /// Lift a stored value into the exact width. Always total.
    fn widen(&self) -> Self::Exact;

    /// **The width guard.** Admit an exactly-computed value back into
    /// storage, or fail closed.
    fn narrow(x: &Self::Exact) -> Option<Self>;

    /// Build WEAKEN's output constraint: the terms unchanged, the degree
    /// replaced by the guarded value. `VeriPbCore.weakenC`.
    ///
    /// A trait method so the `Coeff` impl can route it through the
    /// CONTRACTED [`weaken_apply`]. The default body is the same
    /// computation for the domains whose width has no contract.
    fn apply_weaken(c: &Constraint<Self>, r: Self) -> Constraint<Self> {
        Constraint {
            terms: c.terms.clone(),
            degree: r,
        }
    }

    /// SATURATE's per-term step. A trait method so the `Coeff` impl can route
    /// it through the CONTRACTED [`sat_term`], whose clause pins the built
    /// term's coefficient to at most the degree.
    fn sat_term(degree: &Self, coeff: &Self, lit: Lit) -> Term<Self> {
        Term {
            coeff: Self::cap_coeff(degree, coeff),
            lit,
        }
    }

    /// Package a rule's already-built terms with its guarded degree. A
    /// trait method so the `Coeff` impl can route it through the CONTRACTED
    /// [`pack_constraint`].
    fn pack(terms: Vec<Term<Self>>, d: Self) -> Constraint<Self> {
        Constraint { terms, degree: d }
    }

    /// `VeriPbCore.capCoeff` on stored values. `<=` is the same order at
    /// every width, so this agrees with [`Exact::cap_coeff`] on every value
    /// both can hold.
    fn cap_coeff(degree: &Self, coeff: &Self) -> Self;

    /// **The sign side condition**, `Int.le 0 x`.
    ///
    /// Every rule that scales, weakens or saturates is gated on it, and at
    /// [`Coeff`] this is [`factor_nonneg`] — the concrete-typed leaf that
    /// carries the compiler-checked contract. At [`Big`] it is the same
    /// comparison against an unbounded zero, with nothing to discharge.
    fn is_nonneg(x: &Self) -> bool;

    /// **The value-preservation guard**, `VeriPbCore.eqOkB truth stored`: the
    /// value admitted into storage denotes the exact value it was computed
    /// from.
    ///
    /// At [`Coeff`] this is [`guard::eq_ok`], which carries a compiler-checked
    /// contract saying its body IS the island's `eqOkW` — a *sign-extending*
    /// comparison, so a wrapped `stored` cannot pass. At [`Big`] storage and
    /// the exact width are the same `Int` and the test is plain equality.
    fn eq_ok(stored: &Self, truth: &Self::Exact) -> bool;
}

// ORDER-SENSITIVE, AND NOT FOR STYLE. This impl block must stay ABOVE
// `impl Exact for Wide`, and the reason is a measured property of compiler_consumer's
// verification walk rather than anything about Rust.
//
// The E9 in-walk citation discharge — the soundness-critical lane, the one
// that actually grades an obligation — resolves a clause's program-function
// calls against the facet table AS ACCUMULATED SO FAR. Bodies are walked
// callee-first in impl-block order, so `guard::fits_i64` is recorded only when
// the first caller that reaches it is walked, and that caller is
// `<Coeff as CoeffDomain>::narrow` right here.
//
// The three arithmetic leaves' clauses have `guard::fits_i64(_)` as their
// hypothesis. With this block below `impl Exact for Wide`, the leaves are
// pulled in (as `<Wide as Exact>::checked_add`'s callees) BEFORE
// `guard::fits_i64` has a facet record, and the discharge fails closed with
// "no diagnostic E6 facet record exists for `guard::fits_i64`".
//
// The failure is SILENT in the two places one would look. compiler_consumer still exits
// 0, and it still prints `note: citation ... kernel-discharges this
// postcondition` for each leaf — that note comes from the E9 *sweep*, which
// runs after every body is walked and is explicitly diagnostic-only ("the
// exact sealed criterion is independently rechecked in-walk and installs
// authority only for an exact matching result row"). The only evidence that
// tells the two apart is the per-function verdict line: `2 proved, 0 failed,
// 0 unknown` versus `0 proved, 0 failed, 2 unknown`.
//
// Measured 2026-08-26. `scripts/verify-proofs.sh` gates the difference through
// `wholecrate_proved_floor` (98), which drops by 6 if this block moves back
// down — so the regression is caught, but the diagnostic will not name the
// cause. This comment is the diagnostic.
impl CoeffDomain for Coeff {
    type Exact = Wide;
    const NAME: &'static str = "i64";

    /// Routed through the contracted leaf, so WEAKEN's output degree on the
    /// width the checker actually runs is compiler-checked.
    #[inline]
    fn apply_weaken(c: &Constraint<Self>, r: Self) -> Constraint<Self> {
        weaken_apply(c, r)
    }

    /// Routed through the contracted leaf [`sat_term`].
    #[inline]
    fn sat_term(degree: &Self, coeff: &Self, lit: Lit) -> Term<Self> {
        sat_term(*degree, *coeff, lit)
    }

    /// Routed through the contracted leaf.
    #[inline]
    fn pack(terms: Vec<Term<Self>>, d: Self) -> Constraint<Self> {
        pack_constraint(terms, d)
    }

    // Contracted, but ONE TIER BELOW every other contract in this crate:
    // `result == 0` names no island definition, and the uncited
    // definitional-equality route declines any clause that names none
    // ("NO-ISLAND-CALL ... uncited defeq route declines the whole
    // function"), so 1 of the 2 obligations reaches Certified and the
    // authored clause reaches Trusted/Deductive rather than
    // downstream proof consumer-citation. Reaching the incumbents' tier would need a
    // clause of the form `result == <island def>(..)`, and no island
    // definition of the right nullary carrier exists. Kept because the
    // check is live: perturbing either body to a wrong constant gives
    // `0 proved, 2 failed` with `verified_counterexample = true`.
    #[cfg_attr(feature = "trust-surface", trust::ensures(result == 0))]
    #[inline]
    fn zero() -> Self {
        0
    }
    #[cfg_attr(feature = "trust-surface", trust::ensures(result == 1))]
    #[inline]
    fn one() -> Self {
        1
    }
    #[inline]
    fn widen(&self) -> Wide {
        Wide::from(*self)
    }
    /// `VeriPbCore.fitsI64` — the guard with content.
    #[inline]
    fn narrow(x: &Wide) -> Option<Self> {
        guard::narrow(*x)
    }
    /// Delegates to [`cap_coeff`] itself. (That comment once read "the one
    /// function of this crate that carries a compiler-checked `ensures`
    /// contract" — it is no longer alone: [`guard::narrow`] carries one too,
    /// and unlike the `cap_coeff` twins the contract sits on the real body.)
    #[inline]
    fn cap_coeff(degree: &Self, coeff: &Self) -> Self {
        cap_coeff(*degree, *coeff)
    }
    /// Delegates to [`factor_nonneg`], the leaf carrying
    /// `weaken_factor_sign_exact`.
    #[inline]
    fn is_nonneg(x: &Self) -> bool {
        factor_nonneg(*x)
    }
    /// Delegates to [`guard::eq_ok`], the leaf whose contract says its body IS
    /// the island's `eqOkW`.
    #[inline]
    fn eq_ok(stored: &Self, truth: &Wide) -> bool {
        guard::eq_ok(*stored, *truth)
    }
}

impl Exact for Wide {
    // Contracted, but ONE TIER BELOW every other contract in this crate:
    // `result == 0` names no island definition, and the uncited
    // definitional-equality route declines any clause that names none
    // ("NO-ISLAND-CALL ... uncited defeq route declines the whole
    // function"), so 1 of the 2 obligations reaches Certified and the
    // authored clause reaches Trusted/Deductive rather than
    // downstream proof consumer-citation. Reaching the incumbents' tier would need a
    // clause of the form `result == <island def>(..)`, and no island
    // definition of the right nullary carrier exists. Kept because the
    // check is live: perturbing either body to a wrong constant gives
    // `0 proved, 2 failed` with `verified_counterexample = true`.
    #[cfg_attr(feature = "trust-surface", trust::ensures(result == 0))]
    #[inline]
    fn zero() -> Self {
        0
    }
    #[cfg_attr(feature = "trust-surface", trust::ensures(result == 1))]
    #[inline]
    fn one() -> Self {
        1
    }
    #[inline]
    fn add(&self, rhs: &Self) -> Self {
        self + rhs
    }
    #[inline]
    fn sub(&self, rhs: &Self) -> Self {
        self - rhs
    }
    #[inline]
    fn mul(&self, rhs: &Self) -> Self {
        self * rhs
    }
    #[inline]
    fn neg(&self) -> Self {
        -self
    }
    #[inline]
    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        add_degree_wide(*self, *rhs)
    }
    #[inline]
    fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        sub_degree_wide(*self, *rhs)
    }
    #[inline]
    fn checked_mul(&self, rhs: &Self) -> Option<Self> {
        mul_coeff_wide(*self, *rhs)
    }
    /// Delegates to [`wide_nonneg`], the leaf carrying `wide_sign_exact`.
    /// `is_negative` is its negation, so both of [`mir`](crate::mir)'s sign
    /// re-checks run this body.
    #[inline]
    fn is_nonneg(&self) -> bool {
        wide_nonneg(*self)
    }
    /// Delegates to [`wide_at_least`], the leaf carrying `wide_le_exact`.
    /// `is_positive` is this test against `1`, so MIR's zero-remainder check
    /// runs this body too.
    #[inline]
    fn at_least(&self, rhs: &Self) -> bool {
        wide_at_least(*self, *rhs)
    }
    /// For a positive divisor, Euclidean and floor division coincide (both
    /// round towards negative infinity) and the Euclidean remainder is the
    /// floor remainder, so the two `div_euclid`/`rem_euclid` intrinsics are
    /// exactly `intFloorDiv` / `intFloorMod` here.
    #[inline]
    fn div_mod_floor(&self, k: &Self) -> (Self, Self) {
        debug_assert!(*k > 0);
        (self.div_euclid(*k), self.rem_euclid(*k))
    }
    #[inline]
    fn cap_coeff(degree: &Self, coeff: &Self) -> Self {
        cap_coeff_wide(*degree, *coeff)
    }
}

impl Exact for Big {
    #[inline]
    fn zero() -> Self {
        Big::from(0)
    }
    #[inline]
    fn one() -> Self {
        Big::from(1)
    }
    #[inline]
    fn add(&self, rhs: &Self) -> Self {
        self + rhs
    }
    #[inline]
    fn sub(&self, rhs: &Self) -> Self {
        self - rhs
    }
    #[inline]
    fn mul(&self, rhs: &Self) -> Self {
        self * rhs
    }
    #[inline]
    fn neg(&self) -> Self {
        -self
    }
    /// Unbounded: a sum always exists.
    #[inline]
    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        Some(self + rhs)
    }
    /// Unbounded: a difference always exists.
    #[inline]
    fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        Some(self - rhs)
    }
    /// Unbounded: a product always exists.
    #[inline]
    fn checked_mul(&self, rhs: &Self) -> Option<Self> {
        Some(self * rhs)
    }
    /// `/` and `%` on `BigInt` truncate towards zero, so the quotient is
    /// decremented (and the remainder shifted up by the divisor) exactly when
    /// the truncated remainder is negative — which for a positive divisor is
    /// the floor division `intFloorDiv` and the nonnegative `intFloorMod`.
    #[inline]
    fn div_mod_floor(&self, k: &Self) -> (Self, Self) {
        let zero = Big::from(0);
        debug_assert!(*k > zero);
        let q = self / k;
        let r = self - &q * k;
        if r < zero {
            (q - Big::from(1), r + k)
        } else {
            (q, r)
        }
    }
    #[inline]
    fn cap_coeff(degree: &Self, coeff: &Self) -> Self {
        if coeff <= degree {
            coeff.clone()
        } else {
            degree.clone()
        }
    }
}

impl CoeffDomain for Big {
    type Exact = Big;
    const NAME: &'static str = "bigint";

    #[inline]
    fn zero() -> Self {
        <Big as Exact>::zero()
    }
    #[inline]
    fn one() -> Self {
        <Big as Exact>::one()
    }
    #[inline]
    fn widen(&self) -> Big {
        self.clone()
    }
    /// Vacuous: storage and exact width are the same `Int`, so there is no
    /// width side condition to discharge — which is precisely why this
    /// instantiation mirrors the Clean statements verbatim.
    #[inline]
    fn narrow(x: &Big) -> Option<Self> {
        Some(x.clone())
    }
    #[inline]
    fn cap_coeff(degree: &Self, coeff: &Self) -> Self {
        <Big as Exact>::cap_coeff(degree, coeff)
    }
    /// The same comparison against an unbounded zero: a sign test has content
    /// at every width, unlike the width guards.
    #[inline]
    fn is_nonneg(x: &Self) -> bool {
        *x >= <Big as Exact>::zero()
    }
    /// Vacuous in the same way [`CoeffDomain::narrow`] is: storage and the
    /// exact width are the same `Int`, so nothing can have wrapped.
    #[inline]
    fn eq_ok(stored: &Self, truth: &Big) -> bool {
        stored == truth
    }
}

/// A pseudo-Boolean literal. Mirrors `VeriPbCore.Lit`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct Lit {
    /// Variable index.
    pub var: u32,
    /// Whether the literal is the negation of the variable.
    pub negated: bool,
}

impl Lit {
    /// A positive literal.
    #[cfg_attr(
        feature = "trust-surface",
        trust::ensures(result.var == var by litctor_var_preserved)
    )]
    pub const fn pos(var: u32) -> Self {
        Lit {
            var,
            negated: false,
        }
    }

    /// A negative literal.
    #[cfg_attr(
        feature = "trust-surface",
        trust::ensures(result.var == var by litctor_var_preserved)
    )]
    pub const fn neg(var: u32) -> Self {
        Lit { var, negated: true }
    }

    /// Mirrors `VeriPbCore.negLit`.
    /// The clause is the half that matters: negation flips the SIGN and must
    /// never change the variable. A `negate` that rewrote `var` would silently
    /// change which literal a rule is about, and every count in this crate
    /// would agree nothing was wrong.
    // Citable signature form, like its neighbours -- but it took two
    // recognizer fixes to get there, and the reason is worth keeping.
    //
    // `result.var` denotes this function's own output only once the per-field
    // import is MINTED for it. `pos`/`neg` are a bare `bb0[_0=aggregate|ret]`
    // and always minted. `negate` computes `!self.negated` first, so its shape
    // is `bb0[_2=use,_4=use,_3=unop,_0=aggregate|ret]`, and it failed TWICE
    // over: the aggregate was not the block's sole effectful statement, so the
    // body was not recognized at all; and once it was, its `var` field is a
    // FieldProjection of a STRUCT parameter, which the field mint skipped
    // because it only knew how to place a whole scalar parameter.
    //
    // Both are fixed in the fork. While they were not, `result.var` lowered as
    // a FREE VARIABLE and the citation audit demanded a theorem of the shape
    // `forall x y : UInt32, x = y` -- false, so nothing honest could be cited.
    // That is the failure mode to recognize if this ever regresses: an
    // impossible demanded shape means the mint is missing, not that the
    // property is wrong.
    #[cfg_attr(
        feature = "trust-surface",
        trust::ensures(result.var == self.var by litnegate_var_preserved)
    )]
    pub const fn negate(self) -> Self {
        Lit {
            var: self.var,
            negated: !self.negated,
        }
    }

    /// Mirrors `VeriPbCore.litVal`.
    pub fn value(self, assignment: &dyn Fn(u32) -> bool) -> bool {
        if self.negated {
            !assignment(self.var)
        } else {
            assignment(self.var)
        }
    }
}

/// One `coeff * lit` summand. Mirrors `VeriPbCore.Term`.
///
/// Generic over the [`CoeffDomain`]; `Term` alone means `Term<Coeff>`, and
/// that instantiation is `Copy` exactly as it was before the kernel became
/// generic (the derive is conditional on `C: Copy`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Term<C = Coeff> {
    /// The coefficient.
    pub coeff: C,
    /// The literal.
    pub lit: Lit,
}

/// A normalized PB constraint `sum coeff_i * lit_i >= degree`.
///
/// Mirrors `VeriPbCore.Constraint`. Note that, exactly as in the Clean model,
/// the term list is a *multiset*: nothing here merges like terms. Merging is
/// the proved normalization step [`normalize::normalize`] (`VeriPbCore.normC`,
/// slice 2) — see the development design notes.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Constraint<C = Coeff> {
    /// The summands.
    pub terms: Vec<Term<C>>,
    /// The right-hand side.
    pub degree: C,
}

/// The empty constraint `0 >= 1`. Deriving it refutes the formula
/// (`VeriPbCore.unsat_of_entails_contradiction`).
pub const CONTRADICTION_DEGREE: Coeff = 1;

impl<C: CoeffDomain> Constraint<C> {
    /// Build a constraint.
    pub fn new(terms: Vec<Term<C>>, degree: C) -> Self {
        Constraint { terms, degree }
    }

    /// The contradiction `0 >= 1`.
    pub fn contradiction() -> Self {
        Constraint {
            terms: Vec::new(),
            degree: C::one(),
        }
    }

    /// `true` iff this is the contradiction the top-level rule needs.
    pub fn is_contradiction(&self) -> bool {
        self.terms.is_empty() && self.degree >= C::one()
    }

    /// Mirrors `VeriPbCore.evalTerms`. Evaluated in [`CoeffDomain::Exact`]:
    /// the sum of at most `u32::MAX` coefficients is exact there.
    pub fn eval(&self, assignment: &dyn Fn(u32) -> bool) -> C::Exact {
        C::Exact::sum(
            self.terms
                .iter()
                .filter(|t| t.lit.value(assignment))
                .map(|t| t.coeff.widen()),
        )
    }

    /// Mirrors `VeriPbCore.Holds`.
    pub fn holds(&self, assignment: &dyn Fn(u32) -> bool) -> bool {
        self.eval(assignment) >= self.degree.widen()
    }

    /// The normalization side conditions SATURATE requires
    /// (`VeriPbCore.AllNonneg` and `Int.le 0 c.degree`).
    pub fn is_normalized(&self) -> bool {
        C::is_nonneg(&self.degree) && self.all_nonneg()
    }

    /// `VeriPbCore.AllNonneg`.
    pub fn all_nonneg(&self) -> bool {
        self.terms.iter().all(|t| C::is_nonneg(&t.coeff))
    }

    /// Sum of all coefficients, exactly. Mirrors `VeriPbCore.coeffSum`.
    pub fn coeff_sum(&self) -> C::Exact {
        C::Exact::sum(self.terms.iter().map(|t| t.coeff.widen()))
    }
}

/// Why a rule refused to fire.
///
/// Every variant corresponds to a hypothesis of a Clean theorem that the
/// checker could not establish. A rule NEVER produces a constraint when it
/// cannot establish all of them.
///
/// The two *width* variants can only arise in a guarded domain: at [`Big`],
/// `narrow` is total, so a `DegreeOverflow` or `CoeffOverflow` there is
/// unreachable and every other variant is a genuine failure of a rule
/// hypothesis rather than of a machine word.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum GuardError {
    /// A degree would not fit in the domain (`VeriPbCore.fitsI64` = false).
    DegreeOverflow,
    /// A coefficient would not fit in the domain.
    CoeffOverflow,
    /// MULTIPLY / DIVIDE requires a strictly positive factor
    /// (`hk : Int.le 0 k` plus `k != 0`).
    NonPositiveFactor,
    /// SATURATE requires a normalized constraint
    /// (`VeriPbCore.AllNonneg` and `0 <= degree`).
    NotNormalized,
    /// A computed quotient failed `VeriPbCore.CoeffsDominated`.
    QuotientNotCeiling,
    /// MIR was asked for a cut whose remainder `r` is zero, so
    /// `hr0 : Int.lt 0 r` fails. Not a width or soundness failure: the rule
    /// simply has no content there, and the caller derives the trivial
    /// constraint (`VeriPbCore.entails_trivial`) instead. See [`mir`].
    MirZeroRemainder,
}

/// **Rule ADD** — `F |= C1 -> F |= C2 -> F |= C1 + C2`.
///
/// Proved by `VeriPbCore.entails_add`; the width guard is
/// `VeriPbCore.entails_add_checked`.
pub fn add<C: CoeffDomain>(
    c1: &Constraint<C>,
    c2: &Constraint<C>,
) -> Result<Constraint<C>, GuardError> {
    // `concat` rather than `with_capacity` + two `extend_from_slice`: the
    // same list, but measured at 3 verification obligations instead of 21,
    // and with none of them failing. See `pack_constraint` for the table.
    let terms = [c1.terms.as_slice(), c2.terms.as_slice()].concat();
    // The sum is formed through [`Exact::checked_add`], which at the narrow
    // domain IS [`add_degree_wide`] — the leaf carrying the compiler-checked
    // `checkedAdd128_isSome_of_inI64` contract.
    let sum = c1
        .degree
        .widen()
        .checked_add(&c2.degree.widen())
        .ok_or(GuardError::DegreeOverflow)?;
    let degree = C::narrow(&sum).ok_or(GuardError::DegreeOverflow)?;
    // Through `CoeffDomain::pack`, so the `Coeff` path reaches the
    // CONTRACTED `pack_constraint` and the degree ADD stores is compiler-checked.
    Ok(C::pack(terms, degree))
}

/// **Rule MULTIPLY** — `k > 0 -> F |= C -> F |= k * C`.
///
/// Proved by `VeriPbCore.entails_multiply` (which needs only `0 <= k`; `k > 0`
/// is required here so the rule is also non-degenerate).
pub fn multiply<C: CoeffDomain>(k: C, c: &Constraint<C>) -> Result<Constraint<C>, GuardError> {
    if !C::is_nonneg(&k) || k == C::zero() {
        return Err(GuardError::NonPositiveFactor);
    }
    let kw = k.widen();
    let mut terms = Vec::with_capacity(c.terms.len());
    // Every product is formed through [`Exact::checked_mul`], which at the
    // narrow domain IS [`mul_coeff_wide`].
    for t in &c.terms {
        let scaled = kw
            .checked_mul(&t.coeff.widen())
            .ok_or(GuardError::CoeffOverflow)?;
        let coeff = C::narrow(&scaled).ok_or(GuardError::CoeffOverflow)?;
        terms.push(Term { coeff, lit: t.lit });
    }
    let scaled_degree = kw
        .checked_mul(&c.degree.widen())
        .ok_or(GuardError::DegreeOverflow)?;
    let degree = C::narrow(&scaled_degree).ok_or(GuardError::DegreeOverflow)?;
    Ok(C::pack(terms, degree))
}

/// Ceiling division `ceil(x / k)` for `k > 0`, computed exactly.
///
/// The ceiling map itself is **proved**: `VeriPbCore.intCeilDiv` computes this
/// same function over unbounded `Int` (floor division, incremented when the
/// remainder is nonzero), `intCeilDiv_ub` / `intCeilDiv_min` establish both
/// defining inequalities of `ceil`, and `entails_divide_concrete` is DIVIDE
/// instantiated at it — no side conditions left for a checker to discharge.
///
/// This function is *not* what licenses [`divide`]'s output, and nothing in
/// this tree proves `ceil_div == intCeilDiv` for all inputs: the sampled
/// agreement in `tests/width_guards.rs` is a regression test, not a proof.
/// The licensing argument is in [`divide`] instead, and it does not depend on
/// this function being right — see `VeriPbCore.ceilQuotient_unique`.
fn ceil_div<E: Exact>(x: &E, k: &E) -> E {
    debug_assert!(k.is_positive());
    let (q, r) = x.div_mod_floor(k);
    if r == E::zero() { q } else { q.add(&E::one()) }
}

/// **Rule DIVIDE** — `k > 0 -> F |= (sum c_i l_i >= d) -> F |= (sum ceil(c_i/k) l_i >= ceil(d/k))`.
///
/// Delegates to [`divide_with`] at [`ceil_div`]. The correctness of the
/// accepted output does **not** rest on `ceil_div` being right; see there.
pub fn divide<C: CoeffDomain>(k: C, c: &Constraint<C>) -> Result<Constraint<C>, GuardError> {
    divide_with(k, ceil_div::<C::Exact>, c)
}

/// DIVIDE over an *arbitrary* quotient map — the Rust image of `divS`'s
/// abstract `f : Int -> Int`, with the two side conditions re-checked
/// exactly at **every coefficient and at the degree**:
///
/// * `intCeilDiv_ub`  — `c_i <= k * q_i`
/// * `intCeilDiv_min` — `k * q_i < c_i + k`
///
/// Checking *both* at every point is what makes the licensing argument real
/// rather than sampled. `VeriPbCore.ceilQuotient_unique` proves that any `q`
/// satisfying both **is** `intCeilDiv x k`, so an accepted output is exactly
/// `divC (fun x => intCeilDiv x k) c` whatever `f` computed, and is entailed
/// by `VeriPbCore.entails_divide_concrete` — a theorem with no side
/// conditions left over. Before the minimality check was applied per
/// coefficient, an *overshooting* map still satisfied `c_i <= k * q_i` at
/// every coefficient, so the output was only known to satisfy
/// `entails_divide`'s hypotheses, not to equal the concrete ceiling cut.
///
/// This is also the shape of upstream defect 4 (the oversized-divisor
/// fallback that hard-coded `ceil(A/d) = 1`): that map fails one of the two
/// bounds and is rejected.
/// The map is arbitrary, so its product with `k` is computed with
/// [`Exact::checked_mul`]: at the narrow domain a quotient large enough to
/// overflow `i128` is certainly not a ceiling, and is refused rather than
/// allowed to wrap. [`ceil_div`] never reaches that branch (`|k * ceil(x/k)|
/// < 2^126` for `i64` inputs), so `divide` is unaffected; at [`Big`] the
/// product always exists and the branch is dead.
pub fn divide_with<C: CoeffDomain>(
    k: C,
    f: impl Fn(&C::Exact, &C::Exact) -> C::Exact,
    c: &Constraint<C>,
) -> Result<Constraint<C>, GuardError> {
    if !C::is_nonneg(&k) || k == C::zero() {
        return Err(GuardError::NonPositiveFactor);
    }
    let kw = k.widen();

    let check = |x: &C::Exact, q: &C::Exact| -> bool {
        // intCeilDiv_ub: x <= k*q.  intCeilDiv_min: k*q < x + k.
        //
        // Both the product and the bound are formed through the checked
        // leaves ([`mul_coeff_wide`] / [`add_degree_wide`] at the narrow
        // domain), so a quantity this width cannot hold makes the check FAIL
        // rather than wrap into a comparison that might accidentally pass.
        //
        // Both COMPARISONS go through [`Exact::at_least`], which at the narrow
        // domain is [`wide_at_least`] — the leaf carrying `wide_le_exact`. The
        // strict bound is spelled as the negation of the same test rather than
        // as a second comparison, so the two halves of this check are decided
        // by one contracted body and cannot drift apart.
        match (kw.checked_mul(q), x.checked_add(&kw)) {
            (Some(prod), Some(bound)) => prod.at_least(x) && !prod.at_least(&bound),
            _ => false,
        }
    };

    let mut terms = Vec::with_capacity(c.terms.len());
    for t in &c.terms {
        let cw = t.coeff.widen();
        let q = f(&cw, &kw);
        if !check(&cw, &q) {
            return Err(GuardError::QuotientNotCeiling);
        }
        let coeff = C::narrow(&q).ok_or(GuardError::CoeffOverflow)?;
        terms.push(Term { coeff, lit: t.lit });
    }

    let dw = c.degree.widen();
    let qd = f(&dw, &kw);
    if !check(&dw, &qd) {
        return Err(GuardError::QuotientNotCeiling);
    }
    let degree = C::narrow(&qd).ok_or(GuardError::DegreeOverflow)?;
    Ok(C::pack(terms, degree))
}

/// The capping function `min(c, d)`. Mirrors `VeriPbCore.capCoeff`.
///
/// **This function carries a compiler-checked contract on the REAL body** —
/// not on a twin. Under `--cfg feature="trust-surface"` compiler_consumer admits this
/// body through its `Select` lane, imports the defining equation at the `i64`
/// sign-flip order key `key64`, and requires the island theorem
/// `capcoeff_i64_min_full` to prove the clause. Stock rustc never sees the
/// attribute, so the crate builds unchanged without the toolchain.
///
/// The body is *also* reproduced token-for-token in
/// [`trust_surface::cap_coeff_i64`](crate::trust_surface), which cites the
/// same theorem on a twin. That twin no longer carries the licensing weight;
/// it is kept as a differential control, and the correspondence is pinned by
/// `the_i64_cap_functions_have_the_body_of_the_real_cap_coeff` in
/// `tests/island_sync.rs`, so editing this body cannot silently falsify the
/// claim while leaving every test green.
///
/// The clause is the full characterisation `result == min(coeff, degree)`,
/// spelled as three comparisons. The two upper bounds alone would not do:
/// they are satisfied by a cap that returns `i64::MIN`, and *that* cap makes
/// SATURATE unsound. The lower bound is the direction
/// `VeriPbCore.le_capCoeff` supplies and `entails_saturate_of_key` consumes,
/// and it is cited separately by
/// [`trust_surface::cap_coeff_i64_le_capcoeff`](crate::trust_surface).
///
/// [`saturate`] reaches this function through
/// `<Coeff as CoeffDomain>::cap_coeff`, which is a one-line delegation: the
/// generic SATURATE at the narrow domain still runs *this* body, which is
/// what the island claim is about.
///
/// ## The bare-name blocker, and why it is gone
///
/// This contract could not discharge for most of this crate's history, and
/// the reason was a spelling collision rather than anything mathematical: the
/// theorem existed, the body was admitted (`Select { cmp: Le, cmp_left: 1,
/// cmp_right: 0, then_param: 1, else_param: 0 }` — byte-identical to the
/// recognizer output for [`cap_coeff_wide`]), and the in-walk verifier proved
/// all three conjuncts. To substitute `result` with the function's imported
/// defining equation, the ensures lane looked the function up under its BARE
/// item name; `cap_coeff` is also the name of the `Exact` and `CoeffDomain`
/// trait methods and their four impls, so that key was ambiguity-evicted from
/// the facet table, `result` stayed universally quantified, and the citation
/// was checked against the ∀-over-`result` reading, which is false.
///
/// The eviction is CORRECT and is kept: an ambiguous spelling an *author*
/// writes in a clause must fail closed. What was wrong is that the contracted
/// function's own identity is not something an author wrote — the compiler
/// knows the item — so deriving it from the bare name re-entered the
/// ambiguity keyspace through the one door it did not need. The ensures lane
/// now keys on the canonical def-path (trust `d805784d866`), which survives
/// the collision, and this clause discharges unchanged. [`cap_coeff_wide`]
/// was never affected because its bare name is unique — that difference, and
/// not any property of the two widths, was the whole story.
#[cfg_attr(
    feature = "trust-surface",
    trust::ensures(
        result <= coeff && result <= degree && (result >= degree || result >= coeff)
            by capcoeff_i64_min_full
    )
)]
pub fn cap_coeff(degree: Coeff, coeff: Coeff) -> Coeff {
    if coeff <= degree { coeff } else { degree }
}

/// [`cap_coeff`] at [`Wide`] width: the same `VeriPbCore.capCoeff`, for the
/// rules that apply it *inside* the guard arithmetic rather than to stored
/// coefficients.
///
/// `capCoeff` is defined over unbounded `Int`, so this is the faithful image
/// and [`cap_coeff`] is its narrowing; they agree on every `i64` input, `<=`
/// being the same order on both widths. [`mir::mir_f`] needs this one because
/// `mirF` caps a floor-remainder that is only bounded by the divisor, not by
/// anything already narrowed.
///
/// **This function carries a compiler-checked contract on the REAL body** —
/// not on a twin. Under `--cfg feature="trust-surface"` compiler_consumer admits this
/// body through its `Select` lane, imports the defining equation at the
/// `i128` sign-flip order key `key128`, and requires the island theorem
/// `capcoeff_i128_min_full` to prove the clause. Stock rustc never sees the
/// attribute, so the crate builds unchanged without the toolchain.
///
/// The clause is the full characterisation `result == min(coeff, degree)`,
/// spelled as three comparisons. The two upper bounds alone would not do:
/// they are satisfied by a cap that returns `i128::MIN`, and *that* cap makes
/// SATURATE unsound. The third conjunct — the result is at least one of its
/// two arguments — is what rules it out.
///
/// The `i64` sibling [`cap_coeff`] cannot carry the same contract today, and
/// the reason is a name collision rather than anything mathematical: the E9
/// discharge lane binds `result` to a function's imported defining equation
/// by looking the function up under its BARE item name, and `cap_coeff` is
/// the name of six other items in this crate (the two trait declarations and
/// their four impls), so that spelling is ambiguity-evicted from the facet
/// table and `result` stays universally quantified. `cap_coeff_wide` is the
/// only spelling of its function, which is the whole difference.
#[cfg_attr(
    feature = "trust-surface",
    trust::ensures(
        result <= coeff && result <= degree && (result >= degree || result >= coeff)
            by capcoeff_i128_min_full
    )
)]
pub fn cap_coeff_wide(degree: Wide, coeff: Wide) -> Wide {
    if coeff <= degree { coeff } else { degree }
}

/// **SATURATE's per-term step**, at the stored-coefficient width — the body
/// the generic [`saturate`] runs at [`Coeff`].
///
/// **This function carries a compiler-checked contract on the REAL body.** The
/// clause is `result.coeff <= degree`: the coefficient of the `Term` this
/// builds never exceeds the degree, which is the direction
/// `VeriPbCore.capCoeff_le_degree` supplies and `entails_saturate_of_key`
/// consumes. The VALUE is pinned separately and more strongly by [`cap_coeff`],
/// whose CITED clause is the full characterisation `min(coeff, degree)` at this
/// same width; what this leaf adds is that the `Term` actually constructed
/// carries that value — which no clause on `cap_coeff` alone can say.
///
/// ## Why this contract is UNCITED, and why that is not "unchecked"
///
/// It is listed in `UNCITED_NATIVE_ONLY`, whose other members are nullary
/// constants and the ADD/WEAKEN output-degree claims. This one is richer than
/// those, and it is here for a stated reason rather than by omission.
///
/// The clause is **proved by the native full verifier**, and discriminated: the
/// twin body that ignores the cap (`Term { coeff, .. }`) is correctly REFUTED
/// on the identical clause. So the claim is checked; it is just not checked by
/// a *kernel citation*.
///
/// It cannot be, today. A citation needs the clause inside the exact statement
/// fragment, and an aggregate-returning function is outside it in BOTH spellings
/// — the closure form is refused with *"predicate must be a comparison or a
/// connective"*, and the signature form `result.coeff <= degree` with *"missing
/// supported type for clause variable `result.coeff`"*. The citation lane has no
/// sort for a field projection of the result. That is a toolchain gap, not a
/// soundness gap, and `capcoeff_i64_le_degree` is the theorem waiting for it.
///
/// ## Why the clause is one comparison and not the full characterisation
///
/// Not a judgement about what is worth stating. The three-conjunct form
/// `result.coeff <= coeff && result.coeff <= degree && (result.coeff >= degree
/// || result.coeff >= coeff)` is TRUE of this body and was measured to be
/// **falsely refuted** — `0 proved, 2 failed`, with its `i64::MIN` twin refuted
/// identically. That is the conjunction defect the toolchain records (probe
/// f53: the native lane refutes uncited `&&` clauses that are tautologies), and
/// it is fail-safe. Widen this clause when that lane is fixed.
#[cfg_attr(
    feature = "trust-surface",
    trust::ensures(result.coeff <= degree by satterm_coeff_le_degree)
)]
pub fn sat_term(degree: Coeff, coeff: Coeff, lit: Lit) -> Term<Coeff> {
    Term {
        coeff: cap_coeff(degree, coeff),
        lit,
    }
}

/// **Rule SATURATE** — `F |= (sum c_i l_i >= d) -> F |= (sum min(c_i,d) l_i >= d)`.
///
/// Proved by `VeriPbCore.entails_saturate`, whose hypotheses are exactly the
/// normalization check below. Saturation is UNSOUND without it.
pub fn saturate<C: CoeffDomain>(c: &Constraint<C>) -> Result<Constraint<C>, GuardError> {
    if !c.is_normalized() {
        return Err(GuardError::NotNormalized);
    }
    let terms = c
        .terms
        .iter()
        .map(|t| C::sat_term(&c.degree, &t.coeff, t.lit))
        .collect();
    Ok(C::pack(terms, c.degree.clone()))
}

/// **Rule LITERAL** — `|= (l + ~l >= 1)`, entailed by every formula.
///
/// Proved by `VeriPbCore.entails_literal`.
pub fn literal_axiom<C: CoeffDomain>(l: Lit) -> Constraint<C> {
    Constraint {
        terms: vec![
            Term {
                coeff: C::one(),
                lit: l,
            },
            Term {
                coeff: C::one(),
                lit: l.negate(),
            },
        ],
        degree: C::one(),
    }
}

/// **Degree weakening** — relax the right-hand side downward.
///
/// This is the shape of VeriPB bug C: the degree is decremented by `w`, and in
/// the buggy code the `i64` subtraction wraps. Here the new degree `r` must
/// satisfy `r + w == degree` recomputed exactly
/// (`VeriPbCore.entails_weaken_checked`), which a wrapped value cannot do.
pub fn weaken_degree<C: CoeffDomain>(c: &Constraint<C>, w: C) -> Result<Constraint<C>, GuardError> {
    if !C::is_nonneg(&w) {
        return Err(GuardError::NonPositiveFactor);
    }
    let ww = w.widen();
    // The decrement itself, through [`Exact::checked_sub`] — at the narrow
    // domain that IS [`sub_degree_wide`], the leaf carrying
    // `checkedSub128_isSome_of_inI64`. This is the subtraction bug C wraps.
    let truth = c
        .degree
        .widen()
        .checked_sub(&ww)
        .ok_or(GuardError::DegreeOverflow)?;
    let r = C::narrow(&truth).ok_or(GuardError::DegreeOverflow)?;
    // The Clean hypothesis, verbatim: eqOkB (r + w) c.degree. Unreachable on
    // any input (r comes from the same exact arithmetic), but checked for
    // real — defence in depth, like divide's quotient re-checks. The sum is
    // recomputed through the checked leaf too, so the re-check cannot be
    // satisfied by a wrapped value.
    let back = r
        .widen()
        .checked_add(&ww)
        .ok_or(GuardError::DegreeOverflow)?;
    if !C::eq_ok(&c.degree, &back) {
        return Err(GuardError::DegreeOverflow);
    }
    // Routed through `CoeffDomain::apply_weaken` so the `Coeff` path reaches
    // the CONTRACTED `weaken_apply`: on the width the checker runs, the
    // degree of the constraint WEAKEN returns is compiler-checked to be the
    // guarded value computed above. The terms half is not -- see
    // `weaken_apply`'s doc for exactly what is and is not claimed.
    Ok(C::apply_weaken(c, r))
}

/// **Negation** of a normalized constraint, for RUP.
///
/// `!(sum c_i l_i >= d)` is `sum c_i ~l_i >= (sum c_i) - d + 1`. Establishing
/// `Unsat(negate(C) :: F)` yields `F |= C` by
/// `VeriPbCore.entails_of_negation_unsat`, whose witness equation
/// `nd + d = coeffSum + 1` is exactly the guard below.
pub fn negate<C: CoeffDomain>(c: &Constraint<C>) -> Result<Constraint<C>, GuardError> {
    let coeff_sum = c.coeff_sum();
    let one = <C::Exact as Exact>::one();
    // `coeffSum - d + 1`, formed through the checked leaves.
    let nd_wide = coeff_sum
        .checked_sub(&c.degree.widen())
        .ok_or(GuardError::DegreeOverflow)?
        .checked_add(&one)
        .ok_or(GuardError::DegreeOverflow)?;
    let degree = C::narrow(&nd_wide).ok_or(GuardError::DegreeOverflow)?;
    // The witness equation nd + d = coeffSum + 1, checked for real.
    let back = coeff_sum
        .checked_add(&one)
        .ok_or(GuardError::DegreeOverflow)?
        .checked_sub(&degree.widen())
        .ok_or(GuardError::DegreeOverflow)?;
    if !C::eq_ok(&c.degree, &back) {
        return Err(GuardError::DegreeOverflow);
    }
    let terms = c
        .terms
        .iter()
        .map(|t| Term {
            coeff: t.coeff.clone(),
            lit: t.lit.negate(),
        })
        .collect();
    Ok(C::pack(terms, degree))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn all_true(_: u32) -> bool {
        true
    }
    fn all_false(_: u32) -> bool {
        false
    }

    fn big(x: i64) -> Big {
        Big::from(x)
    }

    /// `2^64`, one bit above the narrow domain.
    fn beyond_i64() -> Big {
        Big::from(u64::MAX) + Big::from(1)
    }

    #[test]
    fn eval_matches_clean_controls() {
        // Mirrors VeriPbCore.ctrl_eval_true / ctrl_eval_false.
        let c = Constraint::new(
            vec![Term {
                coeff: 3,
                lit: Lit::pos(0),
            }],
            1,
        );
        assert_eq!(c.eval(&all_true), 3);
        assert_eq!(c.eval(&all_false), 0);
    }

    #[test]
    fn literal_axiom_always_evaluates_to_one() {
        // Mirrors VeriPbCore.ctrl_litAxiom_true / ctrl_litAxiom_false.
        let c: Constraint = literal_axiom(Lit::pos(0));
        assert_eq!(c.eval(&all_true), 1);
        assert_eq!(c.eval(&all_false), 1);
        assert!(c.holds(&all_true) && c.holds(&all_false));
    }

    #[test]
    fn cap_coeff_matches_clean_controls() {
        assert_eq!(cap_coeff(3, 7), 3);
        assert_eq!(cap_coeff(3, 2), 2);
    }

    #[test]
    fn add_is_semantically_sound_on_a_witness() {
        let c1 = Constraint::new(
            vec![Term {
                coeff: 2,
                lit: Lit::pos(0),
            }],
            1,
        );
        let c2 = Constraint::new(
            vec![Term {
                coeff: 3,
                lit: Lit::pos(1),
            }],
            2,
        );
        let s = add(&c1, &c2).unwrap();
        assert_eq!(s.degree, 3);
        assert!(s.holds(&all_true));
    }

    #[test]
    fn divide_rounds_up_and_passes_its_own_guards() {
        // 4x + 3y >= 5, divided by 2 => 2x + 2y >= 3.
        let c = Constraint::new(
            vec![
                Term {
                    coeff: 4,
                    lit: Lit::pos(0),
                },
                Term {
                    coeff: 3,
                    lit: Lit::pos(1),
                },
            ],
            5,
        );
        let d = divide(2, &c).unwrap();
        assert_eq!(d.degree, 3);
        assert_eq!(d.terms[0].coeff, 2);
        assert_eq!(d.terms[1].coeff, 2);
    }

    #[test]
    fn saturate_requires_normalization() {
        let bad = Constraint::new(
            vec![Term {
                coeff: -1,
                lit: Lit::pos(0),
            }],
            1,
        );
        assert_eq!(saturate(&bad), Err(GuardError::NotNormalized));
        let ok = Constraint::new(
            vec![Term {
                coeff: 7,
                lit: Lit::pos(0),
            }],
            3,
        );
        assert_eq!(saturate(&ok).unwrap().terms[0].coeff, 3);
    }

    #[test]
    fn negate_round_trips_the_witness_equation() {
        let c = Constraint::new(
            vec![
                Term {
                    coeff: 2,
                    lit: Lit::pos(0),
                },
                Term {
                    coeff: 3,
                    lit: Lit::pos(1),
                },
            ],
            4,
        );
        let n = negate(&c).unwrap();
        // nd + d == coeffSum + 1
        assert_eq!(
            Wide::from(n.degree) + Wide::from(c.degree),
            c.coeff_sum() + 1
        );
    }

    // -----------------------------------------------------------------
    // The `Big` instantiation: the same rules where the narrow one refuses.
    // -----------------------------------------------------------------

    /// The narrow domain refuses the ADD whose degree leaves `i64`; the
    /// complete domain computes it, and computes it *right* — the value a
    /// wrapping `i64` add would have produced is a different number.
    #[test]
    fn add_beyond_i64_is_refused_narrow_and_exact_wide() {
        let a = Constraint::new(
            vec![Term {
                coeff: 1,
                lit: Lit::pos(0),
            }],
            Coeff::MAX,
        );
        let b = Constraint::new(
            vec![Term {
                coeff: 1,
                lit: Lit::pos(1),
            }],
            1,
        );
        assert_eq!(add(&a, &b), Err(GuardError::DegreeOverflow));

        let a = Constraint::new(
            vec![Term {
                coeff: big(1),
                lit: Lit::pos(0),
            }],
            big(Coeff::MAX),
        );
        let b = Constraint::new(
            vec![Term {
                coeff: big(1),
                lit: Lit::pos(1),
            }],
            big(1),
        );
        let s = add(&a, &b).unwrap();
        assert_eq!(s.degree, Big::from(Coeff::MAX) + Big::from(1));
        assert_ne!(
            s.degree,
            big(Coeff::MIN),
            "the wrap the narrow guard prevents"
        );
    }

    #[test]
    fn multiply_beyond_i64_is_refused_narrow_and_exact_wide() {
        let a = Constraint::new(
            vec![Term {
                coeff: Coeff::MAX,
                lit: Lit::pos(0),
            }],
            1,
        );
        assert_eq!(multiply(2, &a), Err(GuardError::CoeffOverflow));

        let a = Constraint::new(
            vec![Term {
                coeff: big(Coeff::MAX),
                lit: Lit::pos(0),
            }],
            big(1),
        );
        let m = multiply(big(2), &a).unwrap();
        assert_eq!(m.terms[0].coeff, Big::from(Coeff::MAX) * Big::from(2));
        assert_eq!(m.degree, big(2));
    }

    #[test]
    fn weaken_degree_underflow_is_refused_narrow_and_exact_wide() {
        // Bug C verbatim, at both domains.
        let a = Constraint::new(
            vec![Term {
                coeff: 1,
                lit: Lit::pos(0),
            }],
            Coeff::MIN,
        );
        assert_eq!(weaken_degree(&a, 1), Err(GuardError::DegreeOverflow));

        let a = Constraint::new(
            vec![Term {
                coeff: big(1),
                lit: Lit::pos(0),
            }],
            big(Coeff::MIN),
        );
        let w = weaken_degree(&a, big(1)).unwrap();
        assert_eq!(w.degree, Big::from(Coeff::MIN) - Big::from(1));
        assert_ne!(
            w.degree,
            big(Coeff::MAX),
            "the wrap the narrow guard prevents"
        );
    }

    /// DIVIDE at the complete domain still rounds *up*, on a coefficient no
    /// machine word can hold.
    #[test]
    fn divide_is_a_ceiling_beyond_i64() {
        let a = Constraint::new(
            vec![Term {
                coeff: beyond_i64() + Big::from(1),
                lit: Lit::pos(0),
            }],
            beyond_i64() + Big::from(1),
        );
        let d = divide(big(2), &a).unwrap();
        // ceil((2^64 + 1) / 2) = 2^63 + 1.
        let expect = Big::from(1u64 << 63) + Big::from(1);
        assert_eq!(d.terms[0].coeff, expect);
        assert_eq!(d.degree, expect);
    }

    #[test]
    fn saturate_caps_beyond_i64() {
        let c = Constraint::new(
            vec![
                Term {
                    coeff: beyond_i64(),
                    lit: Lit::pos(0),
                },
                Term {
                    coeff: big(3),
                    lit: Lit::pos(1),
                },
            ],
            big(7),
        );
        let s = saturate(&c).unwrap();
        assert_eq!(s.terms[0].coeff, big(7));
        assert_eq!(s.terms[1].coeff, big(3));
    }

    #[test]
    fn negate_beyond_i64_is_refused_narrow_and_exact_wide() {
        let a = Constraint::new(
            vec![Term {
                coeff: Coeff::MAX,
                lit: Lit::pos(0),
            }],
            Coeff::MIN,
        );
        assert_eq!(negate(&a), Err(GuardError::DegreeOverflow));

        let a = Constraint::new(
            vec![Term {
                coeff: big(Coeff::MAX),
                lit: Lit::pos(0),
            }],
            big(Coeff::MIN),
        );
        let n = negate(&a).unwrap();
        assert_eq!(
            n.degree,
            Big::from(Coeff::MAX) - Big::from(Coeff::MIN) + Big::from(1)
        );
        assert_eq!(n.terms[0].lit, Lit::neg(0));
    }

    /// The complete domain's `narrow` is total, so the two width variants of
    /// [`GuardError`] are unreachable there. Every rule that can only fail on
    /// width therefore always fires.
    #[test]
    fn the_complete_domain_has_no_width_failures() {
        let huge = beyond_i64() * beyond_i64() * beyond_i64();
        let c = Constraint::new(
            vec![Term {
                coeff: huge.clone(),
                lit: Lit::pos(0),
            }],
            huge.clone(),
        );
        assert!(add(&c, &c).is_ok());
        assert!(multiply(huge.clone(), &c).is_ok());
        assert!(divide(huge.clone(), &c).is_ok());
        assert!(saturate(&c).is_ok());
        assert!(weaken_degree(&c, huge.clone()).is_ok());
        assert!(negate(&c).is_ok());
    }

    /// `div_mod_floor` is floor division at both widths: same quotient, same
    /// nonnegative remainder, and the division witness `q*k + m = x` holds.
    #[test]
    fn div_mod_floor_agrees_across_the_two_exact_widths() {
        for x in [-9_i64, -7, -1, 0, 1, 6, 7, 1_000_000] {
            for k in [1_i64, 2, 3, 7, 1_000] {
                let (qn, rn) = Wide::from(x).div_mod_floor(&Wide::from(k));
                let (qb, rb) = big(x).div_mod_floor(&big(k));
                assert_eq!(qb, big(qn as i64), "quotient x={x} k={k}");
                assert_eq!(rb, big(rn as i64), "remainder x={x} k={k}");
                assert!(rn >= 0 && rn < Wide::from(k));
                assert_eq!(qn * Wide::from(k) + rn, Wide::from(x));
            }
        }
    }
}
