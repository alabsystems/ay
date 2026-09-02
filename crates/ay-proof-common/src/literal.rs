// Copyright 2026 Andrew Yates
// Standalone literal/variable types for SAT proof checkers.
// Encoding: positive = 2*var, negative = 2*var + 1. Zero-indexed internally.

use thiserror::Error;

/// Failure to construct or convert a proof-checker literal.
#[derive(Debug, Clone, Copy, Error, PartialEq, Eq)]
#[non_exhaustive]
pub enum LiteralError {
    /// A zero-indexed variable ID does not fit the packed literal encoding.
    #[error("variable {id} exceeds the maximum encodable variable {maximum}")]
    VariableOutOfRange { id: u32, maximum: u32 },

    /// A platform-sized literal index does not fit the `u32` packed encoding.
    #[error("literal index {index} exceeds the maximum packed index {maximum}")]
    IndexOutOfRange { index: usize, maximum: u32 },

    /// Zero terminates a DIMACS clause and therefore is not a literal.
    #[error("DIMACS literal 0 is a clause terminator")]
    ZeroDimacsLiteral,

    /// A valid internal literal has no signed `i32` DIMACS representation.
    #[error("DIMACS literal {value} is outside the i32 range")]
    DimacsOutOfRange { value: i64 },
}

/// A variable identifier (0-indexed internally).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Variable(u32);

// Ties the literal bounds used in this file's Trust preconditions to
// the constants they are supposed to mirror. A contract predicate cannot name
// an associated constant (the frontend refuses to lower it -- see
// `Variable::new`), so the bounds are duplicated as literals; these assertions
// are what stop that duplication from rotting into a WRONG contract, which
// would be worse than no contract at all because a precondition is ASSUMED by
// the prover inside the body. Divergence is a compile error, not a silent
// unsoundness.
// Only `MAX_ID` needs guarding. `Literal::from_index`'s bound mirrors
// `u32::MAX`, which is fixed by the language and cannot drift -- asserting it
// is a tautology, and clippy says so.
const _: () = assert!(Variable::MAX_ID == 2_147_483_647);

impl Variable {
    /// Largest variable ID accepted by the packed [`Literal`] encoding.
    pub const MAX_ID: u32 = u32::MAX >> 1;

    /// Try to create a variable from a raw zero-indexed identifier.
    ///
    /// # Errors
    ///
    /// Returns [`LiteralError::VariableOutOfRange`] if `id` exceeds
    /// [`Self::MAX_ID`].
    #[inline]
    pub fn try_new(id: u32) -> Result<Self, LiteralError> {
        if id <= Self::MAX_ID {
            Ok(Self(id))
        } else {
            Err(LiteralError::VariableOutOfRange {
                id,
                maximum: Self::MAX_ID,
            })
        }
    }

    /// Create a new variable from a raw 0-indexed identifier.
    ///
    /// Prefer [`Self::try_new`] when the identifier comes from an external
    /// input.
    ///
    /// # Panics
    ///
    /// Panics if `id` exceeds [`Self::MAX_ID`]. That panic is the whole reason
    /// this function's panic-freedom obligation is FALSE unconditionally: the
    /// `# Panics` clause above IS the missing precondition, and the contract
    /// below is that clause written where a prover can read it.
    ///
    /// The bound is spelled as a LITERAL rather than as `Self::MAX_ID`, and
    /// that is forced, not stylistic. MEASURED on trust-e26541e3: a contract
    /// predicate naming an associated constant is rejected by the frontend
    /// ("unsupported contract predicate expression
    /// `id <= Variable::MAX_ID`") and discharges nothing. The
    /// `const _: ()` assertion above `impl Variable` makes the duplication
    /// safe: if `MAX_ID` ever changes, this file stops compiling rather than
    /// silently carrying a contract that no longer matches the assertion it is
    /// supposed to justify.
    ///
    /// ── WHY THERE IS NO `requires` CLAUSE HERE, DESPITE ALL OF THE ABOVE ────
    ///
    /// There WAS one, as ``, and it never ran: the attribute form needed an
    /// `--extern trust` overlay, so it fired only in the ratchet lane. A
    /// verified probe made its runtime behavior observable and showed that it
    /// CONTRADICTS this function's tested public behavior.
    ///
    /// The overlay half of that story is now obsolete — the default toolchain
    /// is Trust and the sanctioned spelling is the native clause
    /// `pub fn new(id: u32) -> Self requires id <= 2_147_483_647`, which needs
    /// no overlay and fires in EVERY build. That makes the objection below
    /// stronger, not weaker, and it is why this clause is still absent: the
    /// decision it records is about the API, not about how the precondition is
    /// spelled.
    ///
    /// A `requires` clause is not only a static claim. Where a caller cannot
    /// discharge it, the compiler installs a kernel-certified RUNTIME MONITOR,
    /// and that monitor is a NON-UNWINDING abort:
    ///
    /// ```text
    /// thread '..' panicked at core/src/panicking.rs:225:5:
    /// kernel-certified Trust monitor failed
    /// thread caused non-unwinding panic. aborting.
    /// process didn't exit successfully (signal: 6, SIGABRT)
    /// ```
    ///
    /// `literal_tests::test_overflow_variable_panics` asserts the opposite, and
    /// says why in its own body: "Invalid state is rejected at the Variable
    /// boundary in every build mode". It calls `Variable::new(MAX_VAR + 1)`
    /// under `#[should_panic(expected = "exceeds Variable::MAX_ID")]`. A
    /// `should_panic` test cannot catch an abort — the process dies — so the
    /// contract does not merely fail that test, it removes the recoverable,
    /// catchable panic this API documents and guarantees.
    ///
    /// Both designs are coherent; they are just different APIs. "Out-of-range
    /// input is a caller error the prover must rule out" and "out-of-range
    /// input is a supported, tested, recoverable failure" cannot both hold.
    /// Choosing between them is an API decision, not a verification-lane
    /// decision, so turning verification on does not get to make it silently.
    /// The precondition is left unstated here and the guarantee kept.
    ///
    /// The statically-checkable half is not lost: [`Self::try_new`] carries the
    /// same bound in its return type, needs no precondition, and is what the
    /// `# Panics` note above already tells external callers to prefer.
    ///
    /// To adopt the contract instead, the panic tests must first move to a
    /// subprocess harness that can observe SIGABRT.
    #[inline]
    pub fn new(id: u32) -> Self {
        assert!(
            id <= Self::MAX_ID,
            "variable {id} exceeds Variable::MAX_ID ({})",
            Self::MAX_ID
        );
        Self(id)
    }

    /// Get the raw 0-indexed identifier.
    #[inline]
    pub fn id(self) -> u32 {
        self.0
    }

    /// Get the identifier as an index into a variable-indexed collection.
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A literal (variable with polarity).
///
/// Encoded as: positive = 2*var, negative = 2*var + 1.
/// This compact encoding allows direct indexing into watch/assignment arrays.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Literal(u32);

impl Literal {
    /// Maximum variable index that can be represented without overflow.
    /// Variable indices >= 2^31 would cause the `<< 1` encoding to overflow u32.
    pub const MAX_VAR: u32 = Variable::MAX_ID;

    /// Create a positive literal for the given variable.
    ///
    /// Postcondition (`result.variable() == var && result.is_positive()`) is
    /// NOT EXPRESSIBLE — see the note on [`Self::negated`].
    #[inline]
    pub fn positive(var: Variable) -> Self {
        Self(var.0 << 1)
    }

    /// Create a negative literal for the given variable.
    ///
    /// Postcondition (`result.variable() == var && !result.is_positive()`) is
    /// NOT EXPRESSIBLE — see the note on [`Self::negated`].
    #[inline]
    pub fn negative(var: Variable) -> Self {
        Self((var.0 << 1) | 1)
    }

    /// Get the underlying variable.
    #[inline]
    pub fn variable(self) -> Variable {
        Variable(self.0 >> 1)
    }

    /// True if this literal has positive polarity.
    #[inline]
    pub fn is_positive(self) -> bool {
        (self.0 & 1) == 0
    }

    /// Get the negation of this literal.
    ///
    /// # The encoding postconditions are not expressible today
    ///
    /// The three properties that actually define this operation —
    /// `result.variable() == self.variable()`,
    /// `result.is_positive() != self.is_positive()`, and the involution
    /// `result.negated() == self` — are exactly what the deleted `ensures!`
    /// macro claimed to state and silently erased. They are STILL unstatable,
    /// for a different and more precise reason: MEASURED on trust-e26541e3,
    /// every `result`-and-method postcondition in this file was refused with
    /// "compiler contract predicate was not lowered into a typed verifier
    /// formula", landing in UNKNOWN. The lowerable fragment is comparisons of
    /// PARAMETERS against LITERALS; `result` sugar and method projections parse
    /// (see the toolchain's tests/ui/contracts/trust-spec-opaque-spec-clauses.rs,
    /// which is `check-pass` — it proves they PARSE, not that they LOWER) but do
    /// not reach the solver.
    ///
    /// These are not left unchecked. They are PROVED over a bounded range by the
    /// `model-checker-consumer` harnesses at the bottom of this file, which is why an
    /// unprovable attribute here would add noise rather than assurance.
    #[inline]
    pub fn negated(self) -> Self {
        Self(self.0 ^ 1)
    }

    /// Index into watch/assignment arrays (2 entries per variable).
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Get the raw packed `u32` encoding.
    #[inline]
    pub fn raw(self) -> u32 {
        self.0
    }

    /// Create a literal from its raw packed `u32` encoding.
    ///
    /// Every `u32` is a valid packed literal: its low bit is the polarity and
    /// the remaining 31 bits identify a variable no larger than [`Self::MAX_VAR`].
    #[inline]
    pub fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    /// Try to create a literal from a platform-sized packed index.
    ///
    /// This is the fallible inverse of [`Self::index`] for callers whose index
    /// did not necessarily originate from a `Literal`.
    ///
    /// # Errors
    ///
    /// Returns [`LiteralError::IndexOutOfRange`] if `idx` does not fit the
    /// packed `u32` encoding.
    #[inline]
    pub fn try_from_index(idx: usize) -> Result<Self, LiteralError> {
        u32::try_from(idx)
            .map(Self::from_raw)
            .map_err(|_| LiteralError::IndexOutOfRange {
                index: idx,
                maximum: u32::MAX,
            })
    }

    /// Create a literal from a raw index (inverse of `index()`).
    ///
    /// The index encodes both variable and polarity: `positive = 2*var`,
    /// `negative = 2*var + 1`. This enables zero-cost conversion between
    /// literal types that use the same encoding scheme.
    /// Prefer [`Self::try_from_index`] unless the index came from
    /// [`Self::index`].
    ///
    /// # Panics
    ///
    /// Panics if `idx` exceeds `u32::MAX` on a platform where `usize` is wider
    /// than `u32`.
    ///
    /// NO `requires` CLAUSE, for exactly the reason spelled out at length on
    /// [`Variable::new`], and this is the second function where the explicit
    /// verified probe exposed the incompatible runtime behavior.
    ///
    /// `literal_tests::test_from_index_never_silently_truncates` calls
    /// `from_index(u32::MAX as usize + 1)` under
    /// `#[should_panic(expected = "exceeds u32::MAX")]`. With
    /// `requires idx <= 4294967295` the caller's obligation is undischargeable,
    /// the compiler installs the kernel-certified runtime monitor, and the
    /// monitor ABORTS (SIGABRT, non-unwinding) instead of panicking — which
    /// `should_panic` cannot catch and which destroys the "never silently
    /// truncates" guarantee the test's name states.
    ///
    /// Worth recording separately, because it means the contract was buying
    /// less than it looked like even statically: MEASURED, the literal form
    /// does NOT prove this function's assertion. It only moves it from FAILED
    /// to runtime-checked, because `u32::try_from(idx).is_ok()` in the body is
    /// an absent callee whose result is havoc'd, so the precondition never
    /// reaches the assertion that consumes it. So the trade here was a real
    /// behavioural regression for no static gain at all.
    ///
    /// (Had it been kept, the bound would have to stay a literal: the natural
    /// `idx <= u32::MAX as usize` is refused by the frontend — the associated
    /// constant AND the cast are both unsupported in a contract predicate.)
    #[inline]
    pub fn from_index(idx: usize) -> Self {
        assert!(
            u32::try_from(idx).is_ok(),
            "literal index {idx} exceeds u32::MAX"
        );
        Self::from_raw(idx as u32)
    }

    /// Try to create a literal from a DIMACS-style signed integer.
    ///
    /// Every nonzero `i32` is representable, including `i32::MIN`. Zero is a
    /// clause terminator rather than a literal.
    ///
    /// # Errors
    ///
    /// Returns [`LiteralError::ZeroDimacsLiteral`] if `dimacs` is zero.
    #[inline]
    pub fn try_from_dimacs(dimacs: i32) -> Result<Self, LiteralError> {
        if dimacs == 0 {
            Err(LiteralError::ZeroDimacsLiteral)
        } else {
            Ok(Self::from_nonzero_dimacs(dimacs))
        }
    }

    /// Create a literal from a DIMACS-style signed integer.
    ///
    /// DIMACS variables are 1-indexed. `from_dimacs(3)` → positive literal for
    /// internal variable 2. `from_dimacs(-1)` → negative literal for variable 0.
    /// Prefer [`Self::try_from_dimacs`] when the value comes from an external
    /// input.
    ///
    /// # Panics
    ///
    /// Panics if `dimacs` is zero, the DIMACS clause terminator.
    #[inline]
    pub fn from_dimacs(dimacs: i32) -> Self
        requires dimacs != 0
    {
        assert_ne!(dimacs, 0, "DIMACS literal 0 is a clause terminator");
        Self::from_nonzero_dimacs(dimacs)
    }

    /// The postcondition `result.is_positive() == (dimacs > 0)` is NOT
    /// EXPRESSIBLE (see [`Self::negated`]); the precondition IS, and it is a
    /// real one: `precond` obligations are emitted at BOTH call sites
    /// ([`Self::from_dimacs`] and [`Self::try_from_dimacs`]) and both are
    /// discharged, so the assumption this body enjoys is paid for, not granted.
    #[inline]
    fn from_nonzero_dimacs(dimacs: i32) -> Self
        requires dimacs != 0
    {
        // This computes `dimacs.unsigned_abs() - 1`, respelled so the encoder
        // keeps the range link. Same class of fix, and the same reason, as
        // `to_dimacs_i64` below.
        //
        // `<i32>::unsigned_abs` is an ABSENT CALLEE to the deductive verifier (its
        // body is not in the lowered bundle), so its result is havoc'd to a fresh
        // symbolic and every relation to `dimacs` is lost. The `- 1` was then
        // encoded as satisfiable at zero. MEASURED 2026-08-26 on the sealed
        // toolchain: `Variable(dimacs.unsigned_abs() - 1)` reports
        // `[overflow:sub] FAILED (ay-in-process); counterexample: dimacs = 0`.
        //
        // That counterexample is MISLEADING, and reading it as "the precondition
        // is missing" is a trap I fell into and measured my way out of. Hoisting
        // the caller's zero-guard into this body does NOT fix it: with the guard
        // inlined the verifier simply reports `counterexample: _4 = 0, dimacs = 1`
        // -- it honours `dimacs != 0` and STILL believes the magnitude is zero,
        // because the havoc'd `unsigned_abs` result is unconstrained no matter
        // what is known about `dimacs`. The blocker is the absent callee, not the
        // erased `requires!`. That finding SURVIVES this file's migration to
        // first-class contracts: `dimacs != 0` is now a real checked attribute
        // the prover reads rather than a macro that expanded to nothing, and the
        // absent-callee havoc it could not defeat is precisely why the body still
        // has to avoid `unsigned_abs` rather than lean on the precondition.
        //
        // Both branches below are built only from operations the encoder models
        // directly, so the magnitude stays tied to `dimacs`:
        //   * `dimacs > 0`  =>  `dimacs >= 1`, so `dimacs - 1` cannot underflow
        //     and is non-negative, making `as u32` value-preserving.
        //   * `dimacs < 0`  =>  `!dimacs == |dimacs| - 1` exactly, for EVERY
        //     negative `i32` including `i32::MIN`, whose absolute value is not
        //     representable in `i32` at all. Bitwise NOT is total, so this branch
        //     carries no arithmetic obligation whatsoever.
        // Verified equal to the old spelling for all four boundaries: 1 -> 0,
        // i32::MAX -> 2147483646, -1 -> 0, i32::MIN -> 2147483647.
        if dimacs > 0 {
            Self::positive(Variable((dimacs - 1) as u32))
        } else {
            Self::negative(Variable(!dimacs as u32))
        }
    }

    /// Try to convert this literal to a DIMACS signed `i32`.
    ///
    /// Negative [`Self::MAX_VAR`] maps to `i32::MIN`. Positive
    /// [`Self::MAX_VAR`] is the only valid packed literal outside the signed
    /// `i32` DIMACS range.
    ///
    /// # Errors
    ///
    /// Returns [`LiteralError::DimacsOutOfRange`] for positive
    /// [`Self::MAX_VAR`].
    #[inline]
    pub fn try_to_dimacs(self) -> Result<i32, LiteralError> {
        let value = self.to_dimacs_i64();
        i32::try_from(value).map_err(|_| LiteralError::DimacsOutOfRange { value })
    }

    /// Convert to a DIMACS signed integer.
    ///
    /// This is the inverse of [`Self::from_dimacs`] for every nonzero `i32`,
    /// including `i32::MIN`.
    ///
    /// # Panics
    ///
    /// Panics for the positive literal of [`Self::MAX_VAR`], whose DIMACS
    /// value is `2_147_483_648`. Use [`Self::try_to_dimacs`],
    /// [`Self::to_dimacs_i64`], or `Display` when extension variables may reach
    /// this boundary.
    ///
    /// NOT EXPRESSIBLE as a Trust precondition on this toolchain, and left
    /// unstated rather than approximated. The exact precondition is
    /// `!(self.is_positive() && self.variable().id() == Literal::MAX_VAR)`:
    /// `to_dimacs_i64` returns `±(var_id + 1)`, so the positive branch leaves
    /// `i32` only at `var_id == MAX_VAR` (giving `2_147_483_648`), while the
    /// negative branch bottoms out at exactly `i32::MIN` for that same `var_id`
    /// and is always representable. MEASURED on trust-e26541e3: that predicate
    /// is refused — "unsupported contract predicate expression" — because the
    /// lowerable fragment is comparisons of PARAMETERS against LITERALS, and
    /// this condition is irreducibly about `self` through two method calls
    /// (`is_positive`, `variable().id()`). There is no literal-only rewrite: the
    /// packed `self.0` field is private to the type but the predicate is
    /// evaluated as written, and no supported form can reach it. A weaker
    /// approximation would be a contract the prover ASSUMES, so stating one
    /// would be worse than stating none. This obligation therefore stays
    /// honestly FAILED until the frontend lowers field/method projections.
    #[inline]
    pub fn to_dimacs(self) -> i32 {
        let value = self.to_dimacs_i64();
        assert!(
            i32::try_from(value).is_ok(),
            "variable ID too large for DIMACS i32 representation: {value}"
        );
        value as i32
    }

    /// Convert to DIMACS signed integer as `i64` (never panics).
    ///
    /// Extension variables in LRAT proofs (extended resolution) can have
    /// variable IDs up to `u32::MAX >> 1`, which exceeds `i32::MAX - 1`.
    /// This method uses `i64` arithmetic to avoid overflow on any valid
    /// literal. Prefer this in diagnostic/error paths where panicking would
    /// mask the real error (#5327).
    #[inline]
    pub fn to_dimacs_i64(self) -> i64 {
        // `as i64` rather than `i64::from`, deliberately. Both are the same
        // value-preserving zero-extension of a `u32` for every input, but
        // `<i64 as From<u32>>::from` is an ABSENT CALLEE to the deductive verifier
        // (its body is not in the lowered bundle), so the result is havoc'd to a
        // fresh symbolic, the `u32` range link is lost, and the following add is
        // encoded as satisfiable at `i64::MAX`. MEASURED 2026-08-20 on sealed
        // toolchain trust-e9ca4908: `i64::from(x) + 1` reports
        // `[overflow:add] FAILED (ay-in-process); counterexample:
        // _3 = 9223372036854775807`; `(x as i64) + 1` reports PROVED. The cast
        // form lowers as a widening the encoder can see through. Clippy's
        // `cast_lossless` is allowed workspace-wide (Cargo.toml:180), so this is
        // not lint-suppressed, and `trivial_numeric_casts` does not apply to a
        // widening cast. If a future toolchain models the `From` impl, either
        // spelling proves and this comment can go.
        let var_1indexed = (self.variable().id() as i64) + 1;
        if self.is_positive() {
            var_1indexed
        } else {
            -var_1indexed
        }
    }
}

impl std::fmt::Display for Literal {
    /// Format as DIMACS signed integer. Uses `i64` internally to handle
    /// extension variables that exceed `i32::MAX` (#5327).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_dimacs_i64())
    }
}

/// Bounded model-checking harnesses that PROVE the soundness invariants of the
/// literal encoding (`positive = 2*var`, `negative = 2*var+1`) over all inputs
/// in a tractable range — the formal upgrade of the sample/dense tests in
/// `literal_tests.rs`. A wrong encoding round-trip would silently corrupt a
/// DRAT/LRAT proof checker's clause database, so these are genuine soundness
/// obligations. The harnesses are written in the `kani`-attribute format
/// (`#[cfg(kani)]` gates them out of ordinary builds) but are **executed by
/// Trust's `model-checker-consumer` bounded model checker** (which uses AY itself as its SMT
/// backend), not the standalone `kani` tool. See the
/// `[[trust-verification-toolchain]]` methodology.
#[cfg(kani)]
#[path = "literal/verification.rs"]
mod verification;

#[cfg(test)]
#[path = "literal_tests.rs"]
mod tests;
