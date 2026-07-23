/-
  FAITHFUL, decidable IEEE-754 `to_fp` (narrowing conversion) UNDERFLOW model —
  soundness backing for the two concrete conflict files

    benchmarks/.../fp_tofp_narrow_subnormal_underflow.smt2   (isInfinite, refuted)
    benchmarks/.../fp_tofp_narrow_signed_exponent.smt2       (isNormal,   refuted)

  `AySoundness/FpThy.lean` models the BIT-ENCODING / classification layer but
  explicitly NOT the numeric value of a float nor `to_fp` rounding.  This file
  adds the missing, NON-rounding-fragile piece needed for the two underflow
  conflicts: the EXACT rational (dyadic) magnitude of a source bitpattern per
  IEEE-754, the target-format thresholds (minNormal / smallest-subnormal /
  maxFinite), and a FAITHFUL classifier of the round-toward-negative (`RTN`)
  result — which sidesteps round-to-nearest entirely.

  WHY THIS IS FAITHFUL (and why we do NOT implement a full significand round).
  Every threshold used below (the smallest positive subnormal `subQ`, the
  smallest normal `minNormal`, and `maxFinite`) is itself an EXACTLY-REPRESENTABLE
  grid point of the target format.  `RTN(x)` = the largest representable value
  `≤ x` (round toward −∞).  Because the thresholds are grid points and RTN is
  monotone, the *class* (zero / subnormal / normal / infinite) of `RTN(x)` is
  fixed by where `x` sits relative to those grid points — no significand rounding
  is needed to decide the class:

    * x = 0                          → zero
    * 0 < x < subQ                   → RTN floors to +0            → zero
    * subQ ≤ x < minNormal           → floors to a + subnormal      → subnormal
    * minNormal ≤ x                  → floors to a + normal (≤maxFin, RTN NEVER
                                        rounds a positive up to +∞) → normal
    * −maxFinite ≤ x < 0             → floors to a − subnormal/normal
    * x < −maxFinite                 → no representable ≤ x but −∞  → INFINITE

  The last two lines split at −minNormal: −maxFinite ≤ x ≤ −minNormal → normal,
  −minNormal < x < 0 → subnormal (RTN pushes a tiny negative DOWN to a negative
  subnormal, never to −0).  This asymmetry (positive overflow does NOT go to +∞,
  negative overflow DOES go to −∞) is the defining property of RTN, and the
  reference battery below pins it.

  DECIDABILITY.  Lean-core `Rat` does not kernel-reduce under `decide`
  (`Rat.blt` gets stuck), so every magnitude is a DYADIC value `m · 2^e`
  (`Dy`), and comparisons cross-multiply into `Int` (kernel-accelerated).  All
  proofs are `by decide`; `#print axioms ⊆ {propext, Quot.sound}` (no `sorry`,
  no `native_decide`).

  VALIDATION IS MANDATORY (bounds modelling-bug risk / the §0 wrong-semantics
  hazard): `reference_battery` proves by `decide` that the model reproduces the
  KNOWN-correct IEEE classification for a spread of reference conversions
  (1.0 → normal, a value that overflows to ∞, an underflow to subnormal, an
  underflow to zero, +0 → zero, a mid-range normal, and the exact grid-point
  boundaries).  If any reference were wrong the model would be buggy.

  Pure Lean 4 core (no Mathlib).  HONEST SCOPE: this covers finite `to_fp`
  narrowing under RTN and its zero/subnormal/normal/infinite classification —
  exactly the two underflow conflicts.  It does NOT model NaN propagation,
  round-to-nearest tie-breaking, or fp arithmetic; those are out of scope.
-/
namespace AySoundness.FpUnderflow

/-! ## Dyadic magnitudes (`m · 2^e`), compared in `Int` so `decide` reduces. -/

/-- A signed dyadic rational `m · 2^e` (`e : Int`, so negative exponents are
    exact).  Every value in this file — source magnitudes and target thresholds —
    is dyadic, which is what makes exact comparison kernel-decidable. -/
structure Dy where
  m : Int
  e : Int
deriving DecidableEq, Repr

/-- Multiply an integer by `2^k` (`k : Nat`). -/
def shl (m : Int) (k : Nat) : Int := m * (2 ^ k : Int)

/-- `a < b` as dyadics: shift both to the common lower exponent (a non-negative
    shift) and compare the resulting integers.  For `a = m₁·2^{e₁}`,
    `b = m₂·2^{e₂}`, with `t = min e₁ e₂`, `a < b ⟺ m₁·2^{e₁−t} < m₂·2^{e₂−t}`. -/
def Dy.lt (a b : Dy) : Bool :=
  let t := min a.e b.e
  shl a.m (a.e - t).toNat < shl b.m (b.e - t).toNat

/-- `a ≤ b` as dyadics (same shifting scheme as `Dy.lt`). -/
def Dy.le (a b : Dy) : Bool :=
  let t := min a.e b.e
  shl a.m (a.e - t).toNat ≤ shl b.m (b.e - t).toNat

/-- Negation: `−(m·2^e) = (−m)·2^e`. -/
def Dy.neg (a : Dy) : Dy := ⟨-a.m, a.e⟩

/-! ## Exact IEEE-754 decode of a finite source bitpattern → its dyadic value.

For exponent width `eb` and stored-significand width `sb−1` (so `sb` counts the
hidden bit), `bias = 2^{eb-1} − 1`:

  * subnormal (`expf = 0`):  `(−1)^sign · 2^{1−bias} · (sigf / 2^{sb−1})`
                            = `(−1)^sign · sigf · 2^{2−bias−sb}`,
  * normal    (`expf ≠ 0`):  `(−1)^sign · 2^{expf−bias} · (1 + sigf/2^{sb−1})`
                            = `(−1)^sign · (2^{sb−1}+sigf) · 2^{expf−bias−(sb−1)}`.

(`sb` below is the FULL significand width incl. the hidden bit, matching the SMT
`(_ to_fp eb sb)` where the source `(fp s e m)` has `|m| = sb−1` stored bits.) -/
def decodeFin (eb sb : Nat) (sign : Bool) (expf sigf : Nat) : Dy :=
  let bias : Int := 2 ^ (eb - 1) - 1
  let sgn : Int := if sign then -1 else 1
  if expf = 0 then
    -- subnormal / zero
    ⟨ sgn * (sigf : Int), 2 - bias - (sb : Int) ⟩
  else
    -- normal (this file's sources are finite, non-extreme exponents)
    ⟨ sgn * ((2 ^ (sb - 1) : Int) + (sigf : Int)), (expf : Int) - bias - ((sb : Int) - 1) ⟩

/-! ## Target-format thresholds, each an EXACT grid point. -/

/-- Smallest positive normal, `2^{1−bias}`. -/
def minNormalD (eb _sb : Nat) : Dy := ⟨1, 1 - (2 ^ (eb - 1) - 1 : Int)⟩

/-- Smallest positive subnormal (the quantum), `2^{2−bias−sb}`. -/
def subQD (eb sb : Nat) : Dy := ⟨1, 2 - (2 ^ (eb - 1) - 1 : Int) - (sb : Int)⟩

/-- Largest finite, `2^{bias}·(2 − 2^{−(sb−1)}) = (2^{sb} − 1)·2^{bias−sb+1}`. -/
def maxFinD (eb sb : Nat) : Dy := ⟨(2 ^ sb : Int) - 1, (2 ^ (eb - 1) - 1 : Int) - (sb : Int) + 1⟩

/-! ## The RTN classifier — the faithful, decidable heart of the model. -/

/-- IEEE class of a finite `to_fp` result. -/
inductive FClass
  | zero | subnormal | normal | infinite
deriving DecidableEq, Repr

/-- Class of `RTN(v)` when converting the exact dyadic value `v` into the target
    format `(eb, sb)`, per the grid-point / monotonicity argument in the header.
    `v.m`'s sign is exactly the sign of the value (since `2^e > 0`). -/
def classifyRTN (eb sb : Nat) (v : Dy) : FClass :=
  let mn := minNormalD eb sb
  let sq := subQD eb sb
  let mx := maxFinD eb sb
  if v.m = 0 then FClass.zero
  else if v.m > 0 then
    -- positive: RTN floors toward 0; NEVER overflows up to +∞
    if Dy.lt v sq then FClass.zero
    else if Dy.lt v mn then FClass.subnormal
    else FClass.normal
  else
    -- negative: RTN floors toward −∞; overflows to −∞ below −maxFinite
    if Dy.lt v (Dy.neg mx) then FClass.infinite
    else if Dy.le v (Dy.neg mn) then FClass.normal
    else FClass.subnormal

/-- Is the RTN result an infinity? -/
def isInf (c : FClass) : Bool := match c with | .infinite => true | _ => false
/-- Is the RTN result a normal number? -/
def isNorm (c : FClass) : Bool := match c with | .normal => true | _ => false

/-! ## VALIDATION — reference battery (KNOWN-correct classifications).

If ANY line here failed to `decide`, the model would be mis-classifying a known
conversion and must not be trusted.  Target `(4,4)` unless noted: `bias = 7`,
`subQ = 2^{-9}`, `minNormal = 2^{-6}`, `maxFinite = 240`. -/

/-- `1.0 → normal`. -/
theorem ref_one_normal : classifyRTN 4 4 ⟨1, 0⟩ = FClass.normal := by decide
/-- A mid-range value `1.5 → normal`. -/
theorem ref_mid_normal : classifyRTN 4 4 ⟨3, -1⟩ = FClass.normal := by decide
/-- Exactly `minNormal` (`2^{-6}`) is normal (boundary is a normal grid point). -/
theorem ref_minNormal_boundary : classifyRTN 4 4 ⟨1, -6⟩ = FClass.normal := by decide
/-- Exactly `maxFinite` (`240`) is normal, NOT infinite. -/
theorem ref_maxFinite_normal : classifyRTN 4 4 ⟨15, 4⟩ = FClass.normal := by decide

/-- A large NEGATIVE value `−1000 < −maxFinite` overflows to −∞ under RTN. -/
theorem ref_neg_overflow_inf : classifyRTN 4 4 ⟨-1000, 0⟩ = FClass.infinite := by decide
/-- FAITHFULNESS OF RTN's ASYMMETRY: a large POSITIVE value `300 > maxFinite`
    does NOT overflow to +∞ under RTN — it floors to `maxFinite` (normal). -/
theorem ref_pos_overflow_not_inf : isInf (classifyRTN 4 4 ⟨300, 0⟩) = false := by decide
theorem ref_pos_overflow_normal : classifyRTN 4 4 ⟨300, 0⟩ = FClass.normal := by decide

/-- Underflow to SUBNORMAL: `2^{-8}` (between `subQ = 2^{-9}` and `minNormal`). -/
theorem ref_underflow_subnormal : classifyRTN 4 4 ⟨1, -8⟩ = FClass.subnormal := by decide
/-- Underflow to ZERO: `2^{-12} < subQ` floors to +0 under RTN. -/
theorem ref_underflow_zero : classifyRTN 4 4 ⟨1, -12⟩ = FClass.zero := by decide
/-- A small NEGATIVE value `−2^{-10}` (`|·| < minNormal`) → negative subnormal,
    NOT zero (RTN rounds down, away from 0). -/
theorem ref_neg_underflow_subnormal : classifyRTN 4 4 ⟨-1, -10⟩ = FClass.subnormal := by decide

/-- `+0 → zero`; a zero is neither normal nor infinite. -/
theorem ref_zero : classifyRTN 4 4 ⟨0, 0⟩ = FClass.zero := by decide
theorem ref_zero_not_normal : isNorm (classifyRTN 4 4 ⟨0, 0⟩) = false := by decide
theorem ref_zero_not_inf : isInf (classifyRTN 4 4 ⟨0, 0⟩) = false := by decide

/-- The whole reference battery as one kernel-checked bundle: if this holds, the
    model reproduces every known-correct reference classification. -/
theorem reference_battery :
    classifyRTN 4 4 ⟨1, 0⟩ = FClass.normal ∧
    classifyRTN 4 4 ⟨3, -1⟩ = FClass.normal ∧
    classifyRTN 4 4 ⟨1, -6⟩ = FClass.normal ∧
    classifyRTN 4 4 ⟨15, 4⟩ = FClass.normal ∧
    classifyRTN 4 4 ⟨-1000, 0⟩ = FClass.infinite ∧
    isInf (classifyRTN 4 4 ⟨300, 0⟩) = false ∧
    classifyRTN 4 4 ⟨300, 0⟩ = FClass.normal ∧
    classifyRTN 4 4 ⟨1, -8⟩ = FClass.subnormal ∧
    classifyRTN 4 4 ⟨1, -12⟩ = FClass.zero ∧
    classifyRTN 4 4 ⟨-1, -10⟩ = FClass.subnormal ∧
    classifyRTN 4 4 ⟨0, 0⟩ = FClass.zero := by decide

/-! ## Cross-format thresholds also validated at the target of conflict A. -/

/-- Target `(3,5)` of conflict A: `bias = 3`, `maxFinite = 15.5`, `minNormal = 1/4`.
    Sanity: `1.0 → normal`, `10 → normal`, `−20 < −maxFinite → infinite`. -/
theorem ref35_one_normal : classifyRTN 3 5 ⟨1, 0⟩ = FClass.normal := by decide
theorem ref35_neg_overflow_inf : classifyRTN 3 5 ⟨-20, 0⟩ = FClass.infinite := by decide
theorem ref35_pos_overflow_not_inf : isInf (classifyRTN 3 5 ⟨20, 0⟩) = false := by decide

/-! ## The two concrete underflow conflicts.

Source magnitudes are produced by the general `decodeFin`, so `decide` reduces
the exact IEEE decode as well — no hand-computed mantissa/exponent. -/

/-- Source of `fp_tofp_narrow_subnormal_underflow.smt2`:
    `(fp #b1 #b00000 #b0010000)` in format `eb=5, sb=8` — a NEGATIVE subnormal.
    Its exact value is `−16 · 2^{−21} = −2^{−17}`. -/
def srcA : Dy := decodeFin 5 8 true 0 0b0010000

/-- Cross-check the decode: `srcA` is exactly `−16 · 2^{−21}`. -/
theorem srcA_value : srcA = ⟨-16, -21⟩ := by decide

/-- Source of `fp_tofp_narrow_signed_exponent.smt2`:
    `(fp #b0 #b01000110 #b10100000111101000011111)` in format `eb=8, sb=24`
    (single precision) — a POSITIVE normal with unbiased exponent `70−127=−57`.
    Its exact value is `(2^{23}+5274143) · 2^{−80} ≈ 2^{−57}`. -/
def srcB : Dy := decodeFin 8 24 false 70 0b10100000111101000011111

/-- Cross-check the decode: `srcB = (2^{23}+5274143)·2^{−80}`. -/
theorem srcB_value : srcB = ⟨2 ^ 23 + 5274143, -80⟩ := by decide

/-- **Conflict A — NOT infinite.**  Converting `srcA` (`|srcA| = 2^{−17}`, far
    below `maxFinite(3,5) = 15.5`) into `(_ to_fp 3 5) RTN` does NOT yield an
    infinity: `srcA` is a negative value with `srcA > −maxFinite`, so RTN floors
    it to a finite (subnormal) result.  This refutes `fp.isInfinite(...)`,
    matching AY's `unsat`. -/
theorem conflictA_not_infinite : isInf (classifyRTN 3 5 srcA) = false := by decide

/-- The RTN result of conflict A is in fact a (negative) subnormal. -/
theorem conflictA_class : classifyRTN 3 5 srcA = FClass.subnormal := by decide

/-- **Conflict B — NOT normal.**  Converting `srcB` (`|srcB| ≈ 2^{−57}`, far
    below `minNormal(4,4) = 2^{−6}`, indeed below `subQ(4,4) = 2^{−9}`) into
    `(_ to_fp 4 4) RTN` underflows: RTN floors it to `+0`, which is not normal.
    This refutes `fp.isNormal(...)`, matching AY's `unsat`. -/
theorem conflictB_not_normal : isNorm (classifyRTN 4 4 srcB) = false := by decide

/-- The RTN result of conflict B is in fact `zero` (underflow past `subQ`). -/
theorem conflictB_class : classifyRTN 4 4 srcB = FClass.zero := by decide

/-- Both concrete conflicts, bundled: the model classifies exactly as AY's two
    `unsat` verdicts require — `srcA → not infinite`, `srcB → not normal`. -/
theorem conflicts_match_ay :
    isInf (classifyRTN 3 5 srcA) = false ∧ isNorm (classifyRTN 4 4 srcB) = false := by decide

/-! ## FAITHFUL IEEE-754 `fp.rem` + `fp.isNegative`  (rank6_qf_fp).

Target file `rank6_qf_fp`:

    (fp.isNegative
      (fp.rem (fp #b1 #b11110 #b1111100110)      -- eb=5, sb=11 : a
              (fp #b1 #b00000 #b1001101111)))     -- eb=5, sb=11 : b   → AY = unsat

IEEE-754 / SMT-LIB `fp.rem a b` semantics (for finite `a`, finite `b ≠ 0`):

    r  =  a − n·b ,   n = roundNearestEven(a / b)   (nearest INTEGER, ties to even)

and `r` is **EXACT** — no rounding is applied to the difference.  Because `a` and
`b` are dyadic, `a/b` is rational, `n` is an integer, and `r` is again dyadic, so
the whole computation stays inside the exact `Dy`/`Int` model and reduces under
`decide`.  We never touch round-to-nearest of a *float* significand here — the
only rounding is `a/b` → nearest integer, done in `Int` by cross-multiplication.

`fp.isNegative` (SMT-LIB): true iff the result's sign bit is 1 and it is not NaN
— crucially this is **sign-bit** based, so `fp.isNegative(−0) = true` while
`fp.isNegative(+0) = false`.  IEEE-754 fixes the sign of a zero `fp.rem` result
to the sign of the DIVIDEND `a` ("If r = 0, its sign shall be that of x").  We
thread `a`'s sign into `remIsNegative` so the ±0 boundary is modelled faithfully
(the reference battery pins both `+0` and `−0` cases). -/

/-- Subtract dyadics exactly: shift both to the common lower exponent `t` and
    subtract the integer significands.  `a − b = (a.m·2^{a.e−t} − b.m·2^{b.e−t})·2^t`. -/
def Dy.sub (a b : Dy) : Dy :=
  let t := min a.e b.e
  ⟨ shl a.m (a.e - t).toNat - shl b.m (b.e - t).toNat, t ⟩

/-- Scale a dyadic by an integer `k`: `k·(m·2^e) = (k·m)·2^e`. -/
def Dy.mulInt (k : Int) (a : Dy) : Dy := ⟨ k * a.m, a.e ⟩

/-- Round `N/D` (`D ≠ 0`) to the nearest integer, ties to EVEN.  Normalise so the
    denominator is positive (`D>0`); then `fl = ⌊N/D⌋` (floor division, valid for
    any sign of `N`) and `r = N − fl·D ∈ [0,D)`.  Compare `2r` with `D`:
    `2r<D → fl`, `2r>D → fl+1`, and on the exact half (`2r=D`) pick the even
    neighbour.  All in `Int`, so `decide` reduces it. -/
def roundNE (N D : Int) : Int :=
  let N := if D < 0 then -N else N
  let D := if D < 0 then -D else D
  let fl := Int.fdiv N D
  let r  := N - fl * D                 -- 0 ≤ r < D
  if 2 * r < D then fl
  else if 2 * r > D then fl + 1
  else if fl % 2 == 0 then fl else fl + 1

/-- EXACT `fp.rem a b` value (finite `a`, finite `b ≠ 0`): `r = a − n·b` with
    `n = roundNearestEven(a/b)`.  Form the ratio `a/b = N/D` in `Int`
    (`a/b = (m_a·2^{e_a})/(m_b·2^{e_b})`, cleared to `Int` by the exponent
    difference `de = e_a − e_b`), round to nearest even, then subtract exactly. -/
def remDy (a b : Dy) : Dy :=
  let de := a.e - b.e
  let N := if de ≥ 0 then shl a.m de.toNat else a.m
  let D := if de ≥ 0 then b.m else shl b.m (-de).toNat
  let n := roundNE N D
  Dy.sub a (Dy.mulInt n b)

/-- `fp.isNegative (fp.rem a b)`, `signA` = sign bit of the dividend `a`.  A
    non-zero result is negative iff its value (`= r.m`, since `2^e>0`) is `< 0`.
    A zero result is `±0` with the dividend's sign, and `fp.isNegative(−0)=true`,
    `fp.isNegative(+0)=false` — so it is negative exactly when `signA` is set. -/
def remIsNegative (signA : Bool) (a b : Dy) : Bool :=
  let r := remDy a b
  if r.m < 0 then true
  else if r.m > 0 then false
  else signA

/-! ### VALIDATION — reference battery for `fp.rem` / `fp.isNegative`.

Each line is a KNOWN-correct IEEE-754 `fp.rem` fact (value AND sign).  If any
failed to `decide`, the model would be mis-computing a known remainder and must
not be trusted for the rank6 conflict. -/

/-- `rem(5,3) = −1`   (`5/3 ≈ 1.67 → n=2`, `5 − 6 = −1`)  → NEGATIVE. -/
theorem rem_5_3_val : remDy ⟨5,0⟩ ⟨3,0⟩ = ⟨-1,0⟩ := by decide
theorem rem_5_3_neg : remIsNegative false ⟨5,0⟩ ⟨3,0⟩ = true := by decide
/-- `rem(5,2) = +1`   (`5/2 = 2.5` ties-to-EVEN → `n=2`, `5 − 4 = 1`)  → not negative. -/
theorem rem_5_2_val : remDy ⟨5,0⟩ ⟨2,0⟩ = ⟨1,0⟩ := by decide
theorem rem_5_2_neg : remIsNegative false ⟨5,0⟩ ⟨2,0⟩ = false := by decide
/-- `rem(−5,3) = +1`  (`−5/3 ≈ −1.67 → n=−2`, `−5 − (−6) = 1`)  → not negative. -/
theorem rem_neg5_3_val : remDy ⟨-5,0⟩ ⟨3,0⟩ = ⟨1,0⟩ := by decide
theorem rem_neg5_3_neg : remIsNegative true ⟨-5,0⟩ ⟨3,0⟩ = false := by decide
/-- `rem(7,2) = −1`   (`7/2 = 3.5` ties-to-EVEN → `n=4`, `7 − 8 = −1`)  → NEGATIVE. -/
theorem rem_7_2_val : remDy ⟨7,0⟩ ⟨2,0⟩ = ⟨-1,0⟩ := by decide
theorem rem_7_2_neg : remIsNegative false ⟨7,0⟩ ⟨2,0⟩ = true := by decide
/-- `rem(x,x) = +0`   (`x=5`, `n=1`, `5 − 5 = 0`; dividend `+` → `+0`)  → not negative. -/
theorem rem_x_x_val : remDy ⟨5,0⟩ ⟨5,0⟩ = ⟨0,0⟩ := by decide
theorem rem_x_x_neg : remIsNegative false ⟨5,0⟩ ⟨5,0⟩ = false := by decide
/-- `rem(6,3) = +0`   (exact; dividend `+` → `+0`, sign bit 0)  → not negative. -/
theorem rem_6_3_neg : remIsNegative false ⟨6,0⟩ ⟨3,0⟩ = false := by decide
/-- `rem(−6,3) = −0`  (exact; dividend `−` → `−0`).  `fp.isNegative(−0)=true` — the
    sign-bit semantics of the ±0 boundary. -/
theorem rem_neg6_3_val : remDy ⟨-6,0⟩ ⟨3,0⟩ = ⟨0,0⟩ := by decide
theorem rem_neg6_3_neg : remIsNegative true ⟨-6,0⟩ ⟨3,0⟩ = true := by decide

/-- The whole `fp.rem` reference battery as one kernel-checked bundle. -/
theorem rem_reference_battery :
    remDy ⟨5,0⟩ ⟨3,0⟩ = ⟨-1,0⟩ ∧ remIsNegative false ⟨5,0⟩ ⟨3,0⟩ = true ∧
    remDy ⟨5,0⟩ ⟨2,0⟩ = ⟨1,0⟩ ∧ remIsNegative false ⟨5,0⟩ ⟨2,0⟩ = false ∧
    remDy ⟨-5,0⟩ ⟨3,0⟩ = ⟨1,0⟩ ∧ remIsNegative true ⟨-5,0⟩ ⟨3,0⟩ = false ∧
    remDy ⟨7,0⟩ ⟨2,0⟩ = ⟨-1,0⟩ ∧ remIsNegative false ⟨7,0⟩ ⟨2,0⟩ = true ∧
    remDy ⟨5,0⟩ ⟨5,0⟩ = ⟨0,0⟩ ∧ remIsNegative false ⟨5,0⟩ ⟨5,0⟩ = false ∧
    remIsNegative false ⟨6,0⟩ ⟨3,0⟩ = false ∧
    remDy ⟨-6,0⟩ ⟨3,0⟩ = ⟨0,0⟩ ∧ remIsNegative true ⟨-6,0⟩ ⟨3,0⟩ = true := by decide

/-! ### The rank6 concrete conflict.

Both operands share format `eb=5, sb=11` (5 exponent bits, 10 stored significand
bits + hidden bit).  Decoded exactly by the general `decodeFin` — no hand mantissa. -/

/-- `a = (fp #b1 #b11110 #b1111100110)` — a NEGATIVE normal; `sign=1`, `expf=30`,
    `sigf=998`, unbiased exponent `30−15=15`.  Exact value `−2022·2^5 = −64704`. -/
def rank6_a : Dy := decodeFin 5 11 true 30 0b1111100110

/-- `b = (fp #b1 #b00000 #b1001101111)` — a NEGATIVE subnormal; `sign=1`, `expf=0`,
    `sigf=623`.  Exact value `−623·2^{−24}`. -/
def rank6_b : Dy := decodeFin 5 11 true 0 0b1001101111

/-- Cross-check the decode of `a`. -/
theorem rank6_a_value : rank6_a = ⟨-2022, 5⟩ := by decide
/-- Cross-check the decode of `b`. -/
theorem rank6_b_value : rank6_b = ⟨-623, -24⟩ := by decide

/-- The EXACT `fp.rem a b`.  `a/b = (2022·2^29)/623` (the two negatives cancel);
    `n = roundNearestEven = 1742460649`; `r = a − n·b = 263·2^{−24}` — a strictly
    POSITIVE value.  (Kernel-checked; no rounding of `r`.) -/
theorem rank6_rem_value : remDy rank6_a rank6_b = ⟨263, -24⟩ := by decide

/-- **rank6 — NOT negative.**  `fp.rem a b = 263·2^{−24} > 0`, so its sign bit is
    0 and `fp.isNegative` is false.  This matches AY's `unsat` for
    `(fp.isNegative (fp.rem a b))`.  `signA=true` (dividend `a`'s sign bit) is
    threaded but irrelevant here since the result is non-zero. -/
theorem rank6_not_negative : remIsNegative true rank6_a rank6_b = false := by decide

/-- The rank6 result bundled to AY's verdict: the exact remainder is positive and
    `fp.isNegative` is false — exactly what AY's `unsat` requires. -/
theorem rank6_matches_ay :
    remDy rank6_a rank6_b = ⟨263, -24⟩ ∧ remIsNegative true rank6_a rank6_b = false := by decide

end AySoundness.FpUnderflow
