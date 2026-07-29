/-
  THE SEMANTIC BRIDGE for the QF_FPLRA `guard_claim_*` benchmarks: from
  IEEE-754 binary64 round-to-nearest to the abstract half-ULP (`close` /
  `qround`) model of `AySoundness/FpErrorBound.lean`.

  ###########################################################################
  READ THIS FIRST — WHAT THIS FILE DOES **NOT** ESTABLISH.

  This module proves the RATIONAL side of the `guard_claim_*` argument in full,
  and nothing else. There remains exactly ONE step between it and the SMT-LIB
  formula, and that step is NOT a theorem:

      the identification of SMT-LIB `fp.mul RNE` / `fp.add RNE`, read through
      `fp.to_real`, with the `NearestF64` specification defined below.

  That identification is HAND-ARGUED and lives OUTSIDE the Lean kernel. It is
  categorically larger than the `Int`↔`Int` identifications the other
  `lean_firewall.rs` emitters make, because ay's floating-point verdicts come
  from a BIT-BLASTER, not from a nearest-value definition — so a certificate
  resting on it would be checking the solver against a restatement of the
  semantics the solver itself implements, which is precisely what a firewall
  exists NOT to do.

  Consequently `emit_fp_dot_error_bound_firewall_lean_from_parsed`
  (`crates/ay-dpll/src/executor/lean_firewall.rs`) is DELIBERATELY FAIL-CLOSED
  and emits nothing. This module is the discharged prerequisite, not a shipped
  proof pipeline. Do not read `guard_claim_no_model` as certifying
  `benchmarks/smt/QF_FPLRA/guard_claim_guard2.smt2`; it certifies the rational
  model of that benchmark.
  ###########################################################################

  WHAT IS PROVED HERE (nothing is axiomatized):

  * `IsF64` — a division-free SUBSET of the finite Float64 values:
    `{ M · 2^(-k) : |M| ≤ 2^53, k ≤ 1074 }`.  Using a SUBSET is the soundness
    direction that matters: the rounding hypothesis below quantifies over
    `IsF64`, so a smaller set makes the hypothesis WEAKER, hence *implied by*
    (never stronger than) the IEEE-754 fact.

  * `NearestF64 r x` — the rounding spec: *if* `|x|` is far below the overflow
    threshold, `r` is at least as close to `x` as any `IsF64` point.  This is
    exactly what SMT-LIB's `fp.mul RNE` / `fp.add RNE` guarantee for a finite,
    non-overflowing result (ties-to-even is *a* nearest choice, so the spec is
    tie-rule agnostic and also covers RNA).

  * `rne_step` — THE BRIDGE.  For a grid spacing `u = 1/2^k` and cap
    `M = 2^53·u` (a power of two): if `|x| ≤ M` then the rounded value `r`
    satisfies BOTH
      (i)  `close r x u`   (i.e. `|r − x| ≤ u/2`, the half-ULP bound), and
      (ii) `|r| ≤ M`       (the monotone cap the Rust tactic gets from
                            representable-endpoint clamping).
    Proof: the nearest grid point `qround u x` is itself representable
    (`grid_isF64`), so the true rounded value cannot be further away than it —
    and `half_ulp` (already proven in `FpErrorBound`) bounds the grid point.
    NO binade case analysis, NO subnormal case, NO exactness-at-boundary
    argument is needed: the bound is an ABSOLUTE half-ULP-at-the-cap bound,
    which is automatically valid in the subnormal regime (finer grid) too.

  * `isF64_representable` — SUBSET-NESS AS A THEOREM, not a `decide` battery.
    `NearestF64` quantifies over `IsF64`, so a single non-representable point
    inside `IsF64` would make the rounding hypothesis STRONGER than the
    IEEE-754 fact and the whole certificate unsound.  Proved against the
    INDEPENDENT, reference-battery-validated decode
    `AySoundness.FpUnderflow.decodeFin 11 53`: every `IsF64` point is exactly
    the value of some finite binary64 bit pattern (`expf ≤ 2046`, so never the
    NaN/∞ exponent field; `sigf < 2⁵²`).

  * `guard_claim_intermediates_finite` — CHAINED FINITENESS as its own stated
    obligation.  `fp.isNormal` is asserted only on the seven LEAVES, and
    `fp.to_real` is unspecified on NaN/±∞, so the six intermediates' finiteness
    has to be DERIVED rather than assumed.  It is: each stays at or below
    `2⁵¹`, nine binades under the `OVF = 2⁶⁰` guard and 972 under the binary64
    overflow threshold.

  * `guard_claim_no_model` — the composed conflict for the actual benchmark
    shape: seven binary64 inputs with `|nᵢ| ≤ 1`, `|pᵢ|, |d| ≤ 2⁴⁸`, the exact
    six-operation RNE evaluation, and the refuted claim
    `rf − exact_dot ≥ tnum/tden`.  Certified accumulated bound: `17/64`.

  Pure Lean 4 core + `Std` (`grind`, `omega`, `simp`, `decide`); no Mathlib,
  no `Real`, no `native_decide`, no `sorry`.
-/
import AySoundness.FpErrorBound
import AySoundness.FpUnderflow
import AySoundness.Firewall

namespace AySoundness.FpBridge

open AySoundness.FpErrorBound
open AySoundness.FpUnderflow (Dy decodeFin)

/-! ## Absolute-value helpers (fraction-free, core `Rat` only). -/

/-- `|a| ≤ c`, encoded without division. -/
def AbsLe (a c : Rat) : Prop := -c ≤ a ∧ a ≤ c

/-- Absolute value on `Rat` (core has none). -/
def ratAbs (a : Rat) : Rat := if a < 0 then -a else a

theorem absLe_of_ratAbs_le {a c : Rat} (h : ratAbs a ≤ c) : AbsLe a c := by
  unfold ratAbs at h; unfold AbsLe; grind

theorem ratAbs_le_of_absLe {a c : Rat} (h : AbsLe a c) : ratAbs a ≤ c := by
  obtain ⟨h1, h2⟩ := h; unfold ratAbs; grind

theorem ratAbs_two (a : Rat) : ratAbs (2 * a) = 2 * ratAbs a := by
  unfold ratAbs; grind

theorem absLe_mono {a c d : Rat} (h : AbsLe a c) (hcd : c ≤ d) : AbsLe a d := by
  obtain ⟨h1, h2⟩ := h; unfold AbsLe; grind

theorem absLe_add {a b c d e : Rat} (ha : AbsLe a c) (hb : AbsLe b d)
    (he : c + d ≤ e) : AbsLe (a + b) e := by
  obtain ⟨h1, h2⟩ := ha; obtain ⟨h3, h4⟩ := hb; unfold AbsLe; grind

/-- `close a b c` (from `FpErrorBound`) is exactly `AbsLe (2*(a-b)) c`. -/
theorem close_iff_absLe {a b c : Rat} : close a b c ↔ AbsLe (2 * (a - b)) c := Iff.rfl

/-! ## Int → Rat cast helpers. -/

theorem intCast_pos {c : Int} (h : 0 < c) : (0 : Rat) < (c : Rat) := by
  have h2 := (Rat.intCast_lt_intCast (a := 0) (b := c)).mpr h
  simpa using h2

theorem intCast_le {a b : Int} (h : a ≤ b) : ((a : Int) : Rat) ≤ ((b : Int) : Rat) :=
  Rat.intCast_le_intCast.mpr h

/-! ## The Float64 representable subset and the RNE rounding spec. -/

/-- A DIVISION-FREE subset of the FINITE Float64 values:
    `y = M · 2^(−k)` with `|M| ≤ 2^53` and `k ≤ 1074`.

    Every such `y` really is a finite Float64: writing `M = m·2^t` with `m` odd,
    `|m| ≤ 2^53` and the exponent `t − k ≥ −1074`, so `y` is a normal or
    subnormal double (`|M| = 2^53` is a power of two, hence also representable),
    and `|y| ≤ 2^53 ≤ maxFinite`.  Being a SUBSET is what soundness needs:
    `NearestF64` quantifies over it, so the hypothesis is implied by (weaker
    than) the true IEEE nearest-rounding fact. -/
def IsF64 (y : Rat) : Prop :=
  ∃ (M : Int) (k : Nat), M.natAbs ≤ 2 ^ 53 ∧ k ≤ 1074 ∧ y * ((2 ^ k : Int) : Rat) = (M : Rat)

/-- Overflow guard: `2^60`, far below the Float64 RNE overflow threshold
    `(2 − 2^(−53))·2^1023`. -/
def OVF : Rat := ((1152921504606846976 : Int) : Rat)

/-- **The rounding spec.**  `r` is the RNE rounding of the exact value `x`:
    provided `|x|` stays below the overflow guard, `r` is at least as close to
    `x` as ANY representable value.

    This is exactly the SMT-LIB semantics of `fp.mul RNE` / `fp.add RNE`
    composed with `fp.to_real` when the result is finite — and the overflow
    guard makes finiteness automatic.  It is tie-rule agnostic (ties-to-even is
    a nearest value), so it is also valid for `RNA`. -/
def NearestF64 (r x : Rat) : Prop :=
  AbsLe x OVF → ∀ y : Rat, IsF64 y → ratAbs (r - x) ≤ ratAbs (y - x)

/-- Every point of the uniform grid of spacing `u = 1/2^k` with index
    `|j| ≤ 2^53` is representable. -/
theorem grid_isF64 {c : Int} {k : Nat} (hk : k ≤ 1074) (hc : c = 2 ^ k) {u : Rat}
    (hu : u * (c : Rat) = 1) {j : Int} (hj : j.natAbs ≤ 2 ^ 53) :
    IsF64 ((j : Rat) * u) := by
  refine ⟨j, k, hj, hk, ?_⟩
  subst hc
  rw [Rat.mul_assoc, hu, Rat.mul_one]

/-! ## The half-ULP bound at an arbitrary grid, with no division. -/

/-- `half_ulp` restated without `/`: if `q * u = x` then the grid point
    `(nearestInt q) * u` is within `u/2` of `x`. -/
theorem half_ulp_gen (u q x : Rat) (hu : 0 < u) (hq : q * u = x) :
    close ((nearestInt q : Rat) * u) x u := by
  have hle0 : (0 : Rat) ≤ u := Rat.le_of_lt hu
  have hunit := unit_half_ulp q
  have hval : 2 * ((nearestInt q : Rat) * u - x) = (2 * ((nearestInt q : Rat) - q)) * u := by
    rw [Rat.mul_assoc, sub_mul, hq]
  unfold close
  rw [hval]
  refine ⟨?_, ?_⟩
  · have h := Rat.mul_le_mul_of_nonneg_right hunit.1 hle0
    rwa [Rat.neg_mul, Rat.one_mul] at h
  · have h := Rat.mul_le_mul_of_nonneg_right hunit.2 hle0
    rwa [Rat.one_mul] at h

/-- The nearest integer to `q` stays inside `[-N, N]` when `q` does. -/
theorem nearestInt_bounds (q : Rat) (N : Int) (hlo : -((N : Int) : Rat) ≤ q)
    (hhi : q ≤ ((N : Int) : Rat)) : -N ≤ nearestInt q ∧ nearestInt q ≤ N := by
  have hfl_le_q : ((Rat.floor q : Int) : Rat) ≤ q := Rat.floor_le q
  have hfl_lo : -N ≤ Rat.floor q := by
    rw [Rat.le_floor_iff]
    have : ((-N : Int) : Rat) = -((N : Int) : Rat) := by push_cast; rfl
    rw [this]; exact hlo
  unfold nearestInt
  by_cases hc : 2 * (q - ((Rat.floor q : Int) : Rat)) ≤ 1
  · rw [if_pos hc]
    refine ⟨hfl_lo, ?_⟩
    exact Rat.intCast_le_intCast.mp (Rat.le_trans hfl_le_q hhi)
  · rw [if_neg hc]
    have hgt : ((Rat.floor q : Int) : Rat) < q := by
      have hc' : (1 : Rat) < 2 * (q - ((Rat.floor q : Int) : Rat)) := Rat.not_le.mp hc
      grind
    have hltR : ((Rat.floor q : Int) : Rat) < ((N : Int) : Rat) := by grind
    have hlt : Rat.floor q < N := Rat.intCast_lt_intCast.mp hltR
    omega

/-! ## THE BRIDGE: one RNE-rounded operation. -/

/-- **Bridge lemma.**  `c = 2^k` is the reciprocal grid scale (`u = 1/c`),
    `Mi = 2^53 / c` the magnitude cap (a power of two, hence representable).
    If the exact value `x` satisfies `|x| ≤ Mi`, then the RNE-rounded value `r`
    obeys the half-ULP bound `close r x u` AND the cap `|r| ≤ Mi`.

    Valid for normal, subnormal and zero results alike: the bound is absolute
    (half the spacing at the CAP binade), and the true grid at smaller
    magnitudes is only finer. -/
theorem rne_step {c : Int} {k : Nat} (hk : k ≤ 1074) (hc : c = 2 ^ k) (hcpos : 0 < c)
    {u : Rat} (hu : u * (c : Rat) = 1)
    {Mi : Int} (hMi : Mi * c = 2 ^ 53) (hMiovf : Mi ≤ 1152921504606846976)
    {x r : Rat} (hx : AbsLe x ((Mi : Int) : Rat)) (hr : NearestF64 r x) :
    close r x u ∧ AbsLe r ((Mi : Int) : Rat) := by
  have hcR : (0 : Rat) < (c : Rat) := intCast_pos hcpos
  have hcR0 : (0 : Rat) ≤ (c : Rat) := Rat.le_of_lt hcR
  have hune : u ≠ 0 := by
    intro h0; rw [h0, Rat.zero_mul] at hu; exact absurd hu (by decide)
  have hupos : 0 < u := by
    rcases Rat.le_total (a := u) (b := 0) with h | h
    · exfalso
      have hle : u * (c : Rat) ≤ 0 * (c : Rat) := Rat.mul_le_mul_of_nonneg_right h hcR0
      rw [hu, Rat.zero_mul] at hle
      exact absurd hle (by decide)
    · exact Rat.lt_iff_le_and_ne.mpr ⟨h, fun he => hune he.symm⟩
  -- the overflow guard is discharged from the cap
  have hguard : AbsLe x OVF := by
    refine absLe_mono hx ?_
    exact intCast_le hMiovf
  -- the grid index of x
  obtain ⟨q, hqdef⟩ : ∃ q : Rat, q = x * (c : Rat) := ⟨_, rfl⟩
  have hq : q * u = x := by
    rw [hqdef, Rat.mul_assoc, Rat.mul_comm (c : Rat) u, hu, Rat.mul_one]
  -- |q| ≤ 2^53
  have hMc : ((Mi : Int) : Rat) * (c : Rat) = ((2 ^ 53 : Int) : Rat) := by
    rw [← Rat.intCast_mul, hMi]
  have hqb : AbsLe q (((2 ^ 53 : Int) : Rat)) := by
    obtain ⟨h1, h2⟩ := hx
    constructor
    · have := Rat.mul_le_mul_of_nonneg_right h1 hcR0
      rw [Rat.neg_mul, hMc] at this
      rw [hqdef]; exact this
    · have := Rat.mul_le_mul_of_nonneg_right h2 hcR0
      rw [hMc] at this
      rw [hqdef]; exact this
  -- the nearest grid point is representable
  have hjb := nearestInt_bounds q (2 ^ 53) hqb.1 hqb.2
  have hjabs : (nearestInt q).natAbs ≤ 2 ^ 53 := by omega
  have hgF : IsF64 ((nearestInt q : Rat) * u) := grid_isF64 hk hc hu hjabs
  have hgclose : close ((nearestInt q : Rat) * u) x u := half_ulp_gen u q x hupos hq
  -- (i) the half-ULP bound transfers to r
  have hcmp := hr hguard _ hgF
  have hgabs : 2 * ratAbs ((nearestInt q : Rat) * u - x) ≤ u := by
    have := ratAbs_le_of_absLe (close_iff_absLe.mp hgclose)
    rwa [ratAbs_two] at this
  have hclose : close r x u := by
    refine close_iff_absLe.mpr ?_
    refine absLe_of_ratAbs_le ?_
    rw [ratAbs_two]
    have h2 : 2 * ratAbs (r - x) ≤ 2 * ratAbs ((nearestInt q : Rat) * u - x) :=
      Rat.mul_le_mul_of_nonneg_left hcmp (by decide)
    exact Rat.le_trans h2 hgabs
  -- (ii) the cap: ±Mi are themselves representable grid points
  have hMiu : ((Mi : Int) : Rat) = ((2 ^ 53 : Int) : Rat) * u := by
    have : ((Mi : Int) : Rat) * ((c : Rat) * u) = ((2 ^ 53 : Int) : Rat) * u := by
      rw [← Rat.mul_assoc, hMc]
    rwa [Rat.mul_comm (c : Rat) u, hu, Rat.mul_one] at this
  have hposF : IsF64 (((2 ^ 53 : Int) : Rat) * u) :=
    grid_isF64 hk hc hu (j := (2 ^ 53 : Int)) (by decide)
  have hnegF : IsF64 ((((-(2 ^ 53) : Int)) : Rat) * u) :=
    grid_isF64 hk hc hu (j := (-(2 ^ 53) : Int)) (by decide)
  have hcmpP := hr hguard _ hposF
  have hcmpN := hr hguard _ hnegF
  have hnegcast : (((-(2 ^ 53) : Int)) : Rat) * u = -(((2 ^ 53 : Int) : Rat) * u) := by
    push_cast; rw [Rat.neg_mul]
  rw [hnegcast, ← hMiu] at hcmpN
  rw [← hMiu] at hcmpP
  have hr1 : r - x ≤ ratAbs (r - x) := by unfold ratAbs; grind
  have hr2 : -(r - x) ≤ ratAbs (r - x) := by unfold ratAbs; grind
  have hP : ratAbs (((Mi : Int) : Rat)) = ((Mi : Int) : Rat) := by
    unfold ratAbs
    have : (0 : Rat) ≤ ((Mi : Int) : Rat) := by
      obtain ⟨h1, h2⟩ := hx; grind
    grind
  have hPx : ratAbs (((Mi : Int) : Rat) - x) = ((Mi : Int) : Rat) - x := by
    unfold ratAbs; obtain ⟨h1, h2⟩ := hx; grind
  have hNx : ratAbs (-((Mi : Int) : Rat) - x) = ((Mi : Int) : Rat) + x := by
    unfold ratAbs; obtain ⟨h1, h2⟩ := hx; grind
  rw [hPx] at hcmpP
  rw [hNx] at hcmpN
  refine ⟨hclose, ?_⟩
  unfold AbsLe
  constructor
  · grind
  · grind

/-! ## The composed `guard_claim` conflict. -/

/-- `2^48`, the asserted position/offset magnitude bound `B`. -/
def B48 : Rat := ((281474976710656 : Int) : Rat)

/-- **The `guard_claim_*` refutation, bridged.**

    Hypotheses are EXACTLY the parsed SMT assertions plus the IEEE-754 rounding
    spec for the six recognized operations:

    * `|nᵢ| ≤ 1`, `|pᵢ| ≤ 2⁴⁸`, `|d| ≤ 2⁴⁸`  (from
      `(and (fp.isNormal v) (<= (fp.to_real (fp.abs v)) BOUND))`);
    * `t1 = fp.mul RNE nx px`, …, `rf = fp.add RNE s2 d`  (as `NearestF64`);
    * the refuted claim `rf − (nx·px + ny·py + nz·pz + d) ≥ tnum/tden`.

    Certified accumulated forward error: `2·|err| ≤ 3u₁ + u₂ + u₃ + u₄ = 17/32`,
    i.e. `|err| ≤ 17/64 = 0.265625`.  Any threshold with `17·tden < 64·tnum`
    (i.e. `> 17/64`) is refuted — which covers `2.0` (`guard_claim_guard2`) and
    `0.3` (`guard_claim_signed_distance`), and correctly FAILS to cover `1e-7`
    (`guard_claim_tight_1e7`, genuinely SAT). -/
theorem guard_claim_no_model
    (nx ny nz px py pz d t1 t2 t3 s1 s2 rf : Rat)
    (u1 u2 u3 u4 : Rat)
    (hu1 : u1 * ((32 : Int) : Rat) = 1) (hu2 : u2 * ((16 : Int) : Rat) = 1)
    (hu3 : u3 * ((8 : Int) : Rat) = 1) (hu4 : u4 * ((4 : Int) : Rat) = 1)
    (hnx : AbsLe nx 1) (hny : AbsLe ny 1) (hnz : AbsLe nz 1)
    (hpx : AbsLe px B48) (hpy : AbsLe py B48) (hpz : AbsLe pz B48) (hd : AbsLe d B48)
    (ht1 : NearestF64 t1 (nx * px)) (ht2 : NearestF64 t2 (ny * py))
    (ht3 : NearestF64 t3 (nz * pz))
    (hs1 : NearestF64 s1 (t1 + t2)) (hs2 : NearestF64 s2 (s1 + t3))
    (hrf : NearestF64 rf (s2 + d))
    (tnum tden : Int) (htden : 0 < tden) (hthr : 17 * tden < 64 * tnum)
    (hclaim : (tnum : Rat) ≤ (tden : Rat) * (rf - (((nx * px + ny * py) + nz * pz) + d))) :
    False := by
  -- products: |nᵢ·pᵢ| ≤ 2⁴⁸
  have hm1 : AbsLe (nx * px) B48 := mul_mag hnx.1 hnx.2 hpx.1 hpx.2
  have hm2 : AbsLe (ny * py) B48 := mul_mag hny.1 hny.2 hpy.1 hpy.2
  have hm3 : AbsLe (nz * pz) B48 := mul_mag hnz.1 hnz.2 hpz.1 hpz.2
  -- the three multiplications round at spacing u₁ = 2⁻⁵ (cap 2⁴⁸)
  have r1 := rne_step (c := 32) (k := 5) (by omega) (by decide) (by decide) hu1
      (Mi := 281474976710656) (by decide) (by decide) hm1 ht1
  have r2 := rne_step (c := 32) (k := 5) (by omega) (by decide) (by decide) hu1
      (Mi := 281474976710656) (by decide) (by decide) hm2 ht2
  have r3 := rne_step (c := 32) (k := 5) (by omega) (by decide) (by decide) hu1
      (Mi := 281474976710656) (by decide) (by decide) hm3 ht3
  -- first sum: |t1+t2| ≤ 2⁴⁹, spacing u₂ = 2⁻⁴
  have hsum1 : AbsLe (t1 + t2) (((562949953421312 : Int) : Rat)) := by
    refine absLe_add r1.2 r2.2 ?_
    show ((281474976710656 : Int) : Rat) + ((281474976710656 : Int) : Rat)
        ≤ ((562949953421312 : Int) : Rat)
    rw [← Rat.intCast_add]; exact intCast_le (by decide)
  have r4 := rne_step (c := 16) (k := 4) (by omega) (by decide) (by decide) hu2
      (Mi := 562949953421312) (by decide) (by decide) hsum1 hs1
  -- second sum: |s1+t3| ≤ 3·2⁴⁸ ≤ 2⁵⁰, spacing u₃ = 2⁻³
  have hsum2 : AbsLe (s1 + t3) (((1125899906842624 : Int) : Rat)) := by
    refine absLe_add r4.2 r3.2 ?_
    show ((562949953421312 : Int) : Rat) + ((281474976710656 : Int) : Rat)
        ≤ ((1125899906842624 : Int) : Rat)
    rw [← Rat.intCast_add]; exact intCast_le (by decide)
  have r5 := rne_step (c := 8) (k := 3) (by omega) (by decide) (by decide) hu3
      (Mi := 1125899906842624) (by decide) (by decide) hsum2 hs2
  -- final sum: |s2+d| ≤ 5·2⁴⁸ ≤ 2⁵¹, spacing u₄ = 2⁻²
  have hsum3 : AbsLe (s2 + d) (((2251799813685248 : Int) : Rat)) := by
    refine absLe_add r5.2 hd ?_
    show ((1125899906842624 : Int) : Rat) + ((281474976710656 : Int) : Rat)
        ≤ ((2251799813685248 : Int) : Rat)
    rw [← Rat.intCast_add]; exact intCast_le (by decide)
  have r6 := rne_step (c := 4) (k := 2) (by omega) (by decide) (by decide) hu4
      (Mi := 2251799813685248) (by decide) (by decide) hsum3 hrf
  -- accumulate the six errors exactly as `dot_error_bound` does
  have h12 : close (t1 + t2) (nx * px + ny * py) (u1 + u1) := close_add r1.1 r2.1 rfl
  have hs1c : close s1 (nx * px + ny * py) (u2 + (u1 + u1)) := close_trans_add r4.1 h12 rfl
  have h123 : close (s1 + t3) ((nx * px + ny * py) + nz * pz) ((u2 + (u1 + u1)) + u1) :=
    close_add hs1c r3.1 rfl
  have hs2c : close s2 ((nx * px + ny * py) + nz * pz) (u3 + ((u2 + (u1 + u1)) + u1)) :=
    close_trans_add r5.1 h123 rfl
  have h123d : close (s2 + d) (((nx * px + ny * py) + nz * pz) + d)
      ((u3 + ((u2 + (u1 + u1)) + u1)) + 0) := close_add hs2c (close_self d) rfl
  have hrfc : close rf (((nx * px + ny * py) + nz * pz) + d)
      (u4 + ((u3 + ((u2 + (u1 + u1)) + u1)) + 0)) := close_trans_add r6.1 h123d rfl
  -- the accumulated spacing is exactly 17/32
  have hC : (32 : Rat) * (u4 + ((u3 + ((u2 + (u1 + u1)) + u1)) + 0)) = 17 := by
    have e1 : u1 * (32 : Rat) = 1 := by simpa using hu1
    have e2 : u2 * (16 : Rat) = 1 := by simpa using hu2
    have e3 : u3 * (8 : Rat) = 1 := by simpa using hu3
    have e4 : u4 * (4 : Rat) = 1 := by simpa using hu4
    grind
  -- 64·err ≤ 17
  have hE : (64 : Rat) * (rf - (((nx * px + ny * py) + nz * pz) + d)) ≤ 17 := by
    have h := hrfc.2
    grind
  -- and the claim forces 64·tnum ≤ 17·tden
  have htdR : (0 : Rat) ≤ (tden : Rat) := Rat.le_of_lt (intCast_pos htden)
  have hmul : (tden : Rat) * ((64 : Rat) * (rf - (((nx * px + ny * py) + nz * pz) + d)))
      ≤ (tden : Rat) * 17 := Rat.mul_le_mul_of_nonneg_left hE htdR
  have hfin : ((64 * tnum : Int) : Rat) ≤ ((17 * tden : Int) : Rat) := by
    push_cast
    have h64 : (0 : Rat) ≤ 64 := by decide
    have hc2 := Rat.mul_le_mul_of_nonneg_left hclaim h64
    grind
  have : (64 * tnum : Int) ≤ (17 * tden : Int) := Rat.intCast_le_intCast.mp hfin
  omega

/-! ## VALIDATION — non-vacuity, instantiation witnesses, threshold gate. -/

theorem ratAbs_nonneg (a : Rat) : 0 ≤ ratAbs a := by unfold ratAbs; grind

/-- `0` is representable. -/
theorem isF64_zero : IsF64 0 := ⟨0, 0, by decide, by decide, by rw [Rat.zero_mul]; rfl⟩

/-- An exactly-representable value rounds to itself, so `NearestF64` is
    INHABITED (the rounding hypothesis is not vacuously unsatisfiable). -/
theorem nearest_self (x : Rat) : NearestF64 x x := by
  intro _ y _
  rw [Rat.sub_self]
  have h0 : ratAbs (0 : Rat) = 0 := by unfold ratAbs; grind
  rw [h0]; exact ratAbs_nonneg _

/-- **NON-VACUITY.**  Every hypothesis of `guard_claim_no_model` EXCEPT the
    refuted claim is simultaneously satisfiable (the all-zero assignment), so
    the theorem is not vacuously true: it is the CLAIM that is refuted. -/
theorem hypotheses_satisfiable :
    AbsLe (0 : Rat) 1 ∧ AbsLe (0 : Rat) B48 ∧
    NearestF64 (0 : Rat) (0 * 0) ∧ NearestF64 (0 : Rat) (0 + 0) := by
  refine ⟨by unfold AbsLe; decide, by unfold AbsLe B48; decide, ?_, ?_⟩
  · rw [Rat.zero_mul]; exact nearest_self 0
  · rw [Rat.add_zero]; exact nearest_self 0

/-- The four grid spacings the emitter must supply (`2⁻⁵, 2⁻⁴, 2⁻³, 2⁻²`). -/
theorem u_witnesses :
    ((1 : Rat) / ((32 : Int) : Rat)) * ((32 : Int) : Rat) = 1 ∧
    ((1 : Rat) / ((16 : Int) : Rat)) * ((16 : Int) : Rat) = 1 ∧
    ((1 : Rat) / ((8 : Int) : Rat)) * ((8 : Int) : Rat) = 1 ∧
    ((1 : Rat) / ((4 : Int) : Rat)) * ((4 : Int) : Rat) = 1 :=
  ⟨Rat.div_mul_cancel (by decide), Rat.div_mul_cancel (by decide),
   Rat.div_mul_cancel (by decide), Rat.div_mul_cancel (by decide)⟩

/-- THRESHOLD GATE (`17·tden < 64·tnum`, i.e. `threshold > 17/64`):
    `guard_claim_guard2` (2.0) and `guard_claim_signed_distance` (0.3) are
    covered; the genuinely-SAT `guard_claim_tight_1e7` (1e-7) is NOT — the
    emitter must decline it. -/
theorem threshold_gate_guard2 : (17 : Int) * 1 < 64 * 2 := by decide
theorem threshold_gate_signed_distance : (17 : Int) * 10 < 64 * 3 := by decide
theorem threshold_gate_tight_1e7_declined : ¬((17 : Int) * 10000000 < 64 * 1) := by decide

/-- The cap of the `u₁ = 2⁻⁵` grid is exactly `2⁵³ · u₁ = 2⁴⁸` (the asserted
    input magnitude bound `B`), i.e. the spacings really are the Float64 ULPs
    of the binades the magnitudes reach. -/
theorem cap_check_u1 (u1 : Rat) (h : u1 * 32 = 1) :
    (9007199254740992 : Rat) * u1 = 281474976710656 := by grind
theorem cap_check_u2 (u2 : Rat) (h : u2 * 16 = 1) :
    (9007199254740992 : Rat) * u2 = 562949953421312 := by grind
theorem cap_check_u3 (u3 : Rat) (h : u3 * 8 = 1) :
    (9007199254740992 : Rat) * u3 = 1125899906842624 := by grind
theorem cap_check_u4 (u4 : Rat) (h : u4 * 4 = 1) :
    (9007199254740992 : Rat) * u4 = 2251799813685248 := by grind

/-! ###########################################################################
    ## OBLIGATION 1 — `IsF64` SUBSET-NESS, AS A THEOREM.

    `NearestF64 r x` quantifies over `IsF64`.  Making `IsF64` a SUBSET of the
    representable values is the direction that keeps the hypothesis WEAKER than
    the IEEE-754 fact, hence implied by it.  If `IsF64` instead contained a
    NON-representable point, the hypothesis would assert that IEEE rounding
    beats a value hardware cannot produce — strictly stronger than the truth,
    and the certificate would be unsound.

    So subset-ness is load-bearing and it is proved here, against the
    INDEPENDENT decode `AySoundness.FpUnderflow.decodeFin` (a separately
    reference-battery-validated model of the IEEE-754 bit encoding, written for
    the `to_fp`/`fp.rem` emitters and not for this file).  No `decide` battery
    over sample points: a battery cannot rule out a bad point, and there are
    infinitely many candidates.
    ########################################################################### -/

/-- `decodeFin 11 53` on a ZERO exponent field (the subnormal/zero branch):
    the value is `±sigf · 2^(-1074)`. -/
theorem decode64_zeroexp (sign : Bool) (sigf : Nat) :
    decodeFin 11 53 sign 0 sigf
      = { m := (if sign then -1 else 1) * (sigf : Int), e := -1074 } := by
  simp [decodeFin]

/-- `decodeFin 11 53` on a NON-zero exponent field (the normal branch): the
    value is `±(2^52 + sigf) · 2^(expf - 1075)`. -/
theorem decode64_normexp (sign : Bool) (expf sigf : Nat) (hx : expf ≠ 0) :
    decodeFin 11 53 sign expf sigf
      = { m := (if sign then -1 else 1) * ((2 ^ 52 : Int) + (sigf : Int)),
          e := (expf : Int) - 1075 } := by
  simp [decodeFin, hx]
  omega

theorem pow2_split {a b c : Nat} (h : a + b = c) : (2 : Int) ^ a * 2 ^ b = 2 ^ c := by
  rw [← Int.pow_add, h]

theorem pow2_split_nat {a b c : Nat} (h : a + b = c) : (2 : Nat) ^ a * 2 ^ b = 2 ^ c := by
  rw [← Nat.pow_add, h]

/-- Re-express an `IsF64` witness `y · 2^k = M` (`k ≤ 1074`) on the FIXED
    binary64 quantum `2^(-1074)`, so every later identity is an `Int` identity. -/
theorem shift_to_quantum {y : Rat} {M : Int} {k : Nat} (hk : k ≤ 1074)
    (h : y * ((2 ^ k : Int) : Rat) = (M : Rat)) :
    y * ((2 ^ 1074 : Int) : Rat) = ((M * 2 ^ (1074 - k) : Int) : Rat) := by
  have hpow : ((2 ^ 1074 : Int) : Rat)
      = ((2 ^ k : Int) : Rat) * ((2 ^ (1074 - k) : Int) : Rat) := by
    rw [← Rat.intCast_mul, pow2_split (a := k) (b := 1074 - k) (c := 1074) (by omega)]
  rw [hpow, ← Rat.mul_assoc, h, Rat.intCast_mul]

set_option maxRecDepth 20000 in
/-- **`IsF64 ⊆ finite binary64`.**  Every `IsF64` point is EXACTLY the value of
    a finite IEEE-754 binary64 bit pattern: there are a sign bit, a biased
    exponent field `expf ≤ 2046` (so never the `2047` NaN/∞ field) and a stored
    significand `sigf < 2^52` whose decode `⟨m, e⟩ = decodeFin 11 53 …`
    satisfies `y = m · 2^e`.  The conclusion is written division-free, scaled by
    the binary64 quantum `2^1074` (the shift `e + 1074` is proved non-negative
    alongside it), in the same idiom as `IsF64` itself.

    Construction, by cases on `M = ±N` with `N = M.natAbs ≤ 2^53`:
    * `N = 0` → `±0`;
    * `N = 2^53` → the one point needing 54 raw bits: `m = ±2^52`, `expf = 1076 − k`;
    * otherwise `L = N.log2 ≤ 52` and
      * `k ≤ L + 1022` → NORMAL, `expf = L + 1023 − k`, `sigf = N·2^(52−L) − 2^52`
        (in `[2^52, 2^53)` because `2^L ≤ N < 2^(L+1)`);
      * `k > L + 1022` → SUBNORMAL, `expf = 0`, `sigf = N·2^(1074−k) < 2^52`. -/
theorem isF64_representable {y : Rat} (h : IsF64 y) :
    ∃ (sign : Bool) (expf sigf : Nat),
      expf ≤ 2046 ∧ sigf < 2 ^ 52 ∧
      0 ≤ (decodeFin 11 53 sign expf sigf).e + 1074 ∧
      y * ((2 ^ 1074 : Int) : Rat)
        = (((decodeFin 11 53 sign expf sigf).m
              * 2 ^ ((decodeFin 11 53 sign expf sigf).e + 1074).toNat : Int) : Rat) := by
  obtain ⟨M, k, hMb, hk, hy⟩ := h
  have hyq : y * ((2 ^ 1074 : Int) : Rat) = ((M * 2 ^ (1074 - k) : Int) : Rat) :=
    shift_to_quantum hk hy
  obtain ⟨sign, hsigndef⟩ : ∃ s : Bool, s = decide (M < 0) := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ n : Nat, n = M.natAbs := ⟨_, rfl⟩
  have hsgn : (if sign then (-1 : Int) else 1) * (N : Int) = M := by
    subst hsigndef; subst hNdef
    rcases Int.lt_or_le M 0 with hneg | hpos
    · simp [hneg]; omega
    · simp [Int.not_lt.mpr hpos]; omega
  have hNb : N ≤ 2 ^ 53 := by omega
  by_cases hz : N = 0
  · refine ⟨sign, 0, 0, by omega, by decide, ?_, ?_⟩
    · rw [decode64_zeroexp]; show (0 : Int) ≤ -1074 + 1074; decide
    · rw [decode64_zeroexp, hyq]
      have hM0 : M = 0 := by omega
      congr 1
      simp [hM0]
  by_cases htop : N = 2 ^ 53
  · refine ⟨sign, 1076 - k, 0, by omega, by decide, ?_, ?_⟩
    · rw [decode64_normexp _ _ _ (by omega)]
      simp only
      omega
    · rw [decode64_normexp _ _ _ (by omega), hyq]
      simp only
      have hexp : ((((1076 - k : Nat) : Int) - 1075) + 1074).toNat = 1075 - k := by omega
      rw [hexp]
      congr 1
      have hMv : M = (if sign then (-1 : Int) else 1) * (2 ^ 53) := by
        rw [← hsgn, htop]; norm_cast
      have h0 : ((0 : Nat) : Int) = 0 := rfl
      rw [hMv, h0, Int.add_zero, Int.mul_assoc, Int.mul_assoc]
      congr 1
      rw [pow2_split (a := 53) (b := 1074 - k) (c := 1127 - k) (by omega),
          pow2_split (a := 52) (b := 1075 - k) (c := 1127 - k) (by omega)]
  · obtain ⟨L, hLdef⟩ : ∃ l : Nat, l = N.log2 := ⟨_, rfl⟩
    have hlo : 2 ^ L ≤ N := by rw [hLdef]; exact Nat.log2_self_le hz
    have hhi : N < 2 ^ (L + 1) := by rw [hLdef]; exact Nat.lt_log2_self
    have hNlt : N < 2 ^ 53 := by omega
    have hL52 : L ≤ 52 := by
      rcases Nat.lt_or_ge 52 L with hc | hc
      · exfalso
        have h53 : (2 : Nat) ^ 53 ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      · exact hc
    by_cases hnorm : k ≤ L + 1022
    · refine ⟨sign, L + 1023 - k, N * 2 ^ (52 - L) - 2 ^ 52, by omega, ?_, ?_, ?_⟩
      · have hub : N * 2 ^ (52 - L) < 2 ^ 53 := by
          have h1 : N * 2 ^ (52 - L) < 2 ^ (L + 1) * 2 ^ (52 - L) :=
            (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hhi
          rw [pow2_split_nat (a := L + 1) (b := 52 - L) (c := 53) (by omega)] at h1
          exact h1
        omega
      · rw [decode64_normexp _ _ _ (by omega)]
        simp only
        omega
      · rw [decode64_normexp _ _ _ (by omega)]
        simp only
        rw [hyq]
        have hexp : ((((L + 1023 - k : Nat) : Int) - 1075) + 1074).toNat = L + 1022 - k := by
          omega
        rw [hexp]
        congr 1
        have hlb : (2 : Nat) ^ 52 ≤ N * 2 ^ (52 - L) := by
          have h1 : (2 : Nat) ^ L * 2 ^ (52 - L) ≤ N * 2 ^ (52 - L) :=
            Nat.mul_le_mul_right _ hlo
          rw [pow2_split_nat (a := L) (b := 52 - L) (c := 52) (by omega)] at h1
          exact h1
        have hcast : ((N * 2 ^ (52 - L) - 2 ^ 52 : Nat) : Int)
            = (N : Int) * 2 ^ (52 - L) - 2 ^ 52 := by
          rw [Int.natCast_sub hlb, Int.natCast_mul, Int.natCast_pow, Int.natCast_pow]
          rfl
        have hcancel : ∀ a z : Int, a + (z - a) = z := by intro a z; omega
        have hsig : ((2 : Int) ^ 52 + ((N * 2 ^ (52 - L) - 2 ^ 52 : Nat) : Int))
            = (N : Int) * 2 ^ (52 - L) := by
          rw [hcast, hcancel]
        have hpow : (2 : Int) ^ (52 - L) * 2 ^ (L + 1022 - k) = 2 ^ (1074 - k) :=
          pow2_split (by omega)
        have key : ∀ s n A Bv : Int, s * n * (A * Bv) = s * (n * A) * Bv := by
          intro s n A Bv; grind
        rw [hsig, ← hsgn, ← hpow, key]
    · refine ⟨sign, 0, N * 2 ^ (1074 - k), by omega, ?_, ?_, ?_⟩
      · have h1 : N * 2 ^ (1074 - k) < 2 ^ (L + 1) * 2 ^ (1074 - k) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hhi
        rw [pow2_split_nat (a := L + 1) (b := 1074 - k) (c := L + 1075 - k) (by omega)] at h1
        have h2 : (2 : Nat) ^ (L + 1075 - k) ≤ 2 ^ 52 :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega
      · rw [decode64_zeroexp]; show (0 : Int) ≤ -1074 + 1074; decide
      · rw [decode64_zeroexp, hyq]
        simp only
        have hexp : (((-1074 : Int)) + 1074).toNat = 0 := by omega
        rw [hexp]
        congr 1
        rw [← hsgn]
        push_cast
        grind

/-- VALIDATION of the decode CONVENTION used by `isF64_representable`: known
    binary64 bit patterns decode to their known values.  `1.0 = 2^52·2^(-52)`,
    `−1.0`, `2.0 = 2^52·2^(-51)`, the smallest subnormal `1·2^(-1074)` and the
    smallest normal `2^52·2^(-1074) = 2^(-1022)`.  A convention error (bias,
    hidden bit, or the `sb−1` stored width) would break at least one of these. -/
theorem decode64_reference_battery :
    decodeFin 11 53 false 1023 0 = ⟨2 ^ 52, -52⟩ ∧
    decodeFin 11 53 true 1023 0 = ⟨-(2 ^ 52), -52⟩ ∧
    decodeFin 11 53 false 1024 0 = ⟨2 ^ 52, -51⟩ ∧
    decodeFin 11 53 false 0 1 = ⟨1, -1074⟩ ∧
    decodeFin 11 53 false 1 0 = ⟨2 ^ 52, -1074⟩ := by decide

/-- The two `IsF64` witnesses `rne_step` actually builds — a grid point and the
    cap — really are `IsF64`, so `isF64_representable` is not vacuous on them. -/
theorem isF64_witnesses_nonvacuous :
    IsF64 (((3 : Int) : Rat) * (1 / ((32 : Int) : Rat))) ∧
    IsF64 (((2 ^ 53 : Int) : Rat) * (1 / ((32 : Int) : Rat))) :=
  ⟨grid_isF64 (k := 5) (by omega) (by decide) (Rat.div_mul_cancel (by decide)) (by decide),
   grid_isF64 (k := 5) (by omega) (by decide) (Rat.div_mul_cancel (by decide)) (by decide)⟩

/-! ###########################################################################
    ## OBLIGATION 2 — CHAINED FINITENESS OF THE SIX INTERMEDIATES.

    The benchmark asserts `fp.isNormal` on the SEVEN LEAVES only.  Nothing in
    the assertions says the six INTERMEDIATES `t1 t2 t3 s1 s2 rf` are finite —
    and `fp.to_real` is unspecified on NaN and `±∞`, so if any intermediate
    could be non-finite, the `NearestF64` hypotheses could not be extracted
    from an SMT model at all and the composed conflict would be inapplicable.

    Finiteness therefore has to be DERIVED, and it is: purely from the
    magnitude cap half of `rne_step`, with no extra assumption.
    ########################################################################### -/

/-- **Chained finiteness.**  Under exactly the `guard_claim_*` magnitude
    hypotheses and the six RNE rounding links, every intermediate is bounded:
    `|t1|,|t2|,|t3| ≤ 2⁴⁸`, `|s1| ≤ 2⁴⁹`, `|s2| ≤ 2⁵⁰`, `|rf| ≤ 2⁵¹` — and each
    is therefore under the `OVF = 2⁶⁰` guard, nine binades of slack, and 972
    binades under the binary64 overflow threshold `(2 − 2⁻⁵³)·2¹⁰²³`.  No
    intermediate is `±∞` or NaN, so `fp.to_real` is specified on all of them. -/
theorem guard_claim_intermediates_finite
    (nx ny nz px py pz d t1 t2 t3 s1 s2 rf : Rat)
    (u1 u2 u3 u4 : Rat)
    (hu1 : u1 * ((32 : Int) : Rat) = 1) (hu2 : u2 * ((16 : Int) : Rat) = 1)
    (hu3 : u3 * ((8 : Int) : Rat) = 1) (hu4 : u4 * ((4 : Int) : Rat) = 1)
    (hnx : AbsLe nx 1) (hny : AbsLe ny 1) (hnz : AbsLe nz 1)
    (hpx : AbsLe px B48) (hpy : AbsLe py B48) (hpz : AbsLe pz B48) (hd : AbsLe d B48)
    (ht1 : NearestF64 t1 (nx * px)) (ht2 : NearestF64 t2 (ny * py))
    (ht3 : NearestF64 t3 (nz * pz))
    (hs1 : NearestF64 s1 (t1 + t2)) (hs2 : NearestF64 s2 (s1 + t3))
    (hrf : NearestF64 rf (s2 + d)) :
    AbsLe t1 B48 ∧ AbsLe t2 B48 ∧ AbsLe t3 B48 ∧
      AbsLe s1 (((562949953421312 : Int) : Rat)) ∧
      AbsLe s2 (((1125899906842624 : Int) : Rat)) ∧
      AbsLe rf (((2251799813685248 : Int) : Rat)) ∧
      AbsLe rf OVF := by
  have hm1 : AbsLe (nx * px) B48 := mul_mag hnx.1 hnx.2 hpx.1 hpx.2
  have hm2 : AbsLe (ny * py) B48 := mul_mag hny.1 hny.2 hpy.1 hpy.2
  have hm3 : AbsLe (nz * pz) B48 := mul_mag hnz.1 hnz.2 hpz.1 hpz.2
  have r1 := rne_step (c := 32) (k := 5) (by omega) (by decide) (by decide) hu1
      (Mi := 281474976710656) (by decide) (by decide) hm1 ht1
  have r2 := rne_step (c := 32) (k := 5) (by omega) (by decide) (by decide) hu1
      (Mi := 281474976710656) (by decide) (by decide) hm2 ht2
  have r3 := rne_step (c := 32) (k := 5) (by omega) (by decide) (by decide) hu1
      (Mi := 281474976710656) (by decide) (by decide) hm3 ht3
  have hsum1 : AbsLe (t1 + t2) (((562949953421312 : Int) : Rat)) := by
    refine absLe_add r1.2 r2.2 ?_
    show ((281474976710656 : Int) : Rat) + ((281474976710656 : Int) : Rat)
        ≤ ((562949953421312 : Int) : Rat)
    rw [← Rat.intCast_add]; exact intCast_le (by decide)
  have r4 := rne_step (c := 16) (k := 4) (by omega) (by decide) (by decide) hu2
      (Mi := 562949953421312) (by decide) (by decide) hsum1 hs1
  have hsum2 : AbsLe (s1 + t3) (((1125899906842624 : Int) : Rat)) := by
    refine absLe_add r4.2 r3.2 ?_
    show ((562949953421312 : Int) : Rat) + ((281474976710656 : Int) : Rat)
        ≤ ((1125899906842624 : Int) : Rat)
    rw [← Rat.intCast_add]; exact intCast_le (by decide)
  have r5 := rne_step (c := 8) (k := 3) (by omega) (by decide) (by decide) hu3
      (Mi := 1125899906842624) (by decide) (by decide) hsum2 hs2
  have hsum3 : AbsLe (s2 + d) (((2251799813685248 : Int) : Rat)) := by
    refine absLe_add r5.2 hd ?_
    show ((1125899906842624 : Int) : Rat) + ((281474976710656 : Int) : Rat)
        ≤ ((2251799813685248 : Int) : Rat)
    rw [← Rat.intCast_add]; exact intCast_le (by decide)
  have r6 := rne_step (c := 4) (k := 2) (by omega) (by decide) (by decide) hu4
      (Mi := 2251799813685248) (by decide) (by decide) hsum3 hrf
  refine ⟨r1.2, r2.2, r3.2, r4.2, r5.2, r6.2, ?_⟩
  refine absLe_mono r6.2 ?_
  show ((2251799813685248 : Int) : Rat) ≤ OVF
  unfold OVF
  exact intCast_le (by decide)

#print axioms isF64_representable
#print axioms decode64_reference_battery
#print axioms guard_claim_intermediates_finite
#print axioms rne_step
#print axioms guard_claim_no_model
#print axioms hypotheses_satisfiable

end AySoundness.FpBridge

/-! ###########################################################################
     THE SHAPE THE EMITTER **WOULD** RENDER — NOT EMITTED, NOT AUTHORITATIVE.

     Deliberately NOT in the `AySoundness.Emitted.*` namespace, because nothing
     emits it: `emit_fp_dot_error_bound_firewall_lean_from_parsed` is
     fail-closed. It is kept here as evidence that the composed conflict has the
     same firewall shape as every shipped emission (a `Val` model, a Bool-valued
     `atomVal`, the input clauses, ONE theory-lemma clause discharged by the
     verified bridge, and `firewall_combined_unsat`), so that if the residual
     `fp.mul RNE`/`NearestF64` identification is ever discharged, what remains
     is rendering, not mathematics.

     Rendered for `benchmarks/smt/QF_FPLRA/guard_claim_signed_distance.smt2`
     (threshold `0.3` ⇒ `tnum = 3`, `tden = 10`).
     ###########################################################################  -/

namespace AySoundness.FpBridge.WouldEmitShape

open AySoundness
open AySoundness.FpBridge

attribute [local instance] Classical.propDecidable

/-- The model: the `fp.to_real` values of the seven inputs and of the six
    rounded intermediates. -/
structure Val where
  nx : Rat
  ny : Rat
  nz : Rat
  px : Rat
  py : Rat
  pz : Rat
  d : Rat
  t1 : Rat
  t2 : Rat
  t3 : Rat
  s1 : Rat
  s2 : Rat
  rf : Rat

/-- Atoms 1–7: the asserted magnitude bounds (the `fp.isNormal` conjunct is
    DROPPED — sound, a refutation of a weaker set refutes the original).
    Atoms 8–13: the IEEE-754 RNE rounding links of the six recognized ops —
    THE UNPROVEN IDENTIFICATION, see the file header.
    Atom 14: the refuted claim `(>= (- (fp.to_real rf) rreal) 0.3)`, scaled to
    `3 ≤ 10·(rf − rreal)`. -/
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (AbsLe m.nx 1)
  | 2 => decide (AbsLe m.ny 1)
  | 3 => decide (AbsLe m.nz 1)
  | 4 => decide (AbsLe m.px B48)
  | 5 => decide (AbsLe m.py B48)
  | 6 => decide (AbsLe m.pz B48)
  | 7 => decide (AbsLe m.d B48)
  | 8 => decide (NearestF64 m.t1 (m.nx * m.px))
  | 9 => decide (NearestF64 m.t2 (m.ny * m.py))
  | 10 => decide (NearestF64 m.t3 (m.nz * m.pz))
  | 11 => decide (NearestF64 m.s1 (m.t1 + m.t2))
  | 12 => decide (NearestF64 m.s2 (m.s1 + m.t3))
  | 13 => decide (NearestF64 m.rf (m.s2 + m.d))
  | 14 => decide ((3 : Rat) ≤ (10 : Rat) *
            (m.rf - (((m.nx * m.px + m.ny * m.py) + m.nz * m.pz) + m.d)))
  | _ => false

def original : List (Cid × Clause) :=
  [(1, [1]), (2, [2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7]),
   (8, [8]), (9, [9]), (10, [10]), (11, [11]), (12, [12]), (13, [13]), (14, [14])]

def lemmas : List (Cid × Clause) :=
  [(15, [-1, -2, -3, -4, -5, -6, -7, -8, -9, -10, -11, -12, -13, -14])]

def proof : List (Cid × Clause × List Int) :=
  [(16, [], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])]

theorem lemma_valid (m : Val) :
    clauseSat (atomVal m) [-1, -2, -3, -4, -5, -6, -7, -8, -9, -10, -11, -12, -13, -14] = true := by
  by_cases h1 : AbsLe m.nx 1
  · by_cases h2 : AbsLe m.ny 1
    · by_cases h3 : AbsLe m.nz 1
      · by_cases h4 : AbsLe m.px B48
        · by_cases h5 : AbsLe m.py B48
          · by_cases h6 : AbsLe m.pz B48
            · by_cases h7 : AbsLe m.d B48
              · by_cases h8 : NearestF64 m.t1 (m.nx * m.px)
                · by_cases h9 : NearestF64 m.t2 (m.ny * m.py)
                  · by_cases h10 : NearestF64 m.t3 (m.nz * m.pz)
                    · by_cases h11 : NearestF64 m.s1 (m.t1 + m.t2)
                      · by_cases h12 : NearestF64 m.s2 (m.s1 + m.t3)
                        · by_cases h13 : NearestF64 m.rf (m.s2 + m.d)
                          · by_cases h14 : (3 : Rat) ≤ (10 : Rat) *
                                (m.rf - (((m.nx * m.px + m.ny * m.py) + m.nz * m.pz) + m.d))
                            · exact absurd
                                (guard_claim_no_model m.nx m.ny m.nz m.px m.py m.pz m.d
                                  m.t1 m.t2 m.t3 m.s1 m.s2 m.rf
                                  ((1 : Rat) / ((32 : Int) : Rat))
                                  ((1 : Rat) / ((16 : Int) : Rat))
                                  ((1 : Rat) / ((8 : Int) : Rat))
                                  ((1 : Rat) / ((4 : Int) : Rat))
                                  (Rat.div_mul_cancel (by decide))
                                  (Rat.div_mul_cancel (by decide))
                                  (Rat.div_mul_cancel (by decide))
                                  (Rat.div_mul_cancel (by decide))
                                  h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
                                  3 10 (by decide) (by decide) (by simpa using h14))
                                (by simp)
                            · simp [clauseSat, litSat, atomVal, h14]
                          · simp [clauseSat, litSat, atomVal, h13]
                        · simp [clauseSat, litSat, atomVal, h12]
                      · simp [clauseSat, litSat, atomVal, h11]
                    · simp [clauseSat, litSat, atomVal, h10]
                  · simp [clauseSat, litSat, atomVal, h9]
                · simp [clauseSat, litSat, atomVal, h8]
              · simp [clauseSat, litSat, atomVal, h7]
            · simp [clauseSat, litSat, atomVal, h6]
          · simp [clauseSat, litSat, atomVal, h5]
        · simp [clauseSat, litSat, atomVal, h4]
      · simp [clauseSat, litSat, atomVal, h3]
    · simp [clauseSat, litSat, atomVal, h2]
  · simp [clauseSat, litSat, atomVal, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_valid m

/-- The RATIONAL MODEL of the `guard_claim_signed_distance` assertion set has no
    model — via the firewall.  NOT a certificate for the SMT-LIB benchmark: see
    the file header for the one identification that is still hand-argued. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

#print axioms no_model

end AySoundness.FpBridge.WouldEmitShape
