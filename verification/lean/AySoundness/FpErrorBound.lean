/-
  FORMAL FIXED-GRID RATIONAL RESEARCH MODELS motivated by the QF_FPLRA
  `guard_claim_guard2` and `guard_claim_signed_distance` benchmarks
  (`benchmarks/smt/QF_FPLRA/guard_claim_guard2.smt2`,
   `guard_claim_signed_distance.smt2`).

  Both encode ONE signed-distance evaluation `r = nx·px + ny·py + nz·pz + d`
  in IEEE-754 `Float64` with RNE rounding, inputs constrained by `|nᵢ| ≤ 1`,
  `|pᵢ|, |d| ≤ 2⁴⁸`, and assert `(fp.to_real rf) − exact_real_dot ≥ THRESHOLD`
  (2.0 for guard2, 0.3 for signed_distance).

  AUTHORITY BOUNDARY: neither fixed-grid model is a production proof authority.
  The Rust firewall declines both benchmarks because this file does not yet
  prove that the recognized IEEE-754 operations, their actual rounded
  intermediates, and the asserted magnitude hypotheses instantiate the chosen
  `qround` spacings. The declarations below are preserved as proof research.

  THE CONTENT INSIDE EACH STATED RATIONAL MODEL IS PROVEN, NOT ASSERTED:

  * `unit_half_ulp` / `half_ulp` — the per-operation half-ULP bound
    `|round_RNE x − x| ≤ (1/2)·ulp` is PROVEN from the grid definition
    (nearest multiple of the spacing `u`) and `Rat.floor_le` /
    `Rat.lt_floor_add_one`.  This is the crux; it is derived, never axiomatized.

  * `iround` / `iround_half_ulp` + the `example … by decide` reference battery —
    concrete rounding-error cases over the pure-`Int` rounding kernel, each the
    exact expected fraction of an ULP, checked by kernel `decide` (validation
    that catches model bugs; it already caught a tie-direction mislabel).

  * `mul_mag` — the separate rational magnitude fact
    `|nᵢ| ≤ 1 ∧ |pᵢ| ≤ B ⟹ |nᵢ·pᵢ| ≤ B`, proven from Rat multiplication
    monotonicity. It is useful toward a future bridge, but is not currently
    connected to Float64 exponent/ULP classification or rounded intermediates.

  * `dot_error_bound` / `guard2_qround_unsat` — the accumulated error of the
    displayed coarse fixed-grid computation is `≤ 11/32` (physical), refuting
    `≥ 2.0` inside that rational model only.

  MODEL / SCALING.  Core `Rat` in Lean has no fraction-reducing `decide` (gcd is
  well-founded), so we work in units of `2⁻⁴` (multiply the whole computation by
  16): the three products round at spacing `1`, the first two sums at spacing `2`,
  the final sum at spacing `4`; the magnitude bound is `B = 2⁵² = 16·2⁴⁸` and the
  physical threshold `2.0` becomes `32`.  In these units every spacing, magnitude
  and threshold is an integer-valued rational (`decide`-friendly), while the crux
  stays fully symbolic. Scaling is exact within this model. A future authority
  theorem must additionally relate each parsed IEEE operation to the
  corresponding `qround` term and prove that the selected spacing bounds its
  actual result; prose about binades is not that theorem.

  `guard_claim_signed_distance` (threshold 0.3) NEEDS a strictly tighter bound
  (`11/32 = 0.34375` does not refute `0.3`). The declarations
  `dot_error_bound_tight` / `signed_distance_qround_unsat` below prove the
  accumulated `13/64 = 0.203125 < 0.3` bound INSIDE the stated fixed-spacing
  `qround` model. They do not yet prove that every recognized IEEE-754
  execution instantiates those tighter spacings, so they are research lemmas,
  not an UNSAT authority for the SMT benchmark.

  Pure Lean 4 core + `Std` tactics (`omega`, `decide`, `simp`, `push_cast`,
  `norm_cast`); no Mathlib, no `Real`, no `ring`/`linarith`, no `native_decide`,
  no `sorry`.

  AXIOMS (audited at the end).  The Int-level per-op half-ULP bound
  `iround_half_ulp` and the whole `decide` reference battery are CLASSICAL-FREE:
  `#print axioms ⊆ {propext, Quot.sound}`.  The `Rat`-level results
  (`unit_half_ulp`, `half_ulp`, `mul_mag`, `dot_error_bound`,
  `guard2_qround_unsat`, `dot_error_bound_tight`,
  `signed_distance_qround_unsat`) additionally list
  `Classical.choice` — NOT from any axiomatization of the error
  model, but because Lean v4.30 core's ENTIRE `Rat` ordered-field / floor API
  (`Rat.floor_le`, `Rat.le_total`, `Rat.mul_le_mul_of_nonneg_right`,
  `Rat.div_mul_cancel`, …) is itself proved with `Classical.choice`, so any proof
  touching `Rat` order inherits it.  Removing it would require reimplementing
  rational arithmetic from `Int` (out of scope).  The half-ULP CRUX is therefore
  provided BOTH as the Classical-free `iround_half_ulp` (Int grid) and as the
  symbolic `Rat` `half_ulp`; the propagation/conflict use the `Rat` layer.
-/
import Std
namespace AySoundness.FpErrorBound

/-! ## Derived Rat linear-arithmetic toolkit (core `Rat` API lacks linarith/ring). -/

theorem add_le_add {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Rat.le_trans
    (by rw [Rat.add_comm a c, Rat.add_comm b c]; exact (Rat.add_le_add_left).mpr h1)
    ((Rat.add_le_add_left).mpr h2)

theorem add_le_add_right_iff {a b c : Rat} : a + c ≤ b + c ↔ a ≤ b := by
  rw [Rat.add_comm a c, Rat.add_comm b c]; exact Rat.add_le_add_left

theorem sub_nonneg {a b : Rat} : (0 ≤ b - a) ↔ a ≤ b := by
  constructor
  · intro h
    have := (Rat.add_le_add_left (a := 0) (b := b - a) (c := a)).mpr h
    rwa [Rat.add_zero, show a + (b - a) = b by rw [Rat.add_comm]; exact Rat.sub_add_cancel] at this
  · intro h
    have := (Rat.add_le_add_left (a := a) (b := b) (c := -a)).mpr h
    rwa [Rat.neg_add_cancel, show -a + b = b - a by rw [Rat.sub_eq_add_neg, Rat.add_comm]] at this

theorem sub_pos {a b : Rat} : (0 < b - a) ↔ a < b := by
  constructor
  · intro h
    have := (Rat.add_lt_add_left (a := 0) (b := b - a) (c := a)).mpr h
    rwa [Rat.add_zero, show a + (b - a) = b by rw [Rat.add_comm]; exact Rat.sub_add_cancel] at this
  · intro h
    have := (Rat.add_lt_add_left (a := a) (b := b) (c := -a)).mpr h
    rwa [Rat.neg_add_cancel, show -a + b = b - a by rw [Rat.sub_eq_add_neg, Rat.add_comm]] at this

theorem sub_le_iff {a b c : Rat} : a - c ≤ b ↔ a ≤ b + c := by
  rw [← add_le_add_right_iff (c := c), Rat.sub_add_cancel]

theorem le_sub_iff {a b c : Rat} : a ≤ b - c ↔ a + c ≤ b := by
  rw [← add_le_add_right_iff (c := c) (a := a) (b := b - c), Rat.sub_add_cancel]

theorem neg_add_le_iff {a b c : Rat} : (-c) + a ≤ b ↔ a ≤ b + c := by
  have e : (-c + a) + c = a := by
    rw [Rat.add_assoc, Rat.add_comm a c, ← Rat.add_assoc, Rat.neg_add_cancel, Rat.zero_add]
  constructor
  · intro h
    have := (add_le_add_right_iff (a := -c + a) (b := b) (c := c)).mpr h
    rwa [e] at this
  · intro h
    exact (add_le_add_right_iff (a := -c + a) (b := b) (c := c)).mp (by rw [e]; exact h)

theorem sub_le_sub {a b c d : Rat} (h1 : a ≤ b) (h2 : d ≤ c) : a - c ≤ b - d := by
  rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]; exact add_le_add h1 (Rat.neg_le_neg h2)

theorem sub_mul (a b c : Rat) : (a - b) * c = a * c - b * c := by
  rw [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul, ← Rat.sub_eq_add_neg]

theorem mul_sub (a b c : Rat) : a * (b - c) = a * b - a * c := by
  rw [Rat.mul_comm a (b - c), sub_mul, Rat.mul_comm b a, Rat.mul_comm c a]

theorem add_lt_add_right_iff {a b c : Rat} : a + c < b + c ↔ a < b := by
  rw [Rat.add_comm a c, Rat.add_comm b c]; exact Rat.add_lt_add_left

theorem sub_lt_iff {a b c : Rat} : a - c < b ↔ a < b + c := by
  rw [← add_lt_add_right_iff (c := c), Rat.sub_add_cancel]

/-! ## The nearest-integer function and the unit half-ULP bound. -/

/-- Round-down branch bound: the error value `-(2d)` with `0 ≤ d`, `2d ≤ 1`. -/
theorem neg2d_bounds {d : Rat} (hd0 : 0 ≤ d) (hc : 2 * d ≤ 1) :
    (-1 : Rat) ≤ -(2 * d) ∧ -(2 * d) ≤ 1 := by
  have h2d : (0:Rat) ≤ 2 * d := Rat.mul_nonneg (by decide) hd0
  refine ⟨by simpa using Rat.neg_le_neg hc, ?_⟩
  have : -(2*d) ≤ 0 := by simpa [Rat.neg_zero] using Rat.neg_le_neg h2d
  exact Rat.le_trans this (by decide)

/-- Round-up branch bound: the error value `2 - 2d` with `d < 1`, `1 ≤ 2d`. -/
theorem two_sub_2d_bounds {d : Rat} (hd1 : d < 1) (hc : 1 ≤ 2 * d) :
    (-1 : Rat) ≤ 2 - 2 * d ∧ 2 - 2 * d ≤ 1 := by
  have hlt : 2 * d < 2 * 1 := (Rat.mul_lt_mul_left (by decide)).mpr hd1
  rw [Rat.mul_one] at hlt
  refine ⟨?_, ?_⟩
  · rw [le_sub_iff, neg_add_le_iff]
    have h23 : (2:Rat) ≤ 2 + 1 := by rw [show (2:Rat)+1 = 3 by norm_cast]; decide
    exact Rat.le_trans (Rat.le_of_lt hlt) h23
  · rw [sub_le_iff]
    have : (1:Rat) + 1 ≤ 1 + 2*d := (Rat.add_le_add_left).mpr hc
    rwa [show (1:Rat)+1 = 2 by norm_cast] at this

/-- Nearest integer to `q`; ties resolved toward the floor.  (Any nearest choice
    gives the ≤ 1/2 error bound; the bound below is independent of the tie rule.) -/
def nearestInt (q : Rat) : Int :=
  if 2 * (q - (Rat.floor q : Rat)) ≤ 1 then Rat.floor q else Rat.floor q + 1

/-- **Unit half-ULP bound.**  The nearest integer `N` to `q` obeys
    `-1 ≤ 2·(N − q) ≤ 1` (i.e. `|N − q| ≤ 1/2`), PROVEN from `Rat.floor_le`
    and `Rat.lt_floor_add_one`. -/
theorem unit_half_ulp (q : Rat) :
    (-1 : Rat) ≤ 2 * ((nearestInt q : Rat) - q) ∧
    2 * ((nearestInt q : Rat) - q) ≤ 1 := by
  have hlo : (Rat.floor q : Rat) ≤ q := Rat.floor_le q
  have hhi : q < (Rat.floor q : Rat) + 1 := by
    have := Rat.lt_floor_add_one q; push_cast at this; simpa using this
  have hd0 : (0 : Rat) ≤ q - (Rat.floor q : Rat) := sub_nonneg.mpr hlo
  have hd1 : q - (Rat.floor q : Rat) < 1 :=
    sub_lt_iff.mpr (by rw [Rat.add_comm]; exact hhi)
  unfold nearestInt
  by_cases hc : 2 * (q - (Rat.floor q : Rat)) ≤ 1
  · rw [if_pos hc]
    have key : 2 * ((Rat.floor q : Rat) - q) = -(2 * (q - (Rat.floor q : Rat))) := by
      rw [← Rat.neg_sub q (Rat.floor q : Rat), Rat.mul_neg]
    rw [key]; exact neg2d_bounds hd0 hc
  · rw [if_neg hc]
    have hc' : (1:Rat) ≤ 2 * (q - (Rat.floor q : Rat)) := Rat.le_of_lt (Rat.not_le.mp hc)
    have ecast : ((Rat.floor q + 1 : Int) : Rat) = (Rat.floor q : Rat) + 1 := by push_cast; rfl
    have key : 2 * (((Rat.floor q : Rat) + 1) - q) = 2 - 2 * (q - (Rat.floor q : Rat)) := by
      have e : ((Rat.floor q : Rat) + 1) - q = 1 - (q - (Rat.floor q : Rat)) := by
        rw [Rat.sub_eq_add_neg ((Rat.floor q:Rat)+1) q, Rat.add_comm (Rat.floor q : Rat) 1,
            Rat.add_assoc, Rat.sub_eq_add_neg 1 (q - (Rat.floor q:Rat)), Rat.neg_sub,
            Rat.sub_eq_add_neg (Rat.floor q : Rat) q]
      rw [e, mul_sub, Rat.mul_one]
    rw [ecast, key]; exact two_sub_2d_bounds hd1 hc'

/-- `qround u x` = round `x` to the grid of spacing `u` (nearest multiple of `u`).
    This is the rational operation used by the research model. Connecting a
    parsed `fp.mul RNE` or `fp.add RNE` operation to a particular invocation of
    `qround` requires the absent IEEE-to-model bridge. -/
def qround (u x : Rat) : Rat := (nearestInt (x / u) : Rat) * u

/-- **Half-ULP bound for spacing `u`** — the per-operation RNE error bound.
    `|qround u x − x| ≤ u/2`, stated fraction-free as `-u ≤ 2·(qround u x − x) ≤ u`.
    PROVEN from `unit_half_ulp` (NOT asserted). -/
theorem half_ulp (u x : Rat) (hu : 0 < u) :
    (-u ≤ 2 * (qround u x - x)) ∧ (2 * (qround u x - x) ≤ u) := by
  have hune : u ≠ 0 := by
    intro h; rw [h] at hu; exact absurd hu (by decide)
  have hxu : (x / u) * u = x := Rat.div_mul_cancel hune
  have hle0 : (0:Rat) ≤ u := Rat.le_of_lt hu
  have hunit := unit_half_ulp (x / u)
  have hval : 2 * (qround u x - x)
      = (2 * ((nearestInt (x / u) : Rat) - x / u)) * u := by
    unfold qround; rw [Rat.mul_assoc, sub_mul, hxu]
  rw [hval]
  refine ⟨?_, ?_⟩
  · have h := Rat.mul_le_mul_of_nonneg_right hunit.1 hle0
    rwa [Rat.neg_mul, Rat.one_mul] at h
  · have h := Rat.mul_le_mul_of_nonneg_right hunit.2 hle0
    rwa [Rat.one_mul] at h

/-! ## Reference battery: pure-`Int` rounding kernel + concrete `decide` cases.

`iround a b` is the nearest integer to `a/b` (`b > 0`, ties toward the floor),
using floor division `/`; it is the reflection of `nearestInt` on `q = a/b`.
Being pure `Int`, its concrete values reduce under kernel `decide`. -/

def iround (a b : Int) : Int :=
  if 2 * (a - (a / b) * b) ≤ b then a / b else a / b + 1

/-- Half-ULP bound for the kernel, over fresh integer slots `q = a/b`, `r = a%b`
    (so `omega` never touches `/`,`%`, which keeps it Classical-free). -/
theorem iround_bound_abs (a b q r : Int)
    (hsum : q * b + r = a) (hn : 0 ≤ r) (hl : r < b) :
    -b ≤ 2 * ((if 2 * (a - q * b) ≤ b then q else q + 1) * b - a) ∧
     2 * ((if 2 * (a - q * b) ≤ b then q else q + 1) * b - a) ≤ b := by
  rcases Int.lt_or_le b (2 * (a - q * b)) with hc | hc
  · rw [if_neg (by omega), Int.add_mul, Int.one_mul]; refine ⟨?_, ?_⟩ <;> omega
  · rw [if_pos hc]; refine ⟨?_, ?_⟩ <;> omega

/-- **Int-level per-op half-ULP bound**, PROVEN from floor division (the grid)
    and the nearest rule — and **CLASSICAL-FREE** (`#print axioms` ⊆
    {propext, Quot.sound}; audited below).  This is the RNE half-ULP bound with no
    dependence on `Classical.choice`, independent of the `Rat` layer. -/
theorem iround_half_ulp (a b : Int) (hb : 0 < b) :
    -b ≤ 2 * (iround a b * b - a) ∧ 2 * (iround a b * b - a) ≤ b := by
  have hsum : (a / b) * b + a % b = a := by
    have h := Int.emod_add_ediv a b; rw [Int.mul_comm b (a / b), Int.add_comm] at h; exact h
  have h := iround_bound_abs a b (a / b) (a % b) hsum
    (Int.emod_nonneg a (b := b) (by omega)) (Int.emod_lt_of_pos a hb)
  simpa only [iround] using h

-- Concrete rounding cases (rounding ties toward the floor), checked by `decide`.
example : iround 3 2 = 1 := by decide       -- 1.5  → 1  (tie → floor)
example : iround 1 2 = 0 := by decide       -- 0.5  → 0  (tie → floor)
example : iround 5 4 = 1 := by decide       -- 1.25 → 1
example : iround 7 4 = 2 := by decide       -- 1.75 → 2
example : iround 13 5 = 3 := by decide      -- 2.6  → 3
example : iround 12 5 = 2 := by decide      -- 2.4  → 2
example : iround (-3) 2 = -2 := by decide   -- -1.5 → -2 (tie → floor)
example : iround (-7) 4 = -2 := by decide   -- -1.75 → -2
example : iround 0 5 = 0 := by decide
example : iround 8 1 = 8 := by decide        -- exact integer
-- Error = exact fraction of an ULP:  2·(round·b − a) over 2b is the signed error.
example : 2 * (iround 3 2 * 2 - 3) = -2 := by decide    -- −1/2 ulp (tie → floor)
example : 2 * (iround 5 4 * 4 - 5) = -2 := by decide    -- −1/4 ulp
example : 2 * (iround 7 4 * 4 - 7) = 2 := by decide     -- +1/4 ulp
example : 2 * (iround 13 5 * 5 - 13) = 4 := by decide   -- +2/5 ulp
example : 2 * (iround 8 1 * 1 - 8) = 0 := by decide     -- exact, 0 ulp

/-! ## Rational magnitude propagation (input to a future IEEE bridge). -/

/-- `|n| ≤ 1 ∧ |p| ≤ B ⟹ |n·p| ≤ B` (with `0 ≤ p`). -/
theorem mul_mag_nonneg {n p B : Rat} (hn1 : -1 ≤ n) (hn2 : n ≤ 1)
    (hp0 : 0 ≤ p) (hpB : p ≤ B) : -B ≤ n * p ∧ n * p ≤ B := by
  refine ⟨?_, ?_⟩
  · have h1 : (-1) * p ≤ n * p := Rat.mul_le_mul_of_nonneg_right hn1 hp0
    have h2 : -B ≤ (-1) * p := by rw [Rat.neg_mul, Rat.one_mul]; exact Rat.neg_le_neg hpB
    exact Rat.le_trans h2 h1
  · have h1 : n * p ≤ 1 * p := Rat.mul_le_mul_of_nonneg_right hn2 hp0
    rw [Rat.one_mul] at h1; exact Rat.le_trans h1 hpB

/-- **Rational product magnitude bound.**
    `|nᵢ| ≤ 1 ∧ |pᵢ| ≤ B ⟹ |nᵢ·pᵢ| ≤ B`.

    Relating this fact to a Float64 binade, selected ULP, and actual rounded
    intermediate is an explicit remaining obligation of the semantic bridge. -/
theorem mul_mag {n p B : Rat} (hn1 : -1 ≤ n) (hn2 : n ≤ 1)
    (hp1 : -B ≤ p) (hp2 : p ≤ B) : -B ≤ n * p ∧ n * p ≤ B := by
  rcases (Rat.le_total (a := 0) (b := p)) with hp | hp
  · exact mul_mag_nonneg hn1 hn2 hp hp2
  · have hnp0 : 0 ≤ -p := by have := Rat.neg_le_neg hp; rwa [Rat.neg_zero] at this
    have hnpB : -p ≤ B := by have := Rat.neg_le_neg hp1; rwa [Rat.neg_neg] at this
    obtain ⟨lo, hi⟩ := mul_mag_nonneg hn1 hn2 hnp0 hnpB
    rw [Rat.mul_neg] at lo hi
    refine ⟨?_, ?_⟩
    · have h := Rat.neg_le_neg hi; simp only [Rat.neg_neg] at h; exact h
    · have h := Rat.neg_le_neg lo; simp only [Rat.neg_neg] at h; exact h

/-! ## Error propagation through the six-operation evaluation. -/

/-- `close x y c` : `|x − y| ≤ c/2`, encoded fraction-free as `-c ≤ 2(x−y) ≤ c`. -/
def close (x y c : Rat) : Prop := (-c ≤ 2 * (x - y)) ∧ (2 * (x - y) ≤ c)

/-- Each `qround` operation lands within half its fixed spacing of its input. -/
theorem close_half (u v : Rat) (hu : 0 < u) : close (qround u v) v u := half_ulp u v hu

theorem close_self (d : Rat) : close d d 0 := by
  unfold close; rw [Rat.sub_self, Rat.mul_zero, Rat.neg_zero]; exact ⟨Rat.le_refl, Rat.le_refl⟩

/-- Adding matched exact terms adds the error bounds. -/
theorem close_add {a b a' b' c c' k : Rat}
    (h : close a b c) (h' : close a' b' c') (hk : k = c + c') :
    close (a + a') (b + b') k := by
  unfold close at *
  have id : (a + a') - (b + b') = (a - b) + (a' - b') := by
    simp only [Rat.sub_eq_add_neg, Rat.neg_add, Rat.add_assoc, Rat.add_left_comm]
  have hval : 2 * ((a + a') - (b + b')) = 2 * (a - b) + 2 * (a' - b') := by
    rw [id, Rat.mul_add]
  rw [hval, hk, Rat.neg_add]
  exact ⟨add_le_add h.1 h'.1, add_le_add h.2 h'.2⟩

/-- Triangle inequality: composing two closeness bounds adds them. -/
theorem close_trans_add {x m y c e k : Rat}
    (hxm : close x m c) (hmy : close m y e) (hk : k = c + e) : close x y k := by
  unfold close at *
  have id : (x - m) + (m - y) = x - y := by
    rw [Rat.sub_eq_add_neg x m, Rat.sub_eq_add_neg m y, Rat.add_assoc,
        ← Rat.add_assoc (-m) m (-y), Rat.neg_add_cancel, Rat.zero_add, ← Rat.sub_eq_add_neg]
  have hval : 2 * (x - y) = 2 * (x - m) + 2 * (m - y) := by
    rw [← id, Rat.mul_add]
  rw [hval, hk, Rat.neg_add]
  exact ⟨add_le_add hxm.1 hmy.1, add_le_add hxm.2 hmy.2⟩

/-- **Accumulated error bound for the coarse fixed-grid model**:
    `|rf − (P1+P2+P3+d)| ≤ 11/2` (scaled), i.e.
    `2·error ∈ [−11, 11]`. Errors: 3 products at spacing 1
    (2·e ≤ 1 each) + 2 sums at spacing 2 + 1 sum at spacing 4 =
    1+1+1+2+2+4 = 11. Physical bound 11/32 = 0.34375.

    This theorem does not mention Float64 values or actual rounded
    intermediates; applying it to IEEE execution requires the missing bridge. -/
theorem dot_error_bound (nx ny nz px py pz d : Rat) :
    close
      (qround 4 (qround 2 (qround 2 (qround 1 (nx*px) + qround 1 (ny*py)) + qround 1 (nz*pz)) + d))
      (((nx*px + ny*py) + nz*pz) + d) 11 := by
  have hP1 : close (qround 1 (nx*px)) (nx*px) 1 := close_half _ _ (by decide)
  have hP2 : close (qround 1 (ny*py)) (ny*py) 1 := close_half _ _ (by decide)
  have hP3 : close (qround 1 (nz*pz)) (nz*pz) 1 := close_half _ _ (by decide)
  have h12 : close (qround 1 (nx*px) + qround 1 (ny*py)) (nx*px + ny*py) 2 :=
    close_add hP1 hP2 (by norm_cast)
  have hs1r : close (qround 2 (qround 1 (nx*px) + qround 1 (ny*py)))
      (qround 1 (nx*px) + qround 1 (ny*py)) 2 := close_half _ _ (by decide)
  have hs1 : close (qround 2 (qround 1 (nx*px) + qround 1 (ny*py))) (nx*px + ny*py) 4 :=
    close_trans_add hs1r h12 (by norm_cast)
  have h123 : close (qround 2 (qround 1 (nx*px) + qround 1 (ny*py)) + qround 1 (nz*pz))
      ((nx*px + ny*py) + nz*pz) 5 := close_add hs1 hP3 (by norm_cast)
  have hs2r : close (qround 2 (qround 2 (qround 1 (nx*px) + qround 1 (ny*py)) + qround 1 (nz*pz)))
      (qround 2 (qround 1 (nx*px) + qround 1 (ny*py)) + qround 1 (nz*pz)) 2 := close_half _ _ (by decide)
  have hs2 : close (qround 2 (qround 2 (qround 1 (nx*px) + qround 1 (ny*py)) + qround 1 (nz*pz)))
      ((nx*px + ny*py) + nz*pz) 7 := close_trans_add hs2r h123 (by norm_cast)
  have h123d : close
      (qround 2 (qround 2 (qround 1 (nx*px) + qround 1 (ny*py)) + qround 1 (nz*pz)) + d)
      (((nx*px + ny*py) + nz*pz) + d) 7 := close_add hs2 (close_self d) (by norm_cast)
  have hrfr : close
      (qround 4 (qround 2 (qround 2 (qround 1 (nx*px) + qround 1 (ny*py)) + qround 1 (nz*pz)) + d))
      (qround 2 (qround 2 (qround 1 (nx*px) + qround 1 (ny*py)) + qround 1 (nz*pz)) + d) 4 :=
    close_half _ _ (by decide)
  exact close_trans_add hrfr h123d (by norm_cast)

/-- **Conflict lemma inside the coarse fixed-grid model** (scaled ×16; physical
    threshold 2.0 becomes 32). The modeled error `≥ 32` contradicts the
    fixed-grid bound `2·error ≤ 11` (since `64 ≤ 11` is false).

    This does NOT establish that `guard_claim_guard2.smt2` is UNSAT: that
    conclusion additionally requires the missing IEEE-to-qround bridge. -/
theorem guard2_qround_unsat (nx ny nz px py pz d : Rat)
    (hassert : 32 ≤
      (qround 4 (qround 2 (qround 2 (qround 1 (nx*px) + qround 1 (ny*py)) + qround 1 (nz*pz)) + d))
      - (((nx*px + ny*py) + nz*pz) + d)) : False := by
  have hb := dot_error_bound nx ny nz px py pz d
  have hup := hb.2
  have hlo : (64:Rat) ≤ 2 *
      ((qround 4 (qround 2 (qround 2 (qround 1 (nx*px) + qround 1 (ny*py)) + qround 1 (nz*pz)) + d))
       - (((nx*px + ny*py) + nz*pz) + d)) := by
    have h := Rat.mul_le_mul_of_nonneg_left hassert (by decide : (0:Rat) ≤ 2)
    rwa [show (2:Rat) * 32 = 64 by norm_cast] at h
  exact absurd (Rat.le_trans hlo hup) (by decide)

/-! ## Candidate tighter fixed-grid bound for `guard_claim_signed_distance`
    (threshold 0.3): research, not an IEEE authority.

`dot_error_bound` above bounds each op's error by the FULL worst-case ulp for
its magnitude regime — i.e. it treats the boundary value of the magnitude bound
(e.g. a product of exactly `2⁴⁸`) as needing the *next* binade's (larger) ulp.
The candidate IEEE argument observes that a power-of-two boundary is exactly
representable, so its rounding error is zero and the supremum may come from the
next lower binade.

IMPORTANT AUTHORITY BOUNDARY: the Lean declarations below start from fixed
`qround` spacings. They prove the arithmetic consequence of those spacings, but
they do NOT formalize Float64 exponent classification, prove exactness at each
boundary, or show that every rounded intermediate remains in the claimed
binade. In particular, the following intended IEEE-to-model obligations are not
yet theorems:

* muls `nᵢ·pᵢ`: exact value `≤ B = 2⁴⁸`, with spacing `2⁻⁵` below the exact
  power-of-two boundary;
* first sum `s1 = t1'+t2'`: exact value `≤ 2B = 2⁴⁹`, with spacing `2⁻⁴`
  below its exact boundary;
* second sum `s2 = s1'+t3'`: exact value `≤ 3B`, retaining spacing `2⁻³`;
* final sum `rf = s2'+d`: exact value `≤ 4B = 2⁵⁰`, with spacing `2⁻³`
  below its exact boundary.

If that bridge is proved, the resulting half-ulps sum to
`3·2⁻⁶ + 2⁻⁵ + 2⁻⁴ + 2⁻⁴ = 13/64 = 0.203125`. To keep every
constant an integer (core `Rat`'s `decide`/`DecidableEq` does not reduce
division/gcd — confirmed by hand: `by decide` on bare fraction literals like
`(0:Rat) < 1/32` gets stuck), work in units of `2⁻⁵` (scale `160`, chosen so
BOTH the smallest spacing `2⁻⁵` and the physical threshold `0.3 = 3/10` land on
integers: `160 = 32·5`): mul spacing `5`, first-sum spacing `10`, second-sum
spacing `20` (unchanged from the coarse model's binade), final-sum spacing
`20`; physical threshold `0.3 ↦ 48`. This is the SAME proof shape as
`dot_error_bound`/`guard2_qround_unsat`
(`close_half`/`close_add`/`close_trans_add`),
only the integer spacing/threshold constants differ — no new axioms, no new
primitives. The Rust firewall deliberately declines this path until the bridge
is present and reviewed. -/

/-- **Tighter accumulated fixed-grid error bound**, scaled ×160, for the
    candidate `qround` model: `2·error ≤ 65`, i.e. physical
    `|rf − exact| ≤ 65/320 = 13/64 = 0.203125`. Errors: 3 muls at spacing 5
    (2·e ≤ 5 each) + first sum at spacing 10 + second sum at spacing 20 +
    final sum at spacing 20 = 5+5+5+10+20+20 = 65.

    This theorem quantifies over rationals and the displayed `qround`
    expressions; it does not itself connect them to IEEE-754 execution. -/
theorem dot_error_bound_tight (nx ny nz px py pz d : Rat) :
    close
      (qround 20 (qround 20 (qround 10 (qround 5 (nx*px) + qround 5 (ny*py)) + qround 5 (nz*pz)) + d))
      (((nx*px + ny*py) + nz*pz) + d) 65 := by
  have hP1 : close (qround 5 (nx*px)) (nx*px) 5 := close_half _ _ (by decide)
  have hP2 : close (qround 5 (ny*py)) (ny*py) 5 := close_half _ _ (by decide)
  have hP3 : close (qround 5 (nz*pz)) (nz*pz) 5 := close_half _ _ (by decide)
  have h12 : close (qround 5 (nx*px) + qround 5 (ny*py)) (nx*px + ny*py) 10 :=
    close_add hP1 hP2 (by norm_cast)
  have hs1r : close (qround 10 (qround 5 (nx*px) + qround 5 (ny*py)))
      (qround 5 (nx*px) + qround 5 (ny*py)) 10 := close_half _ _ (by decide)
  have hs1 : close (qround 10 (qround 5 (nx*px) + qround 5 (ny*py))) (nx*px + ny*py) 20 :=
    close_trans_add hs1r h12 (by norm_cast)
  have h123 : close (qround 10 (qround 5 (nx*px) + qround 5 (ny*py)) + qround 5 (nz*pz))
      ((nx*px + ny*py) + nz*pz) 25 := close_add hs1 hP3 (by norm_cast)
  have hs2r : close (qround 20 (qround 10 (qround 5 (nx*px) + qround 5 (ny*py)) + qround 5 (nz*pz)))
      (qround 10 (qround 5 (nx*px) + qround 5 (ny*py)) + qround 5 (nz*pz)) 20 := close_half _ _ (by decide)
  have hs2 : close (qround 20 (qround 10 (qround 5 (nx*px) + qround 5 (ny*py)) + qround 5 (nz*pz)))
      ((nx*px + ny*py) + nz*pz) 45 := close_trans_add hs2r h123 (by norm_cast)
  have h123d : close
      (qround 20 (qround 10 (qround 5 (nx*px) + qround 5 (ny*py)) + qround 5 (nz*pz)) + d)
      (((nx*px + ny*py) + nz*pz) + d) 45 := close_add hs2 (close_self d) (by norm_cast)
  have hrfr : close
      (qround 20 (qround 20 (qround 10 (qround 5 (nx*px) + qround 5 (ny*py)) + qround 5 (nz*pz)) + d))
      (qround 20 (qround 10 (qround 5 (nx*px) + qround 5 (ny*py)) + qround 5 (nz*pz)) + d) 20 :=
    close_half _ _ (by decide)
  exact close_trans_add hrfr h123d (by norm_cast)

/-- **Conflict lemma inside the candidate fixed-grid model** (scaled ×160;
    physical threshold 0.3 becomes 48). The modeled error `≥ 48` contradicts
    the fixed-grid bound `2·error ≤ 65` (since `96 ≤ 65` is false).

    This does NOT establish that `guard_claim_signed_distance.smt2` is UNSAT:
    that conclusion additionally requires the missing IEEE-to-qround bridge. -/
theorem signed_distance_qround_unsat (nx ny nz px py pz d : Rat)
    (hassert : 48 ≤
      (qround 20 (qround 20 (qround 10 (qround 5 (nx*px) + qround 5 (ny*py)) + qround 5 (nz*pz)) + d))
      - (((nx*px + ny*py) + nz*pz) + d)) : False := by
  have hb := dot_error_bound_tight nx ny nz px py pz d
  have hup := hb.2
  have hlo : (96:Rat) ≤ 2 *
      ((qround 20 (qround 20 (qround 10 (qround 5 (nx*px) + qround 5 (ny*py)) + qround 5 (nz*pz)) + d))
       - (((nx*px + ny*py) + nz*pz) + d)) := by
    have h := Rat.mul_le_mul_of_nonneg_left hassert (by decide : (0:Rat) ≤ 2)
    rwa [show (2:Rat) * 48 = 96 by norm_cast] at h
  exact absurd (Rat.le_trans hlo hup) (by decide)

-- Axiom audit.  `iround_half_ulp` (the Classical-free per-op half-ULP crux) and
-- the `decide` battery depend only on {propext, Quot.sound}.  The `Rat`-layer
-- results additionally list `Classical.choice`, inherited from Lean core's `Rat`
-- order/floor API (see header) — no `sorryAx` anywhere.
#print axioms iround_half_ulp   -- {propext, Quot.sound}  (CLASSICAL-FREE)
#print axioms unit_half_ulp     -- + Classical.choice (from core Rat.floor_le)
#print axioms half_ulp
#print axioms mul_mag
#print axioms dot_error_bound
#print axioms guard2_qround_unsat
#print axioms dot_error_bound_tight
#print axioms signed_distance_qround_unsat

end AySoundness.FpErrorBound
