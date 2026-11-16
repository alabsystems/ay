import AySoundness.BitVecThy
import Init.Data.BitVec.Lemmas
import Init.Data.List.Range
import Init.Data.Nat.Mod

/-!
Semantic relations required by AY's equality-to-bits, constant unsigned-spine
and zero-extended-range rules. The statements range over every typed source
word, not an assignment selected by the producer or a rendered circuit model.

These theorems do not authenticate a runtime TermStore, a declaration epoch,
complete assumptions, coverage metadata or a gate/CNF journal. The maintained
kernel must check their exact instantiation and the original-source/circuit
binding before they can authorize a solver proof. This module adds no Rust
admission and does not turn its independent native Lean check into a certificate.
-/
namespace AySoundness.BitVecSourceRelations

/-! ## Complete equality coverage and exact extract bits -/

def bitEqual (a b : Bool) : Bool :=
  BitVecThy.gNot (BitVecThy.gXor a b)

theorem bitEqual_eq : ∀ a b : Bool, bitEqual a b = (a == b) := by decide

def equalityBits {w : Nat} (x y : BitVec w) (indices : List Nat) : Bool :=
  indices.all (fun i => bitEqual (x.getLsbD i) (y.getLsbD i))

theorem equalityBits_sound {w : Nat} (x y : BitVec w) (indices : List Nat)
    (cover : ∀ i, i < w → i ∈ indices) :
    equalityBits x y indices = (x == y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [equalityBits, bitEqual_eq, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    exact BitVec.eq_of_getLsbD_eq_iff.mpr (fun i hi => h i (cover i hi))
  · intro h i _
    rw [h]

/-- Coverage is an actual mathematical premise. A runtime certificate must
    prove it for its exact indices; a Rust coverage count is not a Lean proof. -/
theorem equalityBits_range {w : Nat} (x y : BitVec w) :
    equalityBits x y (List.range w) = (x == y) :=
  equalityBits_sound x y (List.range w) (fun _ hi => List.mem_range.mpr hi)

theorem equality_implies_bit {w : Nat} (x y : BitVec w) (h : x = y) (i : Nat) :
    bitEqual (x.getLsbD i) (y.getLsbD i) = true := by
  rw [h, bitEqual_eq]
  simp

theorem equality_iff_extracts {w : Nat} (x y : BitVec w) :
    x = y ↔ ∀ i, i < w → x.extractLsb' i 1 = y.extractLsb' i 1 := by
  constructor
  · intro h i _
    rw [h]
  · intro h
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    have bits := congrArg (fun word : BitVec 1 => word.getLsbD 0) (h i hi)
    simpa using bits

/-- This total Lean extract relation does not validate an SMT index. The source
    quotation must still prove `i < w` for every authored extract. -/
theorem extractBit_literal {w : Nat} (x : BitVec w) (i : Nat) (value : Bool) :
    ((x.extractLsb' i 1) == BitVec.ofBool value) = (x.getLsbD i == value) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    have hi := congrArg (fun word : BitVec 1 => word.getLsbD 0) h
    simpa using hi
  · intro h
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro j hj
    have hj' : j = 0 := by omega
    subst j
    simpa using h

def signedBitGate (a b p q negative useXor : Bool) : Bool :=
  (if useXor then (a ^^ p) ^^ (b ^^ q) else ((a ^^ p) == (b ^^ q))) ^^ negative

theorem signedBitGate_sound : ∀ a b p q negative useXor : Bool,
    (negative ^^ p ^^ q) = useXor →
      signedBitGate a b p q negative useXor = (a == b) := by decide

theorem constantBitGate_sound : ∀ a value inverted : Bool,
    value ≠ inverted → (a ^^ inverted) = (a == value) := by decide

theorem equalityBits_distinct {w : Nat} (x y : BitVec w) (indices : List Nat)
    (cover : ∀ i, i < w → i ∈ indices) :
    (!equalityBits x y indices) = decide (x ≠ y) := by
  rw [equalityBits_sound x y indices cover]
  by_cases h : x = y <;> simp [h]

/-- The enclosing assertion can also mention the unchanged source valuation. -/
theorem equalityBits_models {w : Nat} {Env : Type} (left right : Env → BitVec w)
    (indices : List Nat) (cover : ∀ i, i < w → i ∈ indices)
    (assertion : Env → Bool → Prop) :
    (∃ env, assertion env (left env == right env)) ↔
      (∃ env, assertion env (equalityBits (left env) (right env) indices)) := by
  constructor
  · rintro ⟨env, h⟩
    refine ⟨env, ?_⟩
    rw [equalityBits_sound (left env) (right env) indices cover]
    exact h
  · rintro ⟨env, h⟩
    refine ⟨env, ?_⟩
    rw [equalityBits_sound (left env) (right env) indices cover] at h
    exact h

/-! ## Unsigned comparator and constant AND/OR spines -/

/-- The exact comparator step for the low `n+1` bits. The proof uses the
    quotient/remainder decomposition, with no enumeration or width bound. -/
theorem comparison_step (x y n : Nat) :
    decide (x % 2 ^ (n + 1) < y % 2 ^ (n + 1)) =
      ((!x.testBit n && y.testBit n) ||
       ((x.testBit n == y.testBit n) && decide (x % 2 ^ n < y % 2 ^ n))) := by
  have hxlt := Nat.mod_lt x (Nat.two_pow_pos n)
  have hylt := Nat.mod_lt y (Nat.two_pow_pos n)
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ n) with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one (y / 2 ^ n) with hy | hy
  all_goals
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ]
    simp only [Nat.testBit_eq_decide_div_mod_eq, hx, hy]
    apply Bool.eq_iff_iff.mpr
    simp <;> omega

def comparisonBits (a b : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => (!a.testBit n && b.testBit n) ||
      ((a.testBit n == b.testBit n) && comparisonBits a b n)

theorem comparisonBits_sound (a b n : Nat) :
    comparisonBits a b n = decide (a % 2 ^ n < b % 2 ^ n) := by
  induction n with
  | zero => simp [comparisonBits, Nat.mod_one]
  | succ n ih => rw [comparisonBits, ih, ← comparison_step]

def wordLeftSpine {w : Nat} (x : BitVec w) (c : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => if c.testBit n then !x.getLsbD n || wordLeftSpine x c n
      else !x.getLsbD n && wordLeftSpine x c n

theorem wordLeftSpine_circuit {w : Nat} (x : BitVec w) (c n : Nat) :
    wordLeftSpine x c n = comparisonBits x.toNat c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [wordLeftSpine, comparisonBits, ih, BitVec.getLsbD]
    cases c.testBit n <;> cases x.toNat.testBit n <;>
      cases comparisonBits x.toNat c n <;> rfl

def wordRightSpine {w : Nat} (x : BitVec w) (c : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => if c.testBit n then x.getLsbD n && wordRightSpine x c n
      else x.getLsbD n || wordRightSpine x c n

theorem wordRightSpine_circuit {w : Nat} (x : BitVec w) (c n : Nat) :
    wordRightSpine x c n = comparisonBits c x.toNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [wordRightSpine, comparisonBits, ih, BitVec.getLsbD]
    cases c.testBit n <;> cases x.toNat.testBit n <;>
      cases comparisonBits c x.toNat n <;> rfl

theorem wordLeftSpine_sound {w : Nat} (x : BitVec w) (c : Nat) (hc : c < 2 ^ w) :
    wordLeftSpine x c w = x.ult (BitVec.ofNat w c) := by
  rw [wordLeftSpine_circuit, comparisonBits_sound]
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt hc]

theorem wordRightSpine_sound {w : Nat} (x : BitVec w) (c : Nat) (hc : c < 2 ^ w) :
    wordRightSpine x c w = (BitVec.ofNat w c).ult x := by
  rw [wordRightSpine_circuit, comparisonBits_sound]
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt hc]

theorem not_wordLeftSpine_sound {w : Nat} (x : BitVec w) (c : Nat) (hc : c < 2 ^ w) :
    (!wordLeftSpine x c w) = (BitVec.ofNat w c).ule x := by
  rw [wordLeftSpine_sound x c hc, BitVec.ule_eq_not_ult]

theorem not_wordRightSpine_sound {w : Nat} (x : BitVec w) (c : Nat) (hc : c < 2 ^ w) :
    (!wordRightSpine x c w) = x.ule (BitVec.ofNat w c) := by
  rw [wordRightSpine_sound x c hc, BitVec.ule_eq_not_ult]

theorem wordLeftSpine_models {w : Nat} {Env : Type} (source : Env → BitVec w)
    (c : Nat) (hc : c < 2 ^ w) (assertion : Env → Bool → Prop) :
    (∃ env, assertion env ((source env).ult (BitVec.ofNat w c))) ↔
      (∃ env, assertion env (wordLeftSpine (source env) c w)) := by
  constructor
  · rintro ⟨env, h⟩
    refine ⟨env, ?_⟩
    rw [wordLeftSpine_sound (source env) c hc]
    exact h
  · rintro ⟨env, h⟩
    refine ⟨env, ?_⟩
    rw [wordLeftSpine_sound (source env) c hc] at h
    exact h

theorem wordLeftSpine_false_prefix {w : Nat} (x : BitVec w) (c n : Nat)
    (hc : ∀ i, i < n → c.testBit i = false) : wordLeftSpine x c n = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [wordLeftSpine, hc n (by omega)]
    simp only [Bool.false_eq_true, ↓reduceIte, ih (fun i hi => hc i (by omega)), Bool.and_false]

theorem wordRightSpine_false_prefix {w : Nat} (x : BitVec w) (c n : Nat)
    (hc : ∀ i, i < n → c.testBit i = true) : wordRightSpine x c n = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [wordRightSpine, hc n (by omega)]
    simp only [↓reduceIte, ih (fun i hi => hc i (by omega)), Bool.and_false]

theorem wordLeftSpine_zero {w : Nat} (x : BitVec w) :
    wordLeftSpine x 0 w = false := by
  apply wordLeftSpine_false_prefix
  intro i _
  simp

theorem wordRightSpine_max {w : Nat} (x : BitVec w) :
    wordRightSpine x (2 ^ w - 1) w = false := by
  apply wordRightSpine_false_prefix
  intro i hi
  simp [hi]

/-- The skipped false seed is valid only with the exact lower constant bits. -/
theorem wordLeftSpine_first {w : Nat} (x : BitVec w) (c first : Nat)
    (below : ∀ i, i < first → c.testBit i = false) (atFirst : c.testBit first = true) :
    wordLeftSpine x c (first + 1) = !x.getLsbD first := by
  rw [wordLeftSpine, atFirst, wordLeftSpine_false_prefix x c first below]
  simp

theorem wordRightSpine_first {w : Nat} (x : BitVec w) (c first : Nat)
    (below : ∀ i, i < first → c.testBit i = true) (atFirst : c.testBit first = false) :
    wordRightSpine x c (first + 1) = x.getLsbD first := by
  rw [wordRightSpine, atFirst, wordRightSpine_false_prefix x c first below]
  simp

/-! ## Typed zero extension and constant-range side conditions

The width is exactly input plus extension. Canonical constants must fit that
result width; the premises deliberately exclude modularly wrapped bounds.
-/

def zeroExtend {w : Nat} (x : BitVec w) (extra : Nat) : BitVec (w + extra) :=
  x.setWidth (w + extra)

theorem zeroExtend_toNat {w : Nat} (x : BitVec w) (extra : Nat) :
    (zeroExtend x extra).toNat = x.toNat :=
  BitVec.toNat_setWidth_of_le (by omega)

theorem zeroExtend_bit {w : Nat} (x : BitVec w) (extra i : Nat) :
    (zeroExtend x extra).getLsbD i = x.getLsbD i := by
  simp only [zeroExtend, BitVec.getLsbD_setWidth]
  by_cases hi : i < w + extra
  · simp [hi]
  · have hw : w ≤ i := by omega
    simp [hi, BitVec.getLsbD_of_ge x i hw]

theorem zeroExtend_high_bit {w : Nat} (x : BitVec w) (extra i : Nat) (hi : w ≤ i) :
    (zeroExtend x extra).getLsbD i = false := by
  rw [zeroExtend_bit]
  exact BitVec.getLsbD_of_ge x i hi

theorem zeroExtend_range {w : Nat} (x : BitVec w) (extra : Nat) :
    (zeroExtend x extra).toNat < 2 ^ w := by
  rw [zeroExtend_toNat]
  exact x.isLt

theorem zeroExtend_lt_constant {w : Nat} (x : BitVec w) (extra c : Nat)
    (hc : c < 2 ^ (w + extra)) (hbound : 2 ^ w ≤ c) :
    (zeroExtend x extra).ult (BitVec.ofNat (w + extra) c) = true := by
  simp only [BitVec.ult_eq_decide, zeroExtend_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hc, decide_eq_true_eq]
  exact Nat.lt_of_lt_of_le x.isLt hbound

theorem constant_not_lt_zeroExtend {w : Nat} (x : BitVec w) (extra c : Nat)
    (hc : c < 2 ^ (w + extra)) (hbound : 2 ^ w - 1 ≤ c) :
    (BitVec.ofNat (w + extra) c).ult (zeroExtend x extra) = false := by
  simp only [BitVec.ult_eq_decide, zeroExtend_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hc, decide_eq_false_iff_not]
  have hx := x.isLt
  omega

/-- The actual consumer's unsigned upper-bound relation, including equality. -/
theorem zeroExtend_le_constant {w : Nat} (x : BitVec w) (extra c : Nat)
    (hc : c < 2 ^ (w + extra)) (hbound : 2 ^ w - 1 ≤ c) :
    (zeroExtend x extra).ule (BitVec.ofNat (w + extra) c) = true := by
  rw [BitVec.ule_eq_not_ult, constant_not_lt_zeroExtend x extra c hc hbound]
  rfl

theorem zeroExtend_not_lt_zero {w : Nat} (x : BitVec w) (extra : Nat) :
    (zeroExtend x extra).ult 0#(w + extra) = false := by
  simp [BitVec.ult_eq_decide]

theorem zeroExtend_nested {w : Nat} (x : BitVec w) (first second : Nat) :
    zeroExtend (zeroExtend x first) second =
      (zeroExtend x (first + second)).cast (by omega) := by
  apply BitVec.eq_of_toNat_eq
  simp only [zeroExtend_toNat, BitVec.toNat_cast]

end AySoundness.BitVecSourceRelations
