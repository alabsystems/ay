import Init.Data.BitVec.Lemmas

/-!
A relation for the real SMT-LIB signed-division operation, including zero.
This is a mathematical source lemma, not a certificate binding an authored SMT
query to a proposed bit-blast circuit. It does not restore Rust checker shortcuts.
-/
namespace AySoundness.SignedDivisionRelation

def signCases {w : Nat} (x y : BitVec w) : BitVec w :=
  if x.msb then
    if y.msb then (-x).smtUDiv (-y) else -((-x).smtUDiv y)
  else
    if y.msb then -(x.smtUDiv (-y)) else x.smtUDiv y

theorem smtSDiv_signCases {w : Nat} (x y : BitVec w) :
    x.smtSDiv y = signCases x y := by
  cases hx : x.msb <;> cases hy : y.msb <;>
    simp only [signCases, BitVec.smtSDiv, hx, hy] <;> rfl

/-! ## Zero and unit divisors

These are equalities of the SMT operations, not Lean's zero-divisor division.
They hold for every dividend and width, including width one, where the bit
patterns for one and minus one coincide. Negation is modular, so division of
the minimum signed value by minus one has no extra, invalid overflow premise.
-/

theorem smtSDiv_zero {w : Nat} (x : BitVec w) :
    x.smtSDiv 0#w = if x.msb then 1#w else BitVec.allOnes w := by
  cases hx : x.msb <;>
    simp [BitVec.smtSDiv, hx, ← BitVec.neg_one_eq_allOnes]

private theorem smtUDiv_one {w : Nat} (x : BitVec w) :
    x.smtUDiv 1#w = x := by
  cases w with
  | zero => simp [BitVec.eq_nil x, BitVec.smtUDiv]
  | succ w => simp [BitVec.smtUDiv]

theorem smtSDiv_one {w : Nat} (x : BitVec w) :
    x.smtSDiv 1#w = x := by
  by_cases hw : w = 1
  · subst hw
    cases hx : x.msb <;> simp [BitVec.smtSDiv_eq, hx, smtUDiv_one]
  · cases hx : x.msb <;> simp [BitVec.smtSDiv_eq, hx, hw, smtUDiv_one]

theorem smtSDiv_neg_one {w : Nat} (x : BitVec w) :
    x.smtSDiv (-1#w) = -x := by
  cases w with
  | zero => simp [BitVec.eq_nil x, BitVec.smtSDiv]
  | succ w =>
    have hm : (-1#(w + 1)).msb = true := by
      rw [BitVec.neg_one_eq_allOnes]
      exact BitVec.msb_allOnes (by omega)
    cases hx : x.msb <;> simp [BitVec.smtSDiv_eq, hx, hm, smtUDiv_one]

/-- SMT division preserves the modular overflow result, at every width. -/
theorem smtSDiv_min_neg_one (w : Nat) :
    (BitVec.intMin w).smtSDiv (-1#w) = BitVec.intMin w := by
  rw [smtSDiv_neg_one, BitVec.neg_intMin]

/-- The old false-successor twin is false on a supported semantic path, even
    when the addition wraps. Positive width is necessary for this rejection. -/
theorem smtSDiv_one_ne_successor {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x.smtSDiv 1#w ≠ x + 1#w := by
  rw [smtSDiv_one]
  intro h
  have hz : 1#w = 0#w := BitVec.add_right_eq_self.mp h.symm
  have hn := congrArg BitVec.toNat hz
  have hw' : w ≠ 0 := by omega
  simp [hw'] at hn

/-- The SMT zero-divisor result differs from ordinary Lean division. -/
theorem smtSDiv_zero_zero_ne_zero {w : Nat} (hw : 0 < w) :
    (0#w).smtSDiv 0#w ≠ 0#w := by
  rw [smtSDiv_zero]
  simp only [BitVec.msb_zero, Bool.false_eq_true, ↓reduceIte]
  rw [← BitVec.neg_one_eq_allOnes]
  intro h
  have hz := BitVec.neg_eq_zero_iff.mp h
  have hn := congrArg BitVec.toNat hz
  have hw' : w ≠ 0 := by omega
  simp [hw'] at hn

theorem srem_zero {w : Nat} (x : BitVec w) : x.srem 0#w = x :=
  BitVec.srem_zero

theorem srem_one {w : Nat} (x : BitVec w) : x.srem 1#w = 0#w :=
  BitVec.srem_one

theorem srem_neg_one {w : Nat} (x : BitVec w) :
    x.srem (-1#w) = 0#w := by
  cases w with
  | zero => simp [BitVec.eq_nil x, BitVec.srem]
  | succ w =>
    have hm : (-1#(w + 1)).msb = true := by
      rw [BitVec.neg_one_eq_allOnes]
      exact BitVec.msb_allOnes (by omega)
    cases hx : x.msb <;> simp [BitVec.srem_eq, hx, hm]

theorem smod_zero {w : Nat} (x : BitVec w) : x.smod 0#w = x :=
  BitVec.smod_zero

theorem smod_one {w : Nat} (x : BitVec w) : x.smod 1#w = 0#w := by
  cases hx : x.msb <;> by_cases hw : w = 1 <;>
    (try subst hw) <;> simp_all [BitVec.smod_eq]

theorem smod_neg_one {w : Nat} (x : BitVec w) :
    x.smod (-1#w) = 0#w := by
  cases w with
  | zero => simp [BitVec.eq_nil x, BitVec.smod]
  | succ w =>
    have hm : (-1#(w + 1)).msb = true := by
      rw [BitVec.neg_one_eq_allOnes]
      exact BitVec.msb_allOnes (by omega)
    cases hx : x.msb <;> simp [BitVec.smod_eq, hx, hm]

/-! ## Typed original-to-lowered relation

This small word language makes the preserved source valuation explicit. It
does not assume a gate equation or accept a producer's claim of equivalence.
`unit_rewrite_sound` proves the actual equality for all assignments to the
original leaves and for an arbitrary dividend expression in this language.

A runtime consumer must still reconstruct this typed quotation from its
authenticated original term, bind its exact declaration/assumption epoch, and
connect the exact lowered expression to its gates. No Rust checker admission
or original-query UNSAT authority is granted by this module alone.
-/

inductive SignedOp where
  | div
  | rem
  | mod
  deriving DecidableEq

def SignedOp.eval {w : Nat} : SignedOp → BitVec w → BitVec w → BitVec w
  | .div, x, y => x.smtSDiv y
  | .rem, x, y => x.srem y
  | .mod, x, y => x.smod y

inductive UnitDivisor where
  | zero
  | one
  | negOne
  deriving DecidableEq

def UnitDivisor.value (w : Nat) : UnitDivisor → BitVec w
  | .zero => 0#w
  | .one => 1#w
  | .negOne => -1#w

inductive WordExpr (w : Nat) (Var : Type) where
  | leaf : Var → WordExpr w Var
  | literal : BitVec w → WordExpr w Var
  | neg : WordExpr w Var → WordExpr w Var
  | signed : SignedOp → WordExpr w Var → WordExpr w Var → WordExpr w Var
  | ifNegative : WordExpr w Var → WordExpr w Var → WordExpr w Var → WordExpr w Var

def WordExpr.eval {w : Nat} {Var : Type} (valuation : Var → BitVec w) :
    WordExpr w Var → BitVec w
  | .leaf v => valuation v
  | .literal value => value
  | .neg argument => -(argument.eval valuation)
  | .signed op left right => op.eval (left.eval valuation) (right.eval valuation)
  | .ifNegative condition yes no =>
      if (condition.eval valuation).msb then yes.eval valuation else no.eval valuation

def lowerUnit {w : Nat} {Var : Type} (op : SignedOp) (divisor : UnitDivisor)
    (argument : WordExpr w Var) : WordExpr w Var :=
  match op, divisor with
  | .div, .zero => .ifNegative argument (.literal 1#w) (.literal (BitVec.allOnes w))
  | .div, .one => argument
  | .div, .negOne => .neg argument
  | .rem, .zero | .mod, .zero => argument
  | .rem, .one | .rem, .negOne | .mod, .one | .mod, .negOne => .literal 0#w

theorem unit_rewrite_sound {w : Nat} {Var : Type} (valuation : Var → BitVec w)
    (op : SignedOp) (divisor : UnitDivisor) (argument : WordExpr w Var) :
    (.signed op argument (.literal (divisor.value w)) : WordExpr w Var).eval valuation =
      (lowerUnit op divisor argument).eval valuation := by
  cases op <;> cases divisor <;>
    simp only [WordExpr.eval, SignedOp.eval, UnitDivisor.value, lowerUnit,
      smtSDiv_zero, smtSDiv_one, smtSDiv_neg_one,
      srem_zero, srem_one, srem_neg_one, smod_zero, smod_one, smod_neg_one]

/-- Every output bit is preserved under the same original leaf valuation. -/
theorem unit_rewrite_bit {w : Nat} {Var : Type} (valuation : Var → BitVec w)
    (op : SignedOp) (divisor : UnitDivisor) (argument : WordExpr w Var) (bit : Nat) :
    ((.signed op argument (.literal (divisor.value w)) : WordExpr w Var).eval
      valuation).getLsbD bit =
      ((lowerUnit op divisor argument).eval valuation).getLsbD bit :=
  congrArg (fun word => word.getLsbD bit) (unit_rewrite_sound valuation op divisor argument)

/-- An enclosing assertion may also mention the original valuation. Its models
    are preserved; the premise is not merely existence of one circuit model. -/
theorem unit_rewrite_models {w : Nat} {Var : Type} (op : SignedOp)
    (divisor : UnitDivisor) (argument : WordExpr w Var)
    (assertion : (Var → BitVec w) → BitVec w → Prop) :
    (∃ valuation, assertion valuation
      ((.signed op argument (.literal (divisor.value w)) : WordExpr w Var).eval valuation)) ↔
    (∃ valuation, assertion valuation ((lowerUnit op divisor argument).eval valuation)) := by
  simp only [unit_rewrite_sound]

/-- A compact literal bit has the same semantics as the original one-bit extract.
    This supplies mathematics, not the missing runtime source/slot binding. -/
theorem literal_bit_extract (w value bit : Nat) :
    ((BitVec.ofNat w value).extractLsb' bit 1 == 1#1) =
      (decide (bit < w) && value.testBit bit) := by
  rw [← BitVec.getLsbD_eq_extractLsb', BitVec.getLsbD_ofNat]


/-! ## Exact extract/BEq and `getLsbD` claim bridge

AY's maintained literal producer states an equality from a one-bit extract's
`BEq` against `1#1` to the original encoded Boolean. The bounded Clean request
prepares an equality from `getLsbD` to that same Boolean. They are distinct
expressions. The following proofs relate the exact expressions while retaining
all original parameters; neither preparation nor a matching Boolean proves the
premise. Applying the bridge still requires checked original proof data and
original source/ordered-slot/declaration-world/resource binding at runtime.

These are total Lean operations, including width zero and out-of-range indices.
They do not relax the maintained Rust producer's positive-width, canonical-value
or in-range-index guards.
-/

/-- The actual one-bit extract/BEq expression, for every word and index. -/
theorem extract_bit_beq_one_eq_getLsbD {w : Nat} (x : BitVec w) (bit : Nat) :
    (x.extractLsb' bit 1 == 1#1) = x.getLsbD bit :=
  (BitVec.getLsbD_eq_extractLsb' x bit).symm

/-- Convert the producer's exact original claim to the prepared Bool equality.
    The expected Boolean is unchanged and remains a proved premise. -/
theorem literal_bit_extract_to_getLsbD (w value bit : Nat) (expected : Bool)
    (original : @Eq Bool ((BitVec.ofNat w value).extractLsb' bit 1 == 1#1) expected) :
    @Eq Bool ((BitVec.ofNat w value).getLsbD bit) expected :=
  (BitVec.getLsbD_eq_extractLsb' (BitVec.ofNat w value) bit).trans original

/-- The reverse direction is needed when a checked request result must justify
    the producer's original extract/BEq statement, rather than replace it. -/
theorem literal_bit_getLsbD_to_extract (w value bit : Nat) (expected : Bool)
    (request : @Eq Bool ((BitVec.ofNat w value).getLsbD bit) expected) :
    @Eq Bool ((BitVec.ofNat w value).extractLsb' bit 1 == 1#1) expected :=
  (extract_bit_beq_one_eq_getLsbD (BitVec.ofNat w value) bit).trans request

theorem literal_bit_extract_iff_getLsbD (w value bit : Nat) (expected : Bool) :
    (@Eq Bool ((BitVec.ofNat w value).extractLsb' bit 1 == 1#1) expected) ↔
      (@Eq Bool ((BitVec.ofNat w value).getLsbD bit) expected) :=
  ⟨literal_bit_extract_to_getLsbD w value bit expected,
   literal_bit_getLsbD_to_extract w value bit expected⟩

/-- Compose with the actual maintained producer theorem, keeping its width
    guard and Nat magnitude's bit; this is not an assumed candidate Boolean. -/
theorem literal_bit_getLsbD (w value bit : Nat) :
    (BitVec.ofNat w value).getLsbD bit =
      (decide (bit < w) && value.testBit bit) :=
  literal_bit_extract_to_getLsbD w value bit _ (literal_bit_extract w value bit)

/-- In-range source guards remain separate from total Lean semantics. -/
theorem literal_bit_getLsbD_out_of_range (w value bit : Nat) (outside : w ≤ bit) :
    (BitVec.ofNat w value).getLsbD bit = false :=
  BitVec.getLsbD_of_ge (BitVec.ofNat w value) bit outside

end AySoundness.SignedDivisionRelation
