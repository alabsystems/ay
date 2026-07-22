import AySoundness.Firewall
/-
  BIT-BLASTING a real ARITHMETIC circuit through the verified firewall — the PoC
  that the bit-blast grounding (CombinedBvBitBlast.lean, 1-bit AND) extends to the
  full set of adder gate kinds a BV-large emitter must produce. This is the
  per-kind VALIDITY-LEMMA de-risk for the `BvBlastProof → firewall` renderer
  (ay-proof/src/bv_blast_export.rs `BitLemmaKind`): every gate kind's Tseitin
  defining clauses are a TINY Boolean tautology over just that gate's bits when the
  output is the COMPUTED Tseitin auxiliary — no `(2^w)^vars` enumeration, no
  `bv_decide` (which would add a native SAT-trust axiom).

  Worked obligation: `not(bvadd(a,b) == bvadd(a,b))` over `BitVec 2` is UNSAT
  (a value equals itself). Bit-blasting a 2-bit ripple-carry adder with carry-in
  `cin = false` shares all gates between the two (syntactically identical) sides,
  so each result bit `Lᵢ ≡ Rᵢ` is the SAME variable and `Eᵢ = (Lᵢ ⇔ Rᵢ)` is a
  constant-`true` XnorEq. The disequality `∨ᵢ ¬Eᵢ` then resolves against the
  derived `Eᵢ` units to the empty clause.

  Variables → atoms (atom = varId+1, 1-based for signed literals):
    a₀=1 a₁=2 b₀=3 b₁=4            (free inputs)
    cin=5  (ConstFalse)
    sum₀  = Xor3(a₀,b₀,cin)            ↦ 6
    carry₀= FullAdderCarry(a₀,b₀,cin)  ↦ 7
    sum₁  = Xor3(a₁,b₁,carry₀)         ↦ 8
    E₀    = XnorEq(sum₀,sum₀)          ↦ 9   (= true)
    E₁    = XnorEq(sum₁,sum₁)          ↦ 10  (= true)

  Gate kinds exercised: Xor3, FullAdderCarry, XnorEq, ConstFalse (the arithmetic
  core). And2 is covered by CombinedBvBitBlast.lean; Xor2/Or2/Not are strictly
  simpler single-gate analogues of the same `out = gate_eval(ins)` pattern.

  `#print axioms no_model` ⊆ {propext, Quot.sound} (all Bool, computable); no
  `sorry`, no `native_decide`.
-/
namespace AySoundness.CombinedBvAdderBitBlast
open AySoundness

/-- A model: the two free 2-bit operands, bit by bit. -/
structure Val where
  a0 : Bool
  a1 : Bool
  b0 : Bool
  b1 : Bool

/-- Atoms are circuit bits. Free inputs read the model; every gate output is the
    COMPUTED Tseitin auxiliary `out = gate_eval(ins)` (so each gate's defining
    clauses are unconditionally valid). `cin = false` (ConstFalse); `E₀ = E₁ =
    true` because each is `XnorEq(l, l) = ¬(l ⊕ l) = ¬false = true`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => m.a0
  | 2 => m.a1
  | 3 => m.b0
  | 4 => m.b1
  | 5 => false                                              -- cin (ConstFalse)
  | 6 => Bool.xor m.a0 m.b0                                 -- sum₀ = a₀⊕b₀⊕cin
  | 7 => m.a0 && m.b0                                       -- carry₀ = maj(a₀,b₀,0)
  | 8 => Bool.xor (Bool.xor m.a1 m.b1) (m.a0 && m.b0)       -- sum₁ = a₁⊕b₁⊕carry₀
  | 9 => true                                              -- E₀ = (sum₀ ⇔ sum₀)
  | 10 => true                                             -- E₁ = (sum₁ ⇔ sum₁)
  | _ => false

/-- The single disequality clause `∨ᵢ ¬Eᵢ` from `not(lhs == rhs)`. -/
def original : List (Cid × Clause) := [(1, [-9, -10])]

/-- Gate Tseitin clauses (all VALID under `atomVal`, since `out = gate_eval(ins)`):
    the two `XnorEq(l,l)` units per bit `(Eᵢ ∨ ¬lᵢ), (Eᵢ ∨ lᵢ)`, plus one
    representative Xor3 and one FullAdderCarry clause to exercise those kinds'
    validity. -/
def lemmas : List (Cid × Clause) :=
  [ (2, [9, -6]), (3, [9, 6])       -- XnorEq E₀ over sum₀ (atom 6)
  , (4, [10, -8]), (5, [10, 8])     -- XnorEq E₁ over sum₁ (atom 8)
  , (6, [-6, 1, 3, 5])              -- Xor3 sum₀: ¬sum₀ ∨ a₀ ∨ b₀ ∨ cin
  , (7, [-7, 1, 3, 5]) ]            -- FullAdderCarry carry₀: ¬carry₀ ∨ a₀ ∨ b₀ ∨ cin

/-- Resolution to ⊥: derive each `Eᵢ` unit from its two XnorEq clauses, then
    consume the disequality. Each step's last hint reaches a falsified clause. -/
def proof : List (Cid × Clause × List Int) :=
  [ (8,  [9],   [2, 3])    -- E₀ unit  : res(clause2, clause3) on var 6
  , (9,  [10],  [4, 5])    -- E₁ unit  : res(clause4, clause5) on var 8
  , (10, [-10], [1, 8])    -- res(disequality, E₀) on var 9
  , (11, [],    [10, 9]) ] -- res(step10, E₁) on var 10 → ⊥

/-- Every gate clause is valid under the computed-output `atomVal`: the `XnorEq`
    clauses hold because `Eᵢ = true`; the Xor3 / FullAdderCarry representatives are
    Boolean tautologies over the two low input bits. -/
theorem gate_clauses_valid (m : Val) (cl : Clause)
    (h : cl = [9, -6] ∨ cl = [9, 6] ∨ cl = [10, -8] ∨ cl = [10, 8]
       ∨ cl = [-6, 1, 3, 5] ∨ cl = [-7, 1, 3, 5]) :
    clauseSat (atomVal m) cl = true := by
  rcases h with h | h | h | h | h | h <;> subst h <;>
    simp only [clauseSat, litSat, atomVal, List.any_cons, List.any_nil] <;>
    cases m.a0 <;> cases m.a1 <;> cases m.b0 <;> cases m.b1 <;> rfl

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  exact gate_clauses_valid m cl hcl

/-- No 2-bit model satisfies `not(bvadd(a,b) == bvadd(a,b))` — via bit-blasting a
    real adder circuit through the verified firewall (per-gate validity +
    `lratCheck`, no value enumeration, no native axiom). -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.CombinedBvAdderBitBlast
