import AySoundness.Firewall
/-
  BIT-BLASTING through the firewall, the EMITTER-READY form — the target shape the
  production `BvBlastProof → Lean` renderer (BV-large piece 3/3) emits.

  The earlier bit-blast PoCs (CombinedBvBitBlast / CombinedBvAdderBitBlast) define
  `atomVal` by COMPUTING each gate output from the inputs. For a deep gate DAG (a
  32-bit adder is hundreds of gates, each feeding the next) that closed form either
  blows up (full inlining) or needs well-founded recursion over the gate graph —
  awkward to generate.

  This formulation sidesteps it entirely. Model the firewall over **gate-respecting
  assignments**: `Val` packages an arbitrary propositional assignment `α : Nat → Bool`
  TOGETHER WITH a proof that each gate output equals `gateEval` of its inputs (one
  hypothesis per gate). `atomVal m = m.α`. The firewall conclusion is a `∀` over such
  assignments — we never CONSTRUCT one, so there is no recursion and a deep DAG is
  just more hypotheses. Soundness is if anything STRONGER: any real bit-vector model
  induces a gate-respecting assignment (the gates are definitions), so "no
  gate-respecting α satisfies `original`" ⟹ the bit-blasted formula is UNSAT.

  Each gate-clause's validity is discharged by rewriting with that gate's respect
  hypothesis and case-splitting the (≤ 3) input bits — exactly what the renderer
  generates per gate (here And2). The 2-gate chain `g₂ = g₁ ∧ c`, `g₁ = a ∧ b`
  demonstrates a gate feeding another: the deep-DAG case the WF-recursion fear was
  about, now handled with no recursion.

  Worked obligation: `(a ∧ b) ∧ c = 1 ∧ a = 0` is UNSAT (`a = 0 ⟹ g₂ = 0 ≠ 1`).
  Atoms: a↦1 b↦2 c↦3 g₁↦4 g₂↦5. `#print axioms no_model` ⊆ {propext, Quot.sound};
  no `sorry`, no `native_decide`.
-/
namespace AySoundness.CombinedBvBlastAbstract
open AySoundness

/-- A gate-respecting assignment: an arbitrary propositional `α`, plus a proof that
    each AND gate's output equals the conjunction of its inputs. The renderer emits
    one `respects_*` field per gate of the `BvBlastProof`. -/
structure Val where
  α : Nat → Bool
  /-- gate `g₁ = a ∧ b` (4 = 1 ∧ 2). -/
  respects_g1 : α 4 = (α 1 && α 2)
  /-- gate `g₂ = g₁ ∧ c` (5 = 4 ∧ 3) — a gate fed by another gate (deep DAG). -/
  respects_g2 : α 5 = (α 4 && α 3)

/-- The atom valuation IS the assignment; gate outputs are not computed but
    constrained by the model's `respects_*` proofs. -/
def atomVal (m : Val) (n : Nat) : Bool := m.α n

/-- `g₂ = 1` (clause `[5]`) and `a = 0` (clause `[-1]`). -/
def original : List (Cid × Clause) := [(1, [5]), (2, [-1])]

/-- Tseitin defining clauses for the two AND gates. -/
def lemmas : List (Cid × Clause) :=
  [ (3, [-4, 1]), (4, [-4, 2]), (5, [4, -1, -2])    -- g₁ = a ∧ b
  , (6, [-5, 4]), (7, [-5, 3]), (8, [5, -4, -3]) ]  -- g₂ = g₁ ∧ c

/-- Unit-propagate `g₂` (clause 1), `¬a` (clause 2), then `g₂→g₁` (clause 6) gives
    `g₁`, and `g₁→a` (clause 3) is falsified ⟹ empty clause. -/
def proof : List (Cid × Clause × List Int) := [(9, [], [1, 2, 6, 3])]

/-- Each AND-gate Tseitin clause holds under any gate-respecting assignment: rewrite
    the gate output via its `respects_*` proof, then the clause is a Boolean
    tautology over the (now input-only) bits. -/
theorem gate_clauses_valid (m : Val) (cl : Clause)
    (h : cl = [-4, 1] ∨ cl = [-4, 2] ∨ cl = [4, -1, -2]
       ∨ cl = [-5, 4] ∨ cl = [-5, 3] ∨ cl = [5, -4, -3]) :
    clauseSat (atomVal m) cl = true := by
  -- Bring the gate-respect equations into scope, split the input bits, then let
  -- `simp_all` reduce the literal arithmetic, substitute the respect equations
  -- (which determine the gate-output bits `α 4`, `α 5`), and close each case.
  have e1 := m.respects_g1
  have e2 := m.respects_g2
  rcases h with h | h | h | h | h | h <;> subst h <;>
    cases hb1 : m.α 1 <;> cases hb2 : m.α 2 <;> cases hb3 : m.α 3 <;>
    simp_all [clauseSat, litSat, atomVal]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  exact gate_clauses_valid m cl hcl

/-- No gate-respecting assignment satisfies `(a ∧ b) ∧ c = 1 ∧ a = 0` — via the
    emitter-ready firewall shape (abstract `α` + per-gate respect hypotheses, no
    value enumeration and no recursion over the gate DAG). -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.CombinedBvBlastAbstract
