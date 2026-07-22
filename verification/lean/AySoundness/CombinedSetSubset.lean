import AySoundness.Firewall
/-
  SET subset refutation through the verified firewall — the target shape for the
  set emitter tier (the VALID-LEMMA fragment of QF_SET).

  For `x ∈ s ∧ x ∉ t ∧ s ⊆ t ⊢ unsat` (ay's `subset_refuted_by_ground_witness`
  case), the theory lemma is the subset DEFINITION instantiated at the GROUND
  witness `x`:

      s ⊆ t  →  (x ∈ s → x ∈ t)        i.e. clause  ¬(s⊆t) ∨ ¬(x∈s) ∨ (x∈t)

  This is a genuinely VALID clause under the set interpretation (`s ⊆ t` means
  `∀ e, e∈s → e∈t`), so it discharges `firewall_combined_unsat`'s `hvalid`
  premise directly — NO Skolemization. (The transitivity case `A⊆B ∧ B⊆C ∧
  ¬(A⊆C)` needs a FRESH witness for the negated subset, which is a Skolem clause —
  NOT valid — and so needs a separate Skolemization extension to the firewall;
  that case is out of scope here.)

  Sets are modeled as characteristic functions `Nat → Bool`; subset as the
  `∀`-implication. The `∀ e` is over an infinite domain, so atom 3's Bool value
  uses `Classical.propDecidable` (allowed kernel axiom `Classical.choice`) — hence
  `atomVal` is `noncomputable`. This is fine: `lratCheck`/`tableWf`/`proofWf` are
  purely propositional over the clause structure and never touch `atomVal`, so the
  `by decide` obligations are unaffected; only `lemmas_valid` (proved by logic)
  and the conclusion mention it.

  `#print axioms no_model` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`,
  no `native_decide`. Pure Lean 4 core.
-/
namespace AySoundness.CombinedSetSubset
open AySoundness

attribute [local instance] Classical.propDecidable

/-- A QF_SET model: two sets (characteristic functions over `Nat`) and the ground
    element `x` named in the assertions. -/
structure Val where
  s : Nat → Bool
  t : Nat → Bool
  x : Nat

/-- Atoms: `1 ↦ x ∈ s`, `2 ↦ x ∈ t`, `3 ↦ s ⊆ t`. -/
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => m.s m.x
  | 2 => m.t m.x
  | 3 => decide (∀ e, m.s e = true → m.t e = true)
  | _ => false

/-- `x∈s` (1), `x∉t` (¬2), `s⊆t` (3). -/
def original : List (Cid × Clause) := [(1, [1]), (2, [-2]), (3, [3])]
/-- The subset definition at the ground witness: `¬(s⊆t) ∨ ¬(x∈s) ∨ (x∈t)`. -/
def lemmas   : List (Cid × Clause) := [(4, [-3, -1, 2])]
/-- Unit-propagate `1, -2, 3` then conflict on the lemma → empty clause. -/
def proof    : List (Cid × Clause × List Int) := [(5, [], [1, 2, 3, 4])]

/-- The subset-instantiation lemma holds in EVERY set model: if `s ⊆ t` and
    `x ∈ s` then `x ∈ t`. -/
theorem subset_lemma_valid (m : Val) : clauseSat (atomVal m) [-3, -1, 2] = true := by
  by_cases h3 : (∀ e, m.s e = true → m.t e = true)
  · by_cases h1 : m.s m.x = true
    · have h2 : m.t m.x = true := h3 m.x h1
      simp [clauseSat, litSat, atomVal, h2]
    · simp [clauseSat, litSat, atomVal, h1]
  · simp [clauseSat, litSat, atomVal, h3]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact subset_lemma_valid m

/-- No set model satisfies `x∈s ∧ x∉t ∧ s⊆t` — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.CombinedSetSubset
