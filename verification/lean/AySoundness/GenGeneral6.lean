import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — GENERAL whole-DAG refutation grounded
  in the verified `firewall_combined_unsat`. The 3 input clause(s) and 3
  theory lemma(s) are jointly unsatisfiable; premise (a) is the resolution
  (`lratCheck` by `decide`), premise (b) is each lemma holding in every model.
  ONE global atom table and ONE shared model `(Nat → Int) × (Nat → Int → Int)`
  span every clause (`m.1` = scalar valuation, `m.2` = the uninterpreted-function
  FAMILY indexed by symbol) — the Nelson–Oppen composition shape, generalised
  from `AySoundness.CombinedExample` (arithmetic by `omega`, congruence by `simp`).
  Pure Lean 4 core; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
namespace AySoundness.Emitted.General_293113edd029dc05
open AySoundness

abbrev Val := (Nat → Int) × (Nat → Int → Int)

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((m.1 0) = (m.1 1))
  | 2 => decide (((m.2 0) (m.1 0)) = ((m.2 1) (m.1 0)))
  | 3 => decide (((m.2 0) (m.1 1)) = ((m.2 1) (m.1 1)))
  | 4 => decide (((m.2 0) (m.1 0)) = ((m.2 0) (m.1 1)))
  | 5 => decide (((m.2 1) (m.1 0)) = ((m.2 1) (m.1 1)))
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [-3])]
def lemmas   : List (Cid × Clause) := [(4, [-1, 4]), (5, [-1, 5]), (6, [-4, -5, -2, 3])]
def proof    : List (Cid × Clause × List Int) := [(7, [], [1, 2, 3, 4, 5, 6])]

theorem lemma_4_valid (m : Val) : clauseSat (atomVal m) [-1, 4] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h1 : (m.1 0) = (m.1 1) <;> simp [h1]

theorem lemma_5_valid (m : Val) : clauseSat (atomVal m) [-1, 5] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h1 : (m.1 0) = (m.1 1) <;> simp [h1]

theorem lemma_6_valid (m : Val) : clauseSat (atomVal m) [-4, -5, -2, 3] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h4 : ((m.2 0) (m.1 0)) = ((m.2 0) (m.1 1)) <;> by_cases h5 : ((m.2 1) (m.1 0)) = ((m.2 1) (m.1 1)) <;> by_cases h2 : ((m.2 0) (m.1 0)) = ((m.2 1) (m.1 0)) <;> by_cases h3 : ((m.2 0) (m.1 1)) = ((m.2 1) (m.1 1)) <;> simp [h4, h5, h2, h3] <;> omega

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  rcases hcl with h | h | h <;> subst h
  · exact lemma_4_valid m
  · exact lemma_5_valid m
  · exact lemma_6_valid m

/-- No model satisfies all the input clauses — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

#print axioms no_model

end AySoundness.Emitted.General_293113edd029dc05

