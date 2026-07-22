import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — GENERAL whole-DAG refutation grounded
  in the verified `firewall_combined_unsat`. The 4 input clause(s) and 2
  theory lemma(s) are jointly unsatisfiable; premise (a) is the resolution
  (`lratCheck` by `decide`), premise (b) is each lemma holding in every model.
  ONE global atom table and ONE shared model `Nat → Int` span every clause —
  the Nelson–Oppen composition shape, generalised from
  `AySoundness.CombinedExample`. Modeling uninterpreted constants as integers is
  sound for equality-only reasoning (any realizable equivalence relation is
  realizable over the integers).
  Pure Lean 4 core; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
namespace AySoundness.Emitted.General_f059cb8695a120f4
open AySoundness

abbrev Val := Nat → Int

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((m 0) ≤ (m 1))
  | 2 => decide ((m 1) ≤ (m 2))
  | 3 => decide ((m 2) ≤ (m 3))
  | 4 => decide ((m 0) ≤ (m 3))
  | 5 => decide ((m 0) ≤ (m 2))
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [3]), (4, [-4])]
def lemmas   : List (Cid × Clause) := [(5, [-1, -2, 5]), (6, [-5, -3, 4])]
def proof    : List (Cid × Clause × List Int) := [(7, [], [1, 2, 3, 4, 5, 6])]

theorem lemma_5_valid (m : Val) : clauseSat (atomVal m) [-1, -2, 5] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h1 : (m 0) ≤ (m 1) <;> by_cases h2 : (m 1) ≤ (m 2) <;> by_cases h5 : (m 0) ≤ (m 2) <;> simp [h1, h2, h5] <;> omega

theorem lemma_6_valid (m : Val) : clauseSat (atomVal m) [-5, -3, 4] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h5 : (m 0) ≤ (m 2) <;> by_cases h3 : (m 2) ≤ (m 3) <;> by_cases h4 : (m 0) ≤ (m 3) <;> simp [h5, h3, h4] <;> omega

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  rcases hcl with h | h <;> subst h
  · exact lemma_5_valid m
  · exact lemma_6_valid m

/-- No model satisfies all the input clauses — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

#print axioms no_model

end AySoundness.Emitted.General_f059cb8695a120f4

