import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — GENERAL whole-DAG refutation grounded
  in the verified `firewall_combined_unsat`. The 3 input clause(s) and 2
  theory lemma(s) are jointly unsatisfiable; premise (a) is the resolution
  (`lratCheck` by `decide`), premise (b) is each lemma holding in every model.
  ONE global atom table and ONE shared model
  `(Nat → Int) × (Nat → Int → Int) × (Nat → Int → Bool)` span every clause
  (`m.1` = scalar valuation, `m.2.1` = function family, `m.2.2` = predicate
  family, both indexed by symbol) — the Nelson–Oppen composition shape,
  generalised from `AySoundness.CombinedExample`.
  Pure Lean 4 core; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
namespace AySoundness.Emitted.General_d4c0afded5b78993
open AySoundness

abbrev Val := (Nat → Int) × (Nat → Int → Int) × (Nat → Int → Bool)

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((m.1 0) = (m.1 1))
  | 2 => ((m.2.2 0) ((m.2.1 0) (m.1 0)))
  | 3 => ((m.2.2 0) ((m.2.1 0) (m.1 1)))
  | 4 => decide (((m.2.1 0) (m.1 0)) = ((m.2.1 0) (m.1 1)))
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [-3])]
def lemmas   : List (Cid × Clause) := [(4, [-1, 4]), (5, [-4, -2, 3])]
def proof    : List (Cid × Clause × List Int) := [(6, [], [1, 2, 3, 4, 5])]

theorem lemma_4_valid (m : Val) : clauseSat (atomVal m) [-1, 4] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h1 : (m.1 0) = (m.1 1) <;> simp [h1]

theorem lemma_5_valid (m : Val) : clauseSat (atomVal m) [-4, -2, 3] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h4 : ((m.2.1 0) (m.1 0)) = ((m.2.1 0) (m.1 1)) <;> simp [h4]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  rcases hcl with h | h <;> subst h
  · exact lemma_4_valid m
  · exact lemma_5_valid m

/-- No model satisfies all the input clauses — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

#print axioms no_model

end AySoundness.Emitted.General_d4c0afded5b78993

