import AySoundness.Firewall
/-
  AUTO-EMITTED by ay (lean_firewall.rs) — GENERAL whole-DAG refutation grounded
  in the verified `firewall_combined_unsat`. The 3 input clause(s) and 1
  theory lemma(s) are jointly unsatisfiable; premise (a) is the resolution
  (`lratCheck` by `decide`), premise (b) is each lemma holding in every model.
  ONE global atom table and ONE shared model `(Nat → Int) × (Nat → Int → Bool)`
  span every clause (`m.1` = scalar valuation, `m.2` = the uninterpreted-predicate
  FAMILY indexed by symbol) — the Nelson–Oppen composition shape, generalised
  from `AySoundness.CombinedExample` (arithmetic by `omega`, predicate congruence by `simp`).
  Pure Lean 4 core; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
namespace AySoundness.Emitted.General_b87c8f3e896e0fb2
open AySoundness

abbrev Val := (Nat → Int) × (Nat → Int → Bool)

def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide ((m.1 0) = (m.1 1))
  | 2 => ((m.2 0) (m.1 0))
  | 3 => ((m.2 0) (m.1 1))
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [-3])]
def lemmas   : List (Cid × Clause) := [(4, [-1, -2, 3])]
def proof    : List (Cid × Clause × List Int) := [(5, [], [1, 2, 3, 4])]

theorem lemma_4_valid (m : Val) : clauseSat (atomVal m) [-1, -2, 3] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h1 : (m.1 0) = (m.1 1) <;> simp [h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact lemma_4_valid m

/-- No model satisfies all the input clauses — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

#print axioms no_model

end AySoundness.Emitted.General_b87c8f3e896e0fb2

