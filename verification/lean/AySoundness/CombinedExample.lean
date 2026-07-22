import AySoundness.Firewall
/-
  A GENUINELY combined EUF + LIA conflict, refuted through the verified firewall
  (`AySoundness.firewall_combined_unsat`) — a concrete demonstration of
  Nelson–Oppen combination SOUNDNESS where BOTH theories are load-bearing.

  Input problem (over a combined model `(a, b, f) : Int × Int × (Int → Int)`):

      a ≤ b   ∧   b ≤ a   ∧   f a ≠ f b.

  Neither theory alone refutes it: the LIA part `a ≤ b ∧ b ≤ a` is satisfiable,
  and the EUF part `f a ≠ f b` is satisfiable. The contradiction needs BOTH,
  connected by the SHARED EQUALITY `a = b` (atom 4 — the Nelson–Oppen interface):

    * LIA lemma  [-1,-2,4]:  `a ≤ b ∧ b ≤ a → a = b`   (antisymmetry, by `omega`)
    * EUF lemma  [-4, 3]:    `a = b → f a = f b`        (congruence, by `congrArg`)

  Propositional resolution closes it:  [1],[2],[-3],[-1,-2,4],[-4,3]  ⊢  ⊥
  (`1`,`2` ⟹ `4` via the LIA lemma, `4` ⟹ `3` via the EUF lemma, `3` vs `-3`).
  REMOVE EITHER LEMMA and atom `4` (resp. `3`) can no longer be derived, so both
  are load-bearing — this is a real cross-theory conflict, not an EUF-only one
  with a decorative LIA lemma.

  `firewall_combined_unsat` discharges premise (a) (`lratCheck … = true` by
  `decide`) and premise (b) (`lemmas_valid`: each lemma holds in every combined
  model — LIA by `omega`, EUF by `congrArg`), concluding no combined model
  satisfies the input. Pure Lean 4 core.
-/
namespace AySoundness.CombinedExample
open AySoundness

/-- Combined model: `(a, b, f)` carries the LIA values `a, b` and the EUF
    function `f`. -/
abbrev Val := Int × Int × (Int → Int)

/-- Atom interpretation: `1 ↦ a≤b`, `2 ↦ b≤a` (LIA), `3 ↦ f a = f b` (EUF),
    `4 ↦ a = b` (the SHARED equality connecting the theories). -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match m, n with
  | (a, b, _), 1 => decide (a ≤ b)
  | (a, b, _), 2 => decide (b ≤ a)
  | (a, b, f), 3 => decide (f a = f b)
  | (a, b, _), 4 => decide (a = b)
  | _,         _ => false

/-- Input clauses: `a ≤ b`, `b ≤ a`, `f a ≠ f b`. -/
def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [-3])]

/-- Theory lemmas: the LIA antisymmetry lemma (id 4) and the EUF congruence
    lemma (id 5). Both load-bearing; `4 = (a = b)` is the shared interface. -/
def lemmas : List (Cid × Clause) := [(4, [-1, -2, 4]), (5, [-4, 3])]

/-- LRAT/RUP refutation: derive `4` (from `1`,`2`, LIA lemma), then `3` (from
    `4`, EUF lemma), conflicting with `-3`. -/
def proof : List (Cid × Clause × List Int) := [(6, [], [1, 2, 4, 5, 3])]

/-- LIA lemma validity: `a ≤ b ∧ b ≤ a → a = b` holds in every model (`omega`). -/
theorem lia_lemma_valid (m : Val) : clauseSat (atomVal m) [-1, -2, 4] = true := by
  obtain ⟨a, b, f⟩ := m
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h1 : a ≤ b <;> by_cases h2 : b ≤ a <;> simp [h1, h2] <;> omega

/-- EUF lemma validity: `a = b → f a = f b` holds in every model (`congrArg`). -/
theorem euf_lemma_valid (m : Val) : clauseSat (atomVal m) [-4, 3] = true := by
  obtain ⟨a, b, f⟩ := m
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h : a = b
  · subst h; simp
  · simp [h]

/-- Both theory lemmas are valid in every combined model — premise (b) of the
    firewall, supplied by the LIA and EUF reasoning. -/
theorem lemmas_valid :
    ∀ c ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) c = true := by
  intro c hc m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with h | h <;> subst h
  · exact lia_lemma_valid m
  · exact euf_lemma_valid m

/-- **Combination soundness, demonstrated.** No combined model `(a, b, f)`
    satisfies `a ≤ b ∧ b ≤ a ∧ f a ≠ f b` — concluded through the verified
    `firewall_combined_unsat` from the resolution proof + the two (genuinely
    cross-theory, both load-bearing) lemmas. -/
theorem no_combined_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

/-- The same combined fact as a plain mathematical statement — `omega` (LIA) gives
    `a = b`, then `congrArg` (EUF) gives `f a = f b`, contradicting `f a ≠ f b`.
    Genuinely needs both theories: dropping `a ≤ b ∧ b ≤ a` (LIA) or `f a ≠ f b`
    (EUF) makes it satisfiable. -/
theorem combined_conflict_unsat :
    ¬ ∃ (a b : Int) (f : Int → Int), a ≤ b ∧ b ≤ a ∧ f a ≠ f b := by
  rintro ⟨a, b, f, h1, h2, h3⟩
  have hab : a = b := by omega
  exact h3 (by rw [hab])

end AySoundness.CombinedExample
