import AySoundness.Firewall
/-
  GENERATED mixed-theory firewall PoC — EUF + LIA.

  This file is the OUTPUT SHAPE of the general `emit_general_firewall_lean`
  emitter (NOT the hand-tuned `CombinedExample`). Everything here is structured
  exactly as a code generator would mechanically produce it from a strict
  (`trust_count == 0`) `Proof`:

    * `Val` is a FLAT right-nested product of per-shared-symbol carriers, ordered
      by a canonical symbol index (component 0,1,… ); no human-chosen tuple.
    * `atomVal` is a SINGLE `match` on the destructured product and the global
      atom id `n`, one arm per atom id, each arm dispatching into the owning
      theory's renderer over the SAME shared components (so the LIA variable `a`
      and the EUF argument `a` are literally `m.0` in both arms — this projection
      sharing IS the Nelson–Oppen interface, no purification term needed).
    * `original` / `lemmas` / `proof` are transcribed verbatim from the proof DAG
      (Assume → original, TheoryLemma → lemmas, Resolution/Step → RUP `proof`).
    * `lemmas_valid` is assembled from one `lemma_<id>_valid` theorem per lemma,
      each closed by ITS OWN theory tactic (LIA: omega; EUF: by_cases+subst+simp),
      then dispatched by an N-way `rcases` over `clauses lemmas`.

  Worked problem (combined EUF+LIA, both theories load-bearing):
      a ≤ b  ∧  b ≤ a  ∧  f a ≠ f b      (UNSAT).

  Canonical shared-symbol table the generator built:
      symbol 0 : a  (Int,        LIA)
      symbol 1 : b  (Int,        LIA)
      symbol 2 : f  (Int → Int,  EUF uninterpreted function)
  ⇒ Val := Int × Int × (Int → Int), destructured as ⟨s0, s1, s2⟩.

  Global atom table (one Nat id per distinct atomic TermId, across ALL clauses):
      atom 1 : (a ≤ b)      LIA          over s0,s1
      atom 2 : (b ≤ a)      LIA          over s0,s1
      atom 3 : (f a = f b)  EUF          over s2,s0,s1
      atom 4 : (a = b)      SHARED EQ    over s0,s1   (the N-O interface atom)

  `#print axioms no_model` ⊆ {propext, Classical.choice, Quot.sound} — verified.
  Pure Lean 4 core: omega / by_cases / subst / simp only. No native_decide, no sorry.
-/
namespace AySoundness.GeneralFirewallPoc
open AySoundness

/-- (Generated) Val product: one factor per shared symbol, canonical order.
    s0 = a : Int, s1 = b : Int, s2 = f : Int → Int. -/
abbrev Val := Int × Int × (Int → Int)

/-- (Generated) per-atom dispatch. Single `match` on the destructured product and
    the global atom id; each arm renders the atom's native predicate over the
    shared components. Atom 4 (`s0 = s1`) is the shared-equality interface atom —
    rendered identically to any other, no special-casing. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n, m with
  | 1, (s0, s1, _)  => decide (s0 ≤ s1)        -- LIA atom over s0,s1
  | 2, (s0, s1, _)  => decide (s1 ≤ s0)        -- LIA atom over s0,s1
  | 3, (s0, s1, s2) => decide (s2 s0 = s2 s1)  -- EUF atom: fn-factor s2 applied to shared s0,s1
  | 4, (s0, s1, _)  => decide (s0 = s1)        -- SHARED equality (N-O interface)
  | _, _            => false

/-- (Generated) `original` = the Assume clauses, atoms abstracted to global ids. -/
def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [-3])]

/-- (Generated) `lemmas` = the validated TheoryLemma clauses, in DAG order.
    id 4 : LIA lemma  [-1,-2,4]  (LraFarkas / antisymmetry)
    id 5 : EUF lemma  [-4,3]     (EufCongruent) -/
def lemmas : List (Cid × Clause) := [(4, [-1, -2, 4]), (5, [-4, 3])]

/-- (Generated) `proof` = RUP chain to the empty clause; hint ids are the
    contributing original+lemma clause ids (DAG topo-order). -/
def proof : List (Cid × Clause × List Int) := [(6, [], [1, 2, 4, 5, 3])]

/-- (Generated) lemma 4 validity — owning theory LIA, tactic = omega. -/
theorem lemma_4_valid (m : Val) : clauseSat (atomVal m) [-1, -2, 4] = true := by
  obtain ⟨s0, s1, s2⟩ := m
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h1 : s0 ≤ s1 <;> by_cases h2 : s1 ≤ s0 <;> simp [h1, h2] <;> omega

/-- (Generated) lemma 5 validity — owning theory EUF, tactic = by_cases+subst+simp. -/
theorem lemma_5_valid (m : Val) : clauseSat (atomVal m) [-4, 3] = true := by
  obtain ⟨s0, s1, s2⟩ := m
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h : s0 = s1
  · subst h; simp
  · simp [h]

/-- (Generated) assembled premise (b): N-way membership split, one bullet per
    lemma in `lemmas` order. -/
theorem lemmas_valid :
    ∀ c ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) c = true := by
  intro c hc m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with h | h <;> subst h
  · exact lemma_4_valid m
  · exact lemma_5_valid m

/-- (Generated) verdict — fixed firewall tail. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

#print axioms no_model

end AySoundness.GeneralFirewallPoc
