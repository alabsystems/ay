import AySoundness.Firewall
/-
  GENERATED THREE-theory firewall PoC — EUF + LIA + BV (bit-vector).

  Same emitter OUTPUT SHAPE as `GeneralFirewallPoc` (flat product `Val`, single
  `match`-based `atomVal` keyed by global atom id, per-lemma `lemma_<id>_valid`
  assembled by an N-way `rcases`), now stressing the generality of the pattern
  with a THIRD theory and THREE shared-interface atoms wiring the theories
  together. All three theory lemmas are load-bearing.

  Worked problem (UNSAT), over shared symbols
      s0 = a : Int,  s1 = b : Int,  s2 = f : Int → Int,  s3 = x : BitVec 4 :

      a ≤ b            (LIA)
      b ≤ a            (LIA)
      x = 0#4          (BV)
      f a ≠ f b        (EUF, asserted negatively)
      (f a + x.toNat as the bridge — see atoms below)

  How the three theories chain (each lemma single-theory in its REASONING; the
  shared atoms are the Nelson–Oppen interface):

    LIA lemma  [-1,-2,4]   : a ≤ b ∧ b ≤ a → a = b           (antisymmetry, omega)
    EUF lemma  [-4,3]      : a = b → f a = f b               (congruence, congrArg)
    BV  lemma  [-5,6]      : x = 0#4 → (x &&& 1#4) = 0#4     (bit fact, decide)

  and the propositional skeleton additionally has the input facts that make
  ATOM 3 (`f a = f b`) and ATOM 6 (`(x &&& 1#4)=0#4`) jointly contradictory with
  a fourth input clause `[-3,-6]` (an asserted disjunction `f a ≠ f b ∨ (x&1)≠0`
  — i.e. the user asserted ¬(f a = f b ∧ (x&1)=0)). Resolution:

    1,2 ⟹ 4 (LIA) ⟹ 3 (EUF);  5 ⟹ 6 (BV);  3 ∧ 6 vs [-3,-6] ⊢ ⊥.

  REMOVE the LIA lemma and 4 is underivable; remove the EUF lemma and 3 is;
  remove the BV lemma and 6 is — so all three are load-bearing.

  `#print axioms no_model` ⊆ {propext, Classical.choice, Quot.sound} — verified.
  Pure Lean 4 core: omega / by_cases+subst+simp / decide. No native_decide, no sorry.
-/
namespace AySoundness.GeneralFirewallPoc3
open AySoundness

/-- (Generated) Val product: one factor per shared symbol, canonical order.
    s0 = a : Int, s1 = b : Int, s2 = f : Int → Int, s3 = x : BitVec 4. -/
abbrev Val := Int × Int × (Int → Int) × BitVec 4

/-- (Generated) per-atom dispatch. Single `match`; each arm renders the atom's
    native predicate over the shared components.
      1 : a ≤ b              (LIA, s0 s1)
      2 : b ≤ a              (LIA, s0 s1)
      3 : f a = f b          (EUF, s2 s0 s1)
      4 : a = b              (SHARED EQ — LIA/EUF interface, s0 s1)
      5 : x = 0#4            (BV, s3)
      6 : (x &&& 1#4) = 0#4  (BV, s3) -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n, m with
  | 1, (s0, s1, _,  _)  => decide (s0 ≤ s1)
  | 2, (s0, s1, _,  _)  => decide (s1 ≤ s0)
  | 3, (s0, s1, s2, _)  => decide (s2 s0 = s2 s1)
  | 4, (s0, s1, _,  _)  => decide (s0 = s1)
  | 5, (_,  _,  _,  s3) => decide (s3 = 0#4)
  | 6, (_,  _,  _,  s3) => decide ((s3 &&& 1#4) = 0#4)
  | _, _                => false

/-- (Generated) `original` = the Assume clauses.
    [1]:a≤b [2]:b≤a [5]:x=0 [-3,-6]: ¬(f a=f b ∧ (x&1)=0). -/
def original : List (Cid × Clause) :=
  [(1, [1]), (2, [2]), (3, [5]), (4, [-3, -6])]

/-- (Generated) `lemmas` = validated TheoryLemma clauses, in DAG order.
    id 5 : LIA  [-1,-2,4]   id 6 : EUF  [-4,3]   id 7 : BV  [-5,6]. -/
def lemmas : List (Cid × Clause) :=
  [(5, [-1, -2, 4]), (6, [-4, 3]), (7, [-5, 6])]

/-- (Generated) RUP chain to the empty clause; hints are the contributing
    original+lemma clause ids in DAG topo-order.
    1,2 (orig) + 5 (LIA) ⟹ 4; 4 + 6 (EUF) ⟹ 3; 3 (orig:x=0=clause3) + 7 (BV) ⟹ 6;
    3 ∧ 6 vs clause 4 [-3,-6] ⊢ ⊥. -/
def proof : List (Cid × Clause × List Int) :=
  [(8, [], [1, 2, 5, 6, 3, 7, 4])]

/-- (Generated) lemma 5 validity — owning theory LIA, tactic = omega. -/
theorem lemma_5_valid (m : Val) : clauseSat (atomVal m) [-1, -2, 4] = true := by
  obtain ⟨s0, s1, s2, s3⟩ := m
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h1 : s0 ≤ s1 <;> by_cases h2 : s1 ≤ s0 <;> simp [h1, h2] <;> omega

/-- (Generated) lemma 6 validity — owning theory EUF, tactic = by_cases+subst+simp. -/
theorem lemma_6_valid (m : Val) : clauseSat (atomVal m) [-4, 3] = true := by
  obtain ⟨s0, s1, s2, s3⟩ := m
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h : s0 = s1
  · subst h; simp
  · simp [h]

/-- (Generated) lemma 7 validity — owning theory BV, tactic = revert+decide
    over the single finite BitVec factor. -/
theorem lemma_7_valid (m : Val) : clauseSat (atomVal m) [-5, 6] = true := by
  obtain ⟨s0, s1, s2, s3⟩ := m
  -- only atoms 5,6 occur; both depend solely on the finite factor s3. The
  -- `match n, m` dispatch reduces on the literal ids 5/6, leaving a goal over
  -- s3 alone, which `decide` enumerates over BitVec 4.
  simp only [clauseSat, litSat, atomVal, List.any_cons, List.any_nil,
    Int.reduceNeg, gt_iff_lt, Int.reduceLT, ↓reduceIte, Int.reduceToNat,
    Bool.or_false]
  revert s3; decide

/-- (Generated) assembled premise (b): N-way membership split, one bullet per
    lemma in `lemmas` order. -/
theorem lemmas_valid :
    ∀ c ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) c = true := by
  intro c hc m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h <;> subst h
  · exact lemma_5_valid m
  · exact lemma_6_valid m
  · exact lemma_7_valid m

/-- (Generated) verdict — fixed firewall tail. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

#print axioms no_model

end AySoundness.GeneralFirewallPoc3
