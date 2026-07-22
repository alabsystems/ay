import AySoundness.Lrat
/-
  CNF-encoding soundness: justifies the firewall's propositional abstraction
  (input Boolean formula ⟶ clause set).

  ay's combined-theory refutation (AySoundness/Firewall.lean) operates on a
  *clause set* (`List Clause`, each `Clause = List Int`, semantics `clauseSat`).
  Before that, the front end abstracts the input problem to propositional atoms
  and converts the resulting Boolean skeleton to clausal form (CNF). This file
  closes the gap between those two representations: it proves that the CNF
  conversion is **model-preserving** — a model satisfies the formula iff it
  satisfies the clause set — so a clause-level `Unsat` verdict (discharged by the
  firewall) entails formula-level unsatisfiability.

  We do the EXACT, no-auxiliary-variable encoding (Option A): a direct
  distributive CNF over an NNF-free `Form` AST. Models are *not* extended with
  Tseitin variables; the formula and its CNF agree on EVERY model over the same
  variables. This is the strongest faithfulness statement available without aux
  vars (and stronger than Tseitin's mere equisatisfiability).

  MAIN RESULTS:
    * `cnf_sound`          : `Holds M f ↔ Sat M (cnf f)`   (model preservation)
    * `cnf_unsat_sound`    : `Unsat (cnf f) → ¬ ∃ M, Holds M f = true`  (firewall bridge)
  plus a concrete kernel-checked example (`Example.holds_unsat`).

  Pure Lean 4 core (no Mathlib). Reuses `Clause`/`clauseSat`/`litSat`/`Sat`/
  `Unsat` from AySoundness/Lrat.lean verbatim, so the clause sets produced here
  are *literally* the ones the firewall consumes.
-/
namespace AySoundness.Cnf

open AySoundness

/-! ## Boolean formula AST.

    Atoms are variables `n : Nat` (matching the `Nat → Bool` valuations and the
    `litSat` literal convention: positive literal `Int.ofNat n` ↦ variable `n`,
    negative literal `-(Int.ofNat n)` ↦ its negation). The well-formedness
    predicate `AtomsWf` (below) requires every atom to be `≥ 1`, so the variable
    `0` (which has no nonzero literal) is never used; this keeps every emitted
    literal nonzero (DIMACS-well-formed), matching `clauseWf`. -/

inductive Form where
  | tt                      -- ⊤
  | ff                      -- ⊥
  | atom (n : Nat)          -- propositional variable `n`
  | neg  (f : Form)         -- ¬ f
  | conj (a b : Form)       -- a ∧ b
  | disj (a b : Form)       -- a ∨ b
  deriving Repr

/-! ## Semantics: a Boolean valuation `M : Nat → Bool` evaluates a `Form`. -/

def Holds (M : Nat → Bool) : Form → Bool
  | .tt       => true
  | .ff       => false
  | .atom n   => M n
  | .neg f    => !(Holds M f)
  | .conj a b => Holds M a && Holds M b
  | .disj a b => Holds M a || Holds M b

/-! ## Clause-set satisfaction as a *Bool*, to stay constructive (no classical
    negation needed for the distribution case). It agrees with the firewall's
    propositional `Sat`. -/

def satB (M : Nat → Bool) (cs : List Clause) : Bool := cs.all (clauseSat M)

theorem satB_iff_Sat (M : Nat → Bool) (cs : List Clause) :
    satB M cs = true ↔ Sat M cs := by
  unfold satB Sat; rw [List.all_eq_true]

/-! ### satB structural facts. -/

theorem satB_append (M : Nat → Bool) (xs ys : List Clause) :
    satB M (xs ++ ys) = (satB M xs && satB M ys) := by
  unfold satB; rw [List.all_append]

/-- Distribution clause-set: `distrib ca cb` is the CNF of `(⋀ ca) ∨ (⋀ cb)`,
    obtained by OR-ing every pair of clauses. -/
def distrib (ca cb : List Clause) : List Clause :=
  ca.flatMap (fun c1 => cb.map (fun c2 => c1 ++ c2))

/-- **Key distribution lemma.** A model satisfies the distributed clause set iff
    it satisfies one of the two operand clause sets — i.e. clause distribution
    realises the Boolean OR exactly. -/
theorem satB_distrib (M : Nat → Bool) (ca cb : List Clause) :
    satB M (distrib ca cb) = (satB M ca || satB M cb) := by
  unfold satB distrib
  cases hb : (ca.all (clauseSat M) || cb.all (clauseSat M)) with
  | true =>
    rw [List.all_eq_true]
    intro c hc
    obtain ⟨c1, hc1, hmap⟩ := List.mem_flatMap.mp hc
    obtain ⟨c2, hc2, he⟩ := List.mem_map.mp hmap
    subst he
    rw [clauseSat, List.any_append]
    rcases Bool.or_eq_true _ _ |>.mp hb with ha | ha
    · have := (List.all_eq_true.mp ha) c1 hc1; rw [clauseSat] at this; rw [this]; rfl
    · have := (List.all_eq_true.mp ha) c2 hc2; rw [clauseSat] at this; rw [this]; simp
  | false =>
    rw [Bool.or_eq_false_iff] at hb
    obtain ⟨ha, hb2⟩ := hb
    rw [List.all_eq_false] at ha hb2
    obtain ⟨c1, hc1, hc1f⟩ := ha
    obtain ⟨c2, hc2, hc2f⟩ := hb2
    rw [List.all_eq_false]
    refine ⟨c1 ++ c2, ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨c1, hc1, List.mem_map.mpr ⟨c2, hc2, rfl⟩⟩
    · rw [clauseSat, List.any_append]
      rw [clauseSat] at hc1f hc2f
      rw [Bool.not_eq_true] at hc1f hc2f
      rw [hc1f, hc2f]; decide

/-! ## The direct CNF transformer.

    `cnf f` is a clause set equisatisfiable-by-the-same-model with `f`; `cnfNeg
    f` is the CNF of `¬ f` (so negation is handled by structural NNF recursion,
    no separate pass). Variable `0` is never produced as an atom literal because
    `Form.atom` uses raw `Nat`; the example below uses atoms ≥ 1, and the
    well-formedness lemma is stated for atoms ≥ 1.

    Clause-set conventions:
      * `cnf tt   = []`          (no constraints ⟹ always satisfied)
      * `cnf ff   = [[]]`        (one empty clause ⟹ never satisfied)
      * `cnf (atom n) = [[n]]`   (unit clause; literal `+n`)
      * conj ⟶ append; disj ⟶ distribute; neg ⟶ swap with `cnfNeg`. -/

mutual
  def cnf : Form → List Clause
    | .tt       => []
    | .ff       => [[]]
    | .atom n   => [[Int.ofNat n]]
    | .neg f    => cnfNeg f
    | .conj a b => cnf a ++ cnf b
    | .disj a b => distrib (cnf a) (cnf b)

  /-- CNF of the negation of the argument (De Morgan, structurally). -/
  def cnfNeg : Form → List Clause
    | .tt       => [[]]
    | .ff       => []
    | .atom n   => [[-(Int.ofNat n)]]
    | .neg f    => cnf f
    | .conj a b => distrib (cnfNeg a) (cnfNeg b)   -- ¬(a∧b) = ¬a ∨ ¬b
    | .disj a b => cnfNeg a ++ cnfNeg b            -- ¬(a∨b) = ¬a ∧ ¬b
end

/-! ## Single-atom literal semantics: a unit clause `[+n]` is satisfied iff `M n`,
    and `[-n]` iff `¬ M n` (for `n ≥ 1`, so the literal is nonzero). -/

theorem clauseSat_pos {M : Nat → Bool} {n : Nat} (hn : n ≥ 1) :
    clauseSat M [Int.ofNat n] = M n := by
  simp only [clauseSat, List.any_cons, List.any_nil, Bool.or_false, litSat]
  have hcast : Int.ofNat n = (n : Int) := rfl
  rw [hcast]
  have hpos : (n : Int) > 0 := by exact_mod_cast hn
  simp only [hpos, if_true]
  have : ((n : Int)).toNat = n := by omega
  rw [this]

theorem clauseSat_neg {M : Nat → Bool} {n : Nat} (hn : n ≥ 1) :
    clauseSat M [-(Int.ofNat n)] = !(M n) := by
  simp only [clauseSat, List.any_cons, List.any_nil, Bool.or_false, litSat]
  have hcast : Int.ofNat n = (n : Int) := rfl
  rw [hcast]
  have hpos : (n : Int) > 0 := by exact_mod_cast hn
  have hnotpos : ¬ ((-(n : Int)) > 0) := by omega
  simp only [hnotpos, if_false]
  have : ((-(-(n : Int)))).toNat = n := by omega
  rw [this]

/-! ## MAIN soundness: `cnf`/`cnfNeg` preserve models.

    Proved by simultaneous structural induction on the formula, using the
    distribution lemma for the `disj`/`cnfNeg conj` cases and `satB_append` for
    the `conj`/`cnfNeg disj` cases. We restrict atoms to `n ≥ 1` (`AtomsWf`) so
    every emitted literal is nonzero; the firewall's `clauseWf` needs exactly
    this. -/

/-- Every atom occurring in `f` is `≥ 1` (so its literals are nonzero). -/
@[reducible] def AtomsWf : Form → Prop
  | .tt       => True
  | .ff       => True
  | .atom n   => n ≥ 1
  | .neg f    => AtomsWf f
  | .conj a b => AtomsWf a ∧ AtomsWf b
  | .disj a b => AtomsWf a ∧ AtomsWf b

theorem cnf_sound_and_neg :
    ∀ (f : Form) (M : Nat → Bool), AtomsWf f →
      (satB M (cnf f) = Holds M f) ∧ (satB M (cnfNeg f) = !(Holds M f)) := by
  intro f
  induction f with
  | tt => intro M _; constructor <;> rfl
  | ff => intro M _; constructor <;> rfl
  | atom n =>
    intro M hwf
    have hn : n ≥ 1 := hwf
    refine ⟨?_, ?_⟩
    · show satB M (cnf (.atom n)) = Holds M (.atom n)
      unfold cnf Holds satB
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      exact clauseSat_pos hn
    · show satB M (cnfNeg (.atom n)) = !(Holds M (.atom n))
      unfold cnfNeg Holds satB
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      exact clauseSat_neg hn
  | neg f ih =>
    intro M hwf
    have hwf' : AtomsWf f := hwf
    obtain ⟨ih1, ih2⟩ := ih M hwf'
    refine ⟨?_, ?_⟩
    · show satB M (cnfNeg f) = !(Holds M f)
      exact ih2
    · show satB M (cnf f) = !(!(Holds M f))
      rw [ih1, Bool.not_not]
  | conj a b iha ihb =>
    intro M hwf
    obtain ⟨hwfa, hwfb⟩ := hwf
    obtain ⟨ha1, ha2⟩ := iha M hwfa
    obtain ⟨hb1, hb2⟩ := ihb M hwfb
    refine ⟨?_, ?_⟩
    · show satB M (cnf a ++ cnf b) = (Holds M a && Holds M b)
      rw [satB_append, ha1, hb1]
    · show satB M (distrib (cnfNeg a) (cnfNeg b)) = !(Holds M a && Holds M b)
      rw [satB_distrib, ha2, hb2]
      cases Holds M a <;> cases Holds M b <;> rfl
  | disj a b iha ihb =>
    intro M hwf
    obtain ⟨hwfa, hwfb⟩ := hwf
    obtain ⟨ha1, ha2⟩ := iha M hwfa
    obtain ⟨hb1, hb2⟩ := ihb M hwfb
    refine ⟨?_, ?_⟩
    · show satB M (distrib (cnf a) (cnf b)) = (Holds M a || Holds M b)
      rw [satB_distrib, ha1, hb1]
    · show satB M (cnfNeg a ++ cnfNeg b) = !(Holds M a || Holds M b)
      rw [satB_append, ha2, hb2]
      cases Holds M a <;> cases Holds M b <;> rfl

/-- **CNF soundness (model preservation).** A valuation satisfies `f` iff it
    satisfies `f`'s direct CNF — exact equisatisfiability with NO auxiliary
    variables; the formula and its clause set agree on every model. -/
theorem cnf_sound {f : Form} {M : Nat → Bool} (hwf : AtomsWf f) :
    Holds M f = true ↔ Sat M (cnf f) := by
  rw [← satB_iff_Sat, (cnf_sound_and_neg f M hwf).1]

/-- **The firewall bridge.** If the CNF clause set is `Unsat` (the verdict the
    firewall discharges via `lratCheck_sound`), then NO valuation satisfies the
    original formula — formula-level unsatisfiability. -/
theorem cnf_unsat_sound {f : Form} (hwf : AtomsWf f) (h : Unsat (cnf f)) :
    ¬ ∃ M, Holds M f = true := by
  rintro ⟨M, hM⟩
  exact h ⟨M, (cnf_sound hwf).mp hM⟩

/-- Conversely, formula-level SAT yields clause-level SAT (so the clause set is
    NOT spuriously unsat — the encoding is faithful in both directions). -/
theorem cnf_sat_complete {f : Form} {M : Nat → Bool}
    (hwf : AtomsWf f) (h : Holds M f = true) : Sat M (cnf f) :=
  (cnf_sound hwf).mp h

/-! ## Concrete kernel-checked example.

    Formula `f = (x ∧ ¬x)` with `x := atom 1`. It is unsatisfiable as a Boolean
    formula. Its direct CNF is `[[+1], [-1]]` (a unit clause and its negation),
    which is `Unsat`. We conclude `¬ ∃ M, Holds M f` via `cnf_unsat_sound`,
    kernel-checked end to end. -/
namespace Example

/-- `x ∧ ¬ x`, with `x` the propositional variable `1`. -/
def f : Form := .conj (.atom 1) (.neg (.atom 1))

theorem f_wf : AtomsWf f := ⟨by decide, by decide⟩

/-- The CNF of `x ∧ ¬x` is exactly `[[1], [-1]]`. -/
theorem cnf_f : cnf f = [[(1 : Int)], [(-1 : Int)]] := by decide

/-- `[[1], [-1]]` is propositionally unsatisfiable. -/
theorem cnf_f_unsat : Unsat (cnf f) := by
  rw [cnf_f]
  rintro ⟨M, hM⟩
  have h1 : clauseSat M [(1 : Int)] = true := hM [(1 : Int)] (by simp)
  have h2 : clauseSat M [(-1 : Int)] = true := hM [(-1 : Int)] (by simp)
  -- `clauseSat M [1]` reduces to `M 1`; `clauseSat M [-1]` reduces to `!(M 1)`.
  simp only [clauseSat, List.any_cons, List.any_nil, Bool.or_false, litSat] at h1 h2
  -- h1 : M 1 = true   (literal 1 > 0)   ;   h2 : !(M 1) = true  (literal -1 ≤ 0)
  simp only [show ((1 : Int) > 0) = True by simp, show ((-1 : Int) > 0) = False by simp,
    if_true, if_false] at h1 h2
  simp only [show (1 : Int).toNat = 1 by rfl, show ((-(-1 : Int)).toNat) = 1 by rfl] at h1 h2
  rw [h1] at h2
  simp at h2

/-- **End-to-end verdict, kernel-checked:** no valuation makes `x ∧ ¬x` hold —
    derived purely from the clause-level `Unsat` through the CNF bridge. -/
theorem holds_unsat : ¬ ∃ M, Holds M f = true :=
  cnf_unsat_sound f_wf cnf_f_unsat

/-- A satisfiable witness in the other direction: `x ∨ ¬x` holds under any model
    and its CNF (`[]`, the empty clause SET) is trivially satisfied — showing the
    statement is non-vacuous (CNF is not always unsat). -/
def g : Form := .disj (.atom 1) (.neg (.atom 1))

theorem g_wf : AtomsWf g := ⟨by decide, by decide⟩

theorem g_holds (M : Nat → Bool) : Holds M g = true := by
  show (Holds M (.atom 1) || Holds M (.neg (.atom 1))) = true
  show (M 1 || !(M 1)) = true
  cases M 1 <;> rfl

theorem g_cnf_sat (M : Nat → Bool) : Sat M (cnf g) :=
  cnf_sat_complete g_wf (g_holds M)

end Example
end AySoundness.Cnf