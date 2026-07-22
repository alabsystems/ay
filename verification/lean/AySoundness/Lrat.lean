/-
  Soundness of ay's emitted LRAT/RUP checker (T0.2 of the development design notes).

  ay emits a self-contained Lean file defining `lratCheck` and a theorem
  `lratCheck original proof = true := by native_decide`. That proves the CHECKER
  ACCEPTS the proof — but NOT that acceptance implies unsatisfiability. This file
  proves the missing keystone:

      lratCheck_sound : Wf … → lratCheck original proof = true → Unsat (clauses original)

  Composing it with the per-problem `lratCheck … = true` fact yields a real,
  kernel-checked theorem that the input formula is unsatisfiable. The solver's
  search is never trusted — only this checker + Lean's kernel.

  Pure Lean 4 core (no Mathlib). The checker definitions mirror
  `crates/ay-sat/src/lean_export.rs::write_kernel_prelude`.
-/
namespace AySoundness

abbrev Clause := List Int
abbrev Cid := Nat

/-! ## Semantics: total models over variables (`Nat`); literals are nonzero `Int`. -/

/-- Positive literal `l` is true iff `M l`; negative `-v` iff `¬ M v`. -/
def litSat (M : Nat → Bool) (l : Int) : Bool :=
  if l > 0 then M l.toNat else !(M (-l).toNat)

def clauseSat (M : Nat → Bool) (c : Clause) : Bool := c.any (litSat M)

def Sat (M : Nat → Bool) (cs : List Clause) : Prop := ∀ c ∈ cs, clauseSat M c = true
def Unsat (cs : List Clause) : Prop := ¬ ∃ M, Sat M cs

/-! ## Checker (mirrors lean_export.rs). `Assign` is a partial assignment. -/

def negLit (l : Int) : Int := -l
abbrev Assign := List Int
def litTrue  (a : Assign) (l : Int) : Bool := a.contains l
def litFalse (a : Assign) (l : Int) : Bool := a.contains (negLit l)

def findUnit : Assign → Clause → Option Int → Option Int
  | _, [], u => u
  | a, l :: rest, u =>
    if litTrue a l then none
    else if litFalse a l then findUnit a rest u
    else match u with
      | none => findUnit a rest (some l)
      | some _ => none

def clauseFalsified (a : Assign) (c : Clause) : Bool := c.all (fun l => litFalse a l)

def lookupClause (table : List (Cid × Clause)) (id : Cid) : Option Clause :=
  (table.find? (fun p => p.fst == id)).map (·.snd)

def rupStep (table : List (Cid × Clause)) (a : Assign) (hints : List Int) : Bool :=
  match hints with
  | [] => false
  | h :: rest =>
    if h ≤ 0 then rupStep table a rest
    else match lookupClause table h.toNat with
      | none => false
      | some c =>
        if clauseFalsified a c then true
        else match findUnit a c none with
          | none => false
          | some l => rupStep table (l :: a) rest

def rupCheck (table : List (Cid × Clause)) (target : Clause) (hints : List Int) : Bool :=
  rupStep table (target.map negLit) hints

def checkStep (table : List (Cid × Clause)) (step : Cid × Clause × List Int) : Bool :=
  rupCheck table step.2.1 step.2.2

def lratCheckAux : List (Cid × Clause) → List (Cid × Clause × List Int) → Bool
  | _, [] => false
  | table, [last] => last.2.1.isEmpty && checkStep table last
  | table, s :: rest =>
    if checkStep table s then lratCheckAux ((s.1, s.2.1) :: table) rest
    else false

def lratCheck (original : List (Cid × Clause)) (proof : List (Cid × Clause × List Int)) : Bool :=
  lratCheckAux original proof

def clauses (table : List (Cid × Clause)) : List Clause := table.map (·.2)

/-! ## Well-formedness: literals are nonzero (DIMACS). -/

@[reducible] def clauseWf (c : Clause) : Prop := ∀ l ∈ c, l ≠ 0
@[reducible] def tableWf (t : List (Cid × Clause)) : Prop := ∀ p ∈ t, clauseWf p.2

/-! ## Model consistency with a partial assignment. -/

def consistent (M : Nat → Bool) (a : Assign) : Prop := ∀ l ∈ a, litSat M l = true
def tableSat (M : Nat → Bool) (t : List (Cid × Clause)) : Prop :=
  ∀ p ∈ t, clauseSat M p.2 = true

/-! ## Basic semantic lemmas. -/

theorem litSat_neg {M : Nat → Bool} {l : Int} (hl : l ≠ 0) :
    litSat M (negLit l) = !(litSat M l) := by
  unfold litSat negLit
  by_cases h : l > 0
  · have h3 : (- -l) = l := by omega
    simp [h, h3] <;> omega
  · simp [h] <;> omega

theorem mem_of_contains {a : Assign} {x : Int} (h : a.contains x = true) : x ∈ a := by
  simpa using h

theorem consistent_litFalse {M : Nat → Bool} {a : Assign} {l : Int}
    (hc : consistent M a) (hf : litFalse a l = true) (hl : l ≠ 0) :
    litSat M l = false := by
  have hmem : negLit l ∈ a := mem_of_contains (by simpa [litFalse] using hf)
  have hpos := hc (negLit l) hmem
  rw [litSat_neg hl] at hpos
  cases hcase : litSat M l with
  | false => rfl
  | true => rw [hcase] at hpos; simp at hpos

/-- consistency extends by a literal `M` makes true. -/
theorem consistent_cons {M : Nat → Bool} {a : Assign} {l : Int}
    (hc : consistent M a) (hl : litSat M l = true) : consistent M (l :: a) := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · subst h; exact hl
  · exact hc x h

/-! ## findUnit characterization. -/

/-- With a `some` accumulator, `findUnit` succeeds only by returning that
    accumulator, and only when every clause literal is false. -/
theorem findUnit_some_acc {a : Assign} :
    ∀ (c : Clause) (j k : Int),
      findUnit a c (some j) = some k → k = j ∧ ∀ l' ∈ c, litFalse a l' = true := by
  intro c
  induction c with
  | nil => intro j k h; simp [findUnit] at h; exact ⟨h.symm, by simp⟩
  | cons l rest ih =>
    intro j k h
    unfold findUnit at h
    by_cases ht : litTrue a l = true
    · simp [ht] at h
    · by_cases hf : litFalse a l = true
      · simp [ht, hf] at h
        obtain ⟨hk, hr⟩ := ih j k h
        refine ⟨hk, ?_⟩
        intro l' hl'
        rcases List.mem_cons.mp hl' with e | e
        · subst e; exact hf
        · exact hr l' e
      · simp [ht, hf] at h

/-- With a `none` accumulator, `findUnit = some k` means `k` is a clause literal
    and every other clause literal is false under `a`. -/
theorem findUnit_none {a : Assign} :
    ∀ (c : Clause) (k : Int),
      findUnit a c none = some k → k ∈ c ∧ ∀ l' ∈ c, l' = k ∨ litFalse a l' = true := by
  intro c
  induction c with
  | nil => intro k h; simp [findUnit] at h
  | cons l rest ih =>
    intro k h
    unfold findUnit at h
    by_cases ht : litTrue a l = true
    · simp [ht] at h
    · by_cases hf : litFalse a l = true
      · simp [ht, hf] at h
        obtain ⟨hmem, hall⟩ := ih k h
        refine ⟨List.mem_cons_of_mem _ hmem, ?_⟩
        intro l' hl'
        rcases List.mem_cons.mp hl' with e | e
        · subst e; right; exact hf
        · exact hall l' e
      · simp [ht, hf] at h
        obtain ⟨hk, hr⟩ := findUnit_some_acc rest l k h
        subst hk
        refine ⟨List.mem_cons_self, ?_⟩
        intro l' hl'
        rcases List.mem_cons.mp hl' with e | e
        · subst e; left; rfl
        · right; exact hr l' e

/-! ## Lookups land in the table; clause helpers. -/

theorem lookup_mem {table : List (Cid × Clause)} {id : Cid} {c : Clause}
    (h : lookupClause table id = some c) : ∃ p ∈ table, p.2 = c := by
  unfold lookupClause at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨p, hfind, hsnd⟩ := h
  exact ⟨p, List.mem_of_find?_eq_some hfind, hsnd⟩

theorem clauseSat_mem {M : Nat → Bool} {c : Clause} (h : clauseSat M c = true) :
    ∃ l ∈ c, litSat M l = true := by
  unfold clauseSat at h; exact List.any_eq_true.mp h

theorem clauseFalsified_all {a : Assign} {c : Clause} (h : clauseFalsified a c = true) :
    ∀ l ∈ c, litFalse a l = true := by
  unfold clauseFalsified at h; intro l hl; exact (List.all_eq_true.mp h) l hl

/-- A clause all-false under a consistent assignment cannot be model-satisfied. -/
theorem clauseFalsified_contra {M : Nat → Bool} {a : Assign} {c : Clause}
    (hsat : clauseSat M c = true) (hfals : clauseFalsified a c = true)
    (hc : consistent M a) (hcw : clauseWf c) : False := by
  obtain ⟨l, hl, hlsat⟩ := clauseSat_mem hsat
  have hfalse := consistent_litFalse hc (clauseFalsified_all hfals l hl) (hcw l hl)
  rw [hfalse] at hlsat; simp at hlsat

/-- The propagated unit literal is entailed by a model of the clause. -/
theorem unit_entailed {M : Nat → Bool} {a : Assign} {c : Clause} {l : Int}
    (hsat : clauseSat M c = true) (hfu : findUnit a c none = some l)
    (hc : consistent M a) (hcw : clauseWf c) : litSat M l = true := by
  obtain ⟨l', hl', hl'sat⟩ := clauseSat_mem hsat
  obtain ⟨_, hall⟩ := findUnit_none c l hfu
  rcases hall l' hl' with e | hfalse
  · subst e; exact hl'sat
  · have hf := consistent_litFalse hc hfalse (hcw l' hl')
    rw [hf] at hl'sat; simp at hl'sat

/-! ## RUP soundness: if propagation reaches conflict, the assignment is
    inconsistent with any model of the table. -/

theorem rupStep_sound {M : Nat → Bool} {table : List (Cid × Clause)}
    (hts : tableSat M table) (htw : tableWf table) :
    ∀ (hints : List Int) (a : Assign),
      rupStep table a hints = true → consistent M a → False := by
  intro hints
  induction hints with
  | nil => intro a h _; simp [rupStep] at h
  | cons hh rest ih =>
    intro a h hc
    unfold rupStep at h
    by_cases hle : hh ≤ 0
    · simp [hle] at h; exact ih a h hc
    · simp [hle] at h
      cases hlook : lookupClause table hh.toNat with
      | none => rw [hlook] at h; simp at h
      | some c =>
        rw [hlook] at h
        obtain ⟨p, hpmem, hpc⟩ := lookup_mem hlook
        have hcsat : clauseSat M c = true := hpc ▸ hts p hpmem
        have hcwf : clauseWf c := hpc ▸ htw p hpmem
        by_cases hfals : clauseFalsified a c = true
        · exact clauseFalsified_contra hcsat hfals hc hcwf
        · simp [hfals] at h
          cases hfu : findUnit a c none with
          | none => rw [hfu] at h; simp at h
          | some l =>
            rw [hfu] at h
            have hlsat : litSat M l = true := unit_entailed hcsat hfu hc hcwf
            exact ih (l :: a) h (consistent_cons hc hlsat)

/-- RUP soundness: an accepted RUP step yields an entailed clause. -/
theorem rupCheck_sound {M : Nat → Bool} {table : List (Cid × Clause)} {target : Clause}
    {hints : List Int} (hts : tableSat M table) (htw : tableWf table)
    (htgw : clauseWf target) (h : rupCheck table target hints = true) :
    clauseSat M target = true := by
  cases hns : clauseSat M target with
  | true => rfl
  | false =>
    exfalso
    unfold rupCheck at h
    refine rupStep_sound hts htw hints (target.map negLit) h ?_
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨l, hl, hxe⟩ := hx
    subst hxe
    rw [litSat_neg (htgw l hl)]
    have hlf : litSat M l = false := by
      cases hh : litSat M l with
      | false => rfl
      | true =>
        have hcs : clauseSat M target = true := List.any_eq_true.mpr ⟨l, hl, hh⟩
        rw [hns] at hcs; simp at hcs
    rw [hlf]; rfl

@[reducible] def proofWf (proof : List (Cid × Clause × List Int)) : Prop := ∀ s ∈ proof, clauseWf s.2.1

/-- Soundness of the step walk: an accepted proof refutes any model of the table. -/
theorem lratCheckAux_sound {M : Nat → Bool} :
    ∀ (proof : List (Cid × Clause × List Int)) (table : List (Cid × Clause)),
      tableWf table → proofWf proof →
      lratCheckAux table proof = true → tableSat M table → False := by
  intro proof
  induction proof with
  | nil => intro table _ _ h _; simp [lratCheckAux] at h
  | cons s rest ih =>
    intro table htw hpw h hts
    have hsw : clauseWf s.2.1 := hpw s List.mem_cons_self
    cases rest with
    | nil =>
      simp only [lratCheckAux, Bool.and_eq_true] at h
      obtain ⟨hempty, hcheck⟩ := h
      have hsat : clauseSat M s.2.1 = true := rupCheck_sound hts htw hsw hcheck
      have hnil : s.2.1 = [] := by
        cases hh : s.2.1 with
        | nil => rfl
        | cons => rw [hh] at hempty; simp at hempty
      rw [hnil] at hsat; simp [clauseSat] at hsat
    | cons r rs =>
      simp only [lratCheckAux] at h
      by_cases hcheck : checkStep table s = true
      · rw [if_pos hcheck] at h
        have hsat : clauseSat M s.2.1 = true := rupCheck_sound hts htw hsw hcheck
        have htw' : tableWf ((s.1, s.2.1) :: table) := by
          intro p hp; rcases List.mem_cons.mp hp with e | e
          · subst e; exact hsw
          · exact htw p e
        have hts' : tableSat M ((s.1, s.2.1) :: table) := by
          intro p hp; rcases List.mem_cons.mp hp with e | e
          · subst e; exact hsat
          · exact hts p e
        have hpw' : proofWf (r :: rs) := fun x hx => hpw x (List.mem_cons_of_mem _ hx)
        exact ih ((s.1, s.2.1) :: table) htw' hpw' h hts'
      · rw [if_neg hcheck] at h; simp at h

/-! ## The keystone: checker acceptance implies unsatisfiability. -/

theorem lratCheck_sound {original : List (Cid × Clause)}
    {proof : List (Cid × Clause × List Int)}
    (htw : tableWf original) (hpw : proofWf proof)
    (h : lratCheck original proof = true) : Unsat (clauses original) := by
  rintro ⟨M, hM⟩
  unfold lratCheck at h
  refine lratCheckAux_sound (M := M) proof original htw hpw h ?_
  intro p hp
  have hmem : p.2 ∈ clauses original := by
    unfold clauses; exact List.mem_map.mpr ⟨p, hp, rfl⟩
  exact hM p.2 hmem

end AySoundness
