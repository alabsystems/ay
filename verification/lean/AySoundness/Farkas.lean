/-
  Soundness of Farkas / LIA-LRA conflict certificates (T2, first theory validator,
  the development design notes §5.2).

  A linear-arithmetic conflict is a set of constraints `eᵢ ≤ 0` that is jointly
  infeasible. ay's Farkas certificate (`TheoryLemmaKind::LraFarkas`,
  `FarkasAnnotation`) is non-negative coefficients `λᵢ ≥ 0` whose weighted sum of
  the premises is a positive constant `c` — `∑ᵢ λᵢ·eᵢ ≡ c > 0` — a manifest
  contradiction (`0 < c ≤ 0`).

  We prove the soundness PRINCIPLE here (`farkas_sound`): any non-negative
  combination of satisfied `≤ 0` premises that is a positive constant refutes the
  premises. The per-problem certificate identity `∑ λᵢ·eᵢ = c` is decidable for
  concrete linear forms and discharged by `omega` (see `Example`), exactly
  mirroring the `lratCheck_sound` + `decide` split. Integer coefficients (an
  LRA certificate scales to clear denominators); pure Lean 4 core.
-/
namespace AySoundness.Farkas

/-- A model maps variables to integers. -/
abbrev Model := Nat → Int

/-- A linear form, identified with its value under a model (abstract: the
    soundness argument needs only the value, not the syntax). -/
abbrev LinForm := Model → Int

/-- `∑ᵢ λᵢ · eᵢ` evaluated at `M` (truncating zip; aligned in practice). -/
def wsum (lam : List Int) (es : List LinForm) (M : Model) : Int :=
  ((lam.zip es).map (fun p => p.1 * p.2 M)).sum

/-- A non-negative combination of `≤ 0` premises is `≤ 0`. -/
theorem wsum_nonpos {M : Model} :
    ∀ (lam : List Int) (es : List LinForm),
      (∀ x ∈ lam, 0 ≤ x) → (∀ e ∈ es, e M ≤ 0) → wsum lam es M ≤ 0 := by
  intro lam
  induction lam with
  | nil => intro es _ _; simp [wsum]
  | cons l ls ih =>
    intro es hlam hes
    cases es with
    | nil => simp [wsum]
    | cons e esr =>
      have hl : 0 ≤ l := hlam l List.mem_cons_self
      have he : e M ≤ 0 := hes e List.mem_cons_self
      have hterm : l * e M ≤ 0 := by
        have := Int.mul_le_mul_of_nonneg_left he hl
        simpa using this
      have hrest : wsum ls esr M ≤ 0 :=
        ih esr (fun x hx => hlam x (List.mem_cons_of_mem _ hx))
               (fun y hy => hes y (List.mem_cons_of_mem _ hy))
      have : wsum (l :: ls) (e :: esr) M = l * e M + wsum ls esr M := by
        simp [wsum]
      omega

/-- **Farkas soundness.** If `λ ≥ 0` and the weighted sum of the premises is a
    positive constant `c`, then no model satisfies all premises `eᵢ ≤ 0`. -/
theorem farkas_sound (es : List LinForm) (lam : List Int) (c : Int)
    (hlam : ∀ x ∈ lam, 0 ≤ x) (hc : 0 < c)
    (hcomb : ∀ M, wsum lam es M = c) :
    ¬ ∃ M, ∀ e ∈ es, e M ≤ 0 := by
  rintro ⟨M, hM⟩
  have hle : wsum lam es M ≤ 0 := wsum_nonpos lam es hlam hM
  rw [hcomb M] at hle
  omega

/-! ## Concrete example: `x ≤ 1 ∧ x ≥ 2` is unsatisfiable. -/

/-- `x ≤ 1`  ⟺  `x - 1 ≤ 0`. -/
def e_le1 : LinForm := fun M => M 0 - 1
/-- `x ≥ 2`  ⟺  `2 - x ≤ 0`. -/
def e_ge2 : LinForm := fun M => 2 - M 0

/-- Refuted by the Farkas certificate `λ = [1,1]`: `(x-1) + (2-x) = 1 > 0`.
    The certificate identity is discharged by `omega`. -/
theorem x_le1_and_ge2_unsat : ¬ ∃ M, ∀ e ∈ [e_le1, e_ge2], e M ≤ 0 :=
  farkas_sound [e_le1, e_ge2] [1, 1] 1
    (by decide) (by decide)
    (by intro M; simp [wsum, e_le1, e_ge2]; omega)

end AySoundness.Farkas
