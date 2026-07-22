/-
  Soundness of the theory of generic sequences (QF_SEQ): length / concat /
  positional-read / UPDATE axioms (the development design notes; the
  sequence-theory validator that underwrites deductive-checks's `Seq` reasoning).

  Unlike the string theory (`StringThy`, where the element sort is a fixed
  codepoint alphabet), deductive-checks's `Seq` is a *generic-element* sequence: it
  supports `len`, `nth` (partial positional read), `concat`, and crucially
  `update` (functional in-bounds element replacement; out-of-range = no-op).
  deductive-checks emits update-bounds verification conditions over this theory —
  read-your-write, update-elsewhere-preserved, and length-preservation — and a
  conflict that uses ONLY instances of the following axioms (plus congruence /
  equality reasoning) is sound iff the axioms hold in the intended model:

    * LEN-CAT       `len (concat s t) = len s + len t`        (length is additive);
    * LEN-UPD       `len (update s i v) = len s`              (update preserves length);
    * NTH-UPD-SAME  `i < len s → nth (update s i v) i = some v`     (read-your-write);
    * NTH-UPD-OTHER `i ≠ j → nth (update s i v) j = nth s j`        (update elsewhere kept);
    * NTH-CAT-LEFT  `i < len s → nth (concat s t) i = nth s i`      (content / positional).

  We fix the *standard list model* — a sequence over element type `α` is the
  free monoid `List α`, `len` is `List.length`, `concat` is `++`, `nth` is the
  partial positional read `s[i]?`, and `update` is `List.set` (which is the
  out-of-range-no-op functional update that matches `Seq.update`'s semantics) —
  and prove every axiom holds there, GENERICALLY in the element type `α`. Hence
  any propositionally-derived conflict built from these axiom instances refutes a
  genuinely unsatisfiable constraint set: the model is forced and the axioms are
  valid (`seq_axioms_sound`).

  We prove the soundness PRINCIPLE (`seq_axioms_sound`): in the standard list
  model the axioms are simultaneously valid for EVERY element type `α`, sequence,
  position and value; the per-problem grounding (which sequence is which) is the
  solver's congruence closure. We also refute the concrete update-bounds
  conflicts deductive-checks emits (`len_update_conflict`, `nth_update_same_conflict`,
  …) and exhibit decidable positional witnesses over a concrete list, mirroring
  the `farkas_sound` (principle) + concrete-`decide` example split of
  `Farkas.lean` / `ArrayThy.lean` / `StringThy.lean`.

  Pure Lean 4 core (no Mathlib). The model definitions mirror the standard list
  semantics used by ay's QF_SEQ decision procedure and deductive-checks's `Seq`.
-/
namespace AySoundness.SeqThy

/-! ## The standard list model.

We generalize over an ARBITRARY element type `α` (a generic sequence element
sort, exactly as deductive-checks's `Seq<T>` is generic). A sequence is a `List α`, so
`len` is `List.length`, `concat` is `++`, the partial positional read `nth` is
`s[i]?` (`none` out of range), and `update` is `List.set`, the functional update
that replaces the element at `i` when `i` is in range and is a no-op otherwise.
This is the canonical model ay's QF_SEQ decision procedure — and the `Seq`
fragment deductive-checks relies on — is proved sound against. -/

/-- A sequence over element type `α`: a finite list of elements. -/
abbrev Seq (α : Type) := List α

/-- `len s` is the number of elements in `s`. -/
def len {α : Type} (s : Seq α) : Nat := s.length

/-- `nth s i` reads the element at position `i`, `none` when out of range — the
    standard partial positional access (`s[i]?`). -/
def nth {α : Type} (s : Seq α) (i : Nat) : Option α := s[i]?

/-- `concat s t` appends `t` after `s` (the monoid operation). -/
def concat {α : Type} (s t : Seq α) : Seq α := s ++ t

/-- `update s i v` replaces the element at position `i` with `v`. In-range it is
    the functional update; out of range it is a no-op — exactly the semantics of
    `Seq.update` (`List.set`). -/
def update {α : Type} (s : Seq α) (i : Nat) (v : α) : Seq α := s.set i v

/-! ## The sequence axioms, valid in the list model. -/

/-- **LEN-CAT.** Length is additive over concatenation:
    `len (concat s t) = len s + len t`. -/
theorem len_concat {α : Type} (s t : Seq α) :
    len (concat s t) = len s + len t := by
  simp [len, concat, List.length_append]

/-- **LEN-UPD.** `update` preserves length: `len (update s i v) = len s`. This is
    the length-preservation fact deductive-checks's update-bounds reasoning depends on —
    writing an element never changes the sequence's length. -/
theorem len_update {α : Type} (s : Seq α) (i : Nat) (v : α) :
    len (update s i v) = len s := by
  simp [len, update, List.length_set]

/-- **NTH-UPD-SAME** (read-your-write): for an in-range index `i < len s`,
    reading the just-written position returns the written value:
    `nth (update s i v) i = some v`. The side condition `i < len s` is the
    in-bounds guard deductive-checks discharges before applying read-your-write. -/
theorem nth_update_same {α : Type} (s : Seq α) (i : Nat) (v : α)
    (h : i < len s) : nth (update s i v) i = some v := by
  simp only [nth, update]
  exact List.getElem?_set_self (by simpa [len] using h)

/-- **NTH-UPD-OTHER** (update elsewhere preserved): updating position `i` does
    not affect a *different* position `j ≠ i`:
    `nth (update s i v) j = nth s j`. -/
theorem nth_update_other {α : Type} (s : Seq α) (i j : Nat) (v : α)
    (h : i ≠ j) : nth (update s i v) j = nth s j := by
  simp only [nth, update]
  exact List.getElem?_set_ne h

/-- **NTH-CAT-LEFT** (content / positional): reading a position inside the left
    operand of a concatenation ignores the right operand: for `i < len s`,
    `nth (concat s t) i = nth s i`. -/
theorem nth_concat_left {α : Type} (s t : Seq α) (i : Nat)
    (h : i < len s) : nth (concat s t) i = nth s i := by
  simp only [nth, concat]
  exact List.getElem?_append_left (by simpa [len] using h)

/-! ## The soundness principle.

`seq_axioms_sound` packages the core sequence axioms as a single validity
statement: for the standard list `len` / `nth` / `concat` / `update`, ALL the
axioms hold for every element type, sequence, position and value. This is the
theory content the QF_SEQ validator — and deductive-checks's `Seq.update`/bounds VCs —
rely on, so any conflict built solely from these axiom instances is sound. -/

/-- **Sequence theory soundness.** In the standard list model the core QF_SEQ
    axioms — length-additivity over concat, length-preservation under update,
    read-your-write, update-elsewhere-preserved, and the left content axiom —
    hold simultaneously, generically in the element type `α`. A conflict that
    uses only these axiom instances therefore refutes a genuinely unsatisfiable
    constraint set, which directly underwrites deductive-checks's `Seq.update`/bounds
    verification conditions. -/
theorem seq_axioms_sound :
    (∀ (α : Type) (s t : Seq α), len (concat s t) = len s + len t) ∧
    (∀ (α : Type) (s : Seq α) (i : Nat) (v : α), len (update s i v) = len s) ∧
    (∀ (α : Type) (s : Seq α) (i : Nat) (v : α),
        i < len s → nth (update s i v) i = some v) ∧
    (∀ (α : Type) (s : Seq α) (i j : Nat) (v : α),
        i ≠ j → nth (update s i v) j = nth s j) ∧
    (∀ (α : Type) (s t : Seq α) (i : Nat),
        i < len s → nth (concat s t) i = nth s i) :=
  ⟨fun α => @len_concat α,
   fun α => @len_update α,
   fun α => @nth_update_same α,
   fun α => @nth_update_other α,
   fun α => @nth_concat_left α⟩

/-! ## Conflict abstraction.

ay / deductive-checks represent the result of a sequence decision as: a set of
length / content / update literals is UNSAT. We discharge each conflict shape
from the axioms above so a kernel-checked `False` witnesses the soundness of the
emitted conflict — mirroring the `farkas_sound` / `array_axioms_sound`
principles. -/

/-- **Length-additivity conflict.** The literal `len (concat s t) ≠ len s + len t`
    is unsatisfiable. -/
theorem len_concat_conflict {α : Type} (s t : Seq α) :
    ¬ (len (concat s t) ≠ len s + len t) :=
  fun h => h (len_concat s t)

/-- **Update-length conflict.** The literal `len (update s i v) ≠ len s` is
    unsatisfiable: ay/deductive-checks's "update preserves length" bounds conflict is
    sound. -/
theorem len_update_conflict {α : Type} (s : Seq α) (i : Nat) (v : α) :
    ¬ (len (update s i v) ≠ len s) :=
  fun h => h (len_update s i v)

/-- **Read-your-write conflict.** With `i < len s`, the literal
    `nth (update s i v) i ≠ some v` is unsatisfiable: ay/deductive-checks's
    read-your-write conflict is sound. -/
theorem nth_update_same_conflict {α : Type} (s : Seq α) (i : Nat) (v : α)
    (h : i < len s) : ¬ (nth (update s i v) i ≠ some v) :=
  fun hne => hne (nth_update_same s i v h)

/-- **Update-elsewhere conflict.** With `i ≠ j`, the literal
    `nth (update s i v) j ≠ nth s j` is unsatisfiable: ay/deductive-checks's
    update-frame conflict is sound. -/
theorem nth_update_other_conflict {α : Type} (s : Seq α) (i j : Nat) (v : α)
    (h : i ≠ j) : ¬ (nth (update s i v) j ≠ nth s j) :=
  fun hne => hne (nth_update_other s i j v h)

/-- **Content conflict.** With `i < len s`, the literal
    `nth (concat s t) i ≠ nth s i` is unsatisfiable: ay's element-propagation
    conflict is sound. -/
theorem nth_concat_left_conflict {α : Type} (s t : Seq α) (i : Nat)
    (h : i < len s) : ¬ (nth (concat s t) i ≠ nth s i) :=
  fun hne => hne (nth_concat_left s t i h)

/-! ## Concrete, kernel-checked, NON-vacuous examples.

Each refutes a *real* conflict over a concrete ground sequence; the
contradictions are discharged by pure-kernel `decide` on the decidable
`List`/`Option` equalities. We use the concrete element type `Int` and the
non-trivial three-element sequence `[10, 20, 30]`, so the witnesses are not
vacuous (the read values are concrete non-`none` elements). -/

/-- A concrete non-trivial sequence over `Int`. -/
def s3 : Seq Int := [10, 20, 30]

/-- Concrete update-length fact: updating index `1` of a length-3 sequence keeps
    length `3`, so the bounds conflict `len (update s3 1 99) ≠ len s3` is refuted.
    Kernel-checked by `decide`. -/
theorem ex_len_update_value : len (update s3 1 99) = len s3 := by decide

/-- The same refutation via the general principle (not just `decide`). -/
theorem ex_len_update_via_principle : ¬ (len (update s3 1 99) ≠ len s3) :=
  len_update_conflict s3 1 99

/-- Concrete read-your-write fact: position `1 < len s3 = 3`, so reading the
    just-written index returns `some 99`. The written value is non-trivial and
    differs from the original element `some 20`, so the conflict
    `nth (update s3 1 99) 1 ≠ some 99` is refuted. Kernel-checked by `decide`. -/
theorem ex_nth_update_same_value : nth (update s3 1 99) 1 = some 99 := by decide

/-- The same read-your-write fact follows from the general principle, with the
    in-bounds side condition `1 < len s3` discharged by `decide`. -/
theorem ex_nth_update_same_via_principle : nth (update s3 1 99) 1 = some 99 :=
  nth_update_same s3 1 99 (by decide)

/-- Non-vacuity witness that the write is REAL: before the update position `1`
    held `some 20`, after it holds `some 99`, and `some 20 ≠ some 99`. So
    read-your-write changes the read value — the axiom is not vacuous. -/
theorem ex_update_changes_value : nth s3 1 ≠ nth (update s3 1 99) 1 := by decide

/-- Concrete update-elsewhere fact: updating index `1` leaves index `0`
    untouched, so `nth (update s3 1 99) 0 = nth s3 0 = some 10`. Kernel-checked,
    refuting the frame conflict `nth (update s3 1 99) 0 ≠ nth s3 0`. -/
theorem ex_nth_update_other_value : nth (update s3 1 99) 0 = nth s3 0 := by decide

/-- The same via the general principle, with the distinctness side condition
    `1 ≠ 0` discharged by `decide`. -/
theorem ex_nth_update_other_via_principle : nth (update s3 1 99) 0 = nth s3 0 :=
  nth_update_other s3 1 0 99 (by decide)

/-- Concrete content fact: position `1 < len s3` reads `some 20` in both `s3` and
    `concat s3 [40]`, so the content conflict `nth (concat s3 [40]) 1 ≠ nth s3 1`
    is refuted. The read value `some 20` is non-trivial. -/
theorem ex_nth_concat_value : nth (concat s3 [40]) 1 = nth s3 1 := by decide

/-- The same content fact via the general principle, with `1 < len s3` by `decide`. -/
theorem ex_nth_concat_via_principle : nth (concat s3 [40]) 1 = nth s3 1 :=
  nth_concat_left s3 [40] 1 (by decide)

/-- Out-of-range non-vacuity witness: updating at an out-of-bounds index `5` of a
    length-3 sequence is a no-op — both length AND every element are preserved —
    confirming `update`'s `List.set` semantics (no spurious extension), so the
    in-bounds guard on read-your-write is genuinely necessary. -/
theorem ex_update_out_of_range_noop : update s3 5 99 = s3 := by decide

end AySoundness.SeqThy