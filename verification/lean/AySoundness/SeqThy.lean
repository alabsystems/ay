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

/-! ## `seq.at` — the single-element positional subsequence.

The SMT `seq.at s i` returns a SEQUENCE of length 0 or 1 (the 1-element
subsequence at position `i`, or the empty sequence if `i` is out of range) — the
generic-element mirror of `str.at`. It is *not* the element read `nth`; it
re-wraps the read into a length-≤1 sequence. We model it as `(s[i]?).toList`
over `Seq α`, and `seq.unit v` (the singleton constructor) as `[v]`. The conflict
corollaries below are the `¬(…)`-shaped literals the emitter grounds in for the
`seqat` false-`sat` regressions. -/

/-- `seq.unit v`: the one-element sequence `[v]` (the SMT singleton constructor). -/
def unit {α : Type} (v : α) : Seq α := [v]

/-- `seq.at` at position `i`: the 1-element (or empty) subsequence, modelled as
    the length-≤1 sequence `(s[i]?).toList`. -/
def seqAt {α : Type} (s : Seq α) (i : Nat) : Seq α := (s[i]?).toList

/-- **`seq.at` length bound.** `len (seq.at s i) ≤ 1` — always: the read is `none`
    (empty, length 0) out of range or `some x` (length 1) in range. -/
theorem len_seqAt_le_one {α : Type} (s : Seq α) (i : Nat) :
    len (seqAt s i) ≤ 1 := by
  unfold seqAt len
  cases s[i]? <;> simp

/-- **`seq.at` in-range length.** For an in-range index `i < len s`,
    `len (seq.at s i) = 1` — it wraps exactly one element. This is the length-1
    fact that clashes with `len (as seq.empty) = 0` in the `iteofseq` false-`sat`
    conflict (the `ite`-false branch). -/
theorem len_seqAt_of_lt {α : Type} (s : Seq α) (i : Nat) (h : i < len s) :
    len (seqAt s i) = 1 := by
  unfold seqAt len
  rw [List.getElem?_eq_getElem (by simpa [len] using h)]
  simp

/-- **`seq.unit` value.** `len (seq.unit v) = 1`, and the ground content is `[v]`;
    a `seq.unit` is never empty. -/
theorem len_unit {α : Type} (v : α) : len (unit v) = 1 := by
  simp [len, unit]

/-- **`seq.unit` injectivity.** `seq.unit a = seq.unit b → a = b`: distinct values
    build distinct singletons. This is the value-propagation step that turns a
    sequence equation `seq.unit a = seq.unit b` into the element equation the
    LIA / Bool core refutes. -/
theorem unit_injective {α : Type} {a b : α} (h : unit a = unit b) : a = b := by
  simpa [unit] using h

/-! ### `seq.at` conflict corollaries. -/

/-- **`seq.at` length conflict.** Asserting `len (seq.at s i) ≥ 2` is unsat. -/
theorem seqAt_len_ge_two_conflict {α : Type} (s : Seq α) (i : Nat) :
    ¬ (len (seqAt s i) ≥ 2) := by
  have h := len_seqAt_le_one s i
  omega

/-- **`seq.unit` distinctness conflict.** With `a ≠ b`, the literal
    `seq.unit a = seq.unit b` is unsatisfiable — ay's singleton value-conflict is
    sound. -/
theorem unit_ne_conflict {α : Type} {a b : α} (hab : a ≠ b) :
    ¬ (unit a = unit b) :=
  fun h => hab (unit_injective h)

/-- **`seq.at`-vs-empty length conflict.** For an in-range index, the literal set
    `{ seq.at s i = t, t = as seq.empty }` is unsatisfiable: the LHS has length
    `1`, the empty sequence length `0`. Stated directly on lengths — the shape the
    `iteofseq` `ite`-false branch grounds in. -/
theorem seqAt_ne_empty_conflict {α : Type} (s : Seq α) (i : Nat) (h : i < len s) :
    ¬ (len (seqAt s i) = len ([] : Seq α)) := by
  have h1 := len_seqAt_of_lt s i h
  have h2 : len ([] : Seq α) = 0 := rfl
  omega

/-! ### Ground-eval bridge for the TOTAL `seq.nth`.

SMT `seq.nth s i` is a *total* function (it returns an element directly; the
out-of-range value is unconstrained). For an in-range concrete read it agrees
with the partial `nth` (`s[i]?`) via `some`, which is all the emitter needs: it
binds `seq.nth v2 v10 = x` from the ground read and hands the resulting numeric
literal to the LIA core. `nthD s i d` models the total read with an (irrelevant,
in-range) default `d`. -/

/-- Total positional read with default `d` (SMT `seq.nth`). In range it is the
    element; out of range it is `d`. -/
def nthD {α : Type} (s : Seq α) (i : Nat) (d : α) : α := (s[i]?).getD d

/-- **`seq.nth` ↔ `nth` bridge.** If the partial read `nth s i = some v` (i.e. `i`
    is in range with value `v`), then the total read `seq.nth s i = v`,
    regardless of the default. This is the value-binding the emitter uses. -/
theorem nthD_eq_of_nth {α : Type} (s : Seq α) (i : Nat) (d v : α)
    (h : nth s i = some v) : nthD s i d = v := by
  simp only [nth] at h
  simp [nthD, h]

/-! ### Concrete, kernel-checked `seq.at` / `seq.nth` conflict witnesses. -/

/-- The ground sequence `seq.++ (seq.unit 3) (seq.unit -2) (seq.unit 3) = [3,-2,3]`
    over `Int`, from the `qf_slia_seqat_symbolic_pinned` regression. -/
def sat3 : Seq Int := [3, -2, 3]

/-- Concrete `seq.at` read: `seq.at [3,-2,3] 1 = [-2] = seq.unit (-2)`. Length
    exactly `1`, so the read wraps a real element and is non-vacuous. -/
theorem ex_seqAt_value : seqAt sat3 1 = unit (-2) := by decide

/-- **`qf_slia_seqat_symbolic_pinned` conflict.** The literal
    `seq.unit 1 = seq.at [3,-2,3] 1` is unsatisfiable: the read is `seq.unit (-2)`,
    and `seq.unit 1 = seq.unit (-2)` forces `1 = -2` (by `unit_injective`), which
    is false. Kernel-checked. -/
theorem ex_seqat_pinned_conflict : ¬ (unit (1 : Int) = seqAt sat3 1) := by decide

/-- The same via the general principle: rewrite the read to `seq.unit (-2)` and
    close with `seq.unit` injectivity + `(1 : Int) ≠ -2`. -/
theorem ex_seqat_pinned_via_principle : ¬ (unit (1 : Int) = seqAt sat3 1) := by
  rw [ex_seqAt_value]
  exact unit_ne_conflict (by decide)

/-- The length-2 sequence `v1 = seq.++ (seq.unit false) (seq.unit false)` over
    `Bool`, from the `iteofseq` regression. -/
def vff : Seq Bool := [false, false]

/-- Concrete `seq.at` read over `Bool`: `seq.at [false,false] 0 = [false] =
    seq.unit false`. -/
theorem ex_seqAt_bool_value : seqAt vff 0 = unit false := by decide

/-- **`iteofseq` `ite`-true branch conflict.** `seq.at [false,false] 0 =
    seq.unit true` is unsatisfiable: the read is `seq.unit false`, and
    `seq.unit false = seq.unit true` forces `false = true`. -/
theorem ex_seqat_ite_true_conflict : ¬ (seqAt vff 0 = unit true) := by decide

/-- **`iteofseq` `ite`-false branch conflict.** `seq.at [false,false] 0 =
    as seq.empty` is unsatisfiable: the read has length `1` (`0 < len [false,false]`),
    the empty sequence length `0`. Kernel-checked, and also derivable from
    `seqAt_ne_empty_conflict` (length-1 vs length-0). -/
theorem ex_seqat_ite_false_conflict : ¬ (seqAt vff 0 = ([] : Seq Bool)) := by decide

/-- The `ite`-false branch via the general principle (length argument). -/
theorem ex_seqat_ite_false_via_principle :
    ¬ (len (seqAt vff 0) = len ([] : Seq Bool)) :=
  seqAt_ne_empty_conflict vff 0 (by decide)

/-- The length-1 sequence `v2 = seq.unit 0` over `Int`, from the
    `seq_falsesat_nth_ground_eval` regression. -/
def v2nth : Seq Int := [0]

/-- Concrete in-range partial read: `nth (seq.unit 0) 0 = some 0`, the ground-eval
    bridge input. -/
theorem ex_nth_ground_zero : nth v2nth 0 = some (0 : Int) := by decide

/-- Concrete total read via the bridge: `seq.nth (seq.unit 0) 0 = 0` (any default),
    binding the value the LIA core needs. -/
theorem ex_nthD_ground_zero (d : Int) : nthD v2nth 0 d = 0 :=
  nthD_eq_of_nth v2nth 0 d 0 ex_nth_ground_zero

/-- **`seq_falsesat_nth_ground_eval` conflict.** The literal set
    `{ nth (seq.unit 0) 0 = some v, (-3 - 4) ≥ v }` is unsatisfiable: the ground
    read forces `v = 0`, and `-7 ≥ 0` is false in LIA. Kernel-checked (the
    seq ground-eval hands the conflict to pure LIA). -/
theorem ex_seq_nth_ground_lia_conflict :
    ¬ (∃ v : Int, nth v2nth 0 = some v ∧ ((-3 : Int) - 4) ≥ v) := by
  rintro ⟨v, hv, hle⟩
  rw [ex_nth_ground_zero] at hv
  simp at hv
  omega

/-! ## `seq.suffixof` — aligned-last-element content conflict.

The SMT `seq.suffixof a b` holds iff `a` is a suffix of `b` — there is a prefix
`p` with `b = p ++ a` (element sort generic). We model it as `suffixOf x y :=
∃ p, y = p ++ x`, and prove the KEY firewall fact: a non-empty suffix shares the
whole's LAST element. So if the alleged suffix `x` ends in `a` but the whole `y`
ends in a *different* `b`, the suffix relation is impossible — the
`seq_falsesat_suffixof_elem_mismatch` conflict (`[-1,-1]` cannot be a suffix of
`v3 ++ [1]`: last elements `-1` vs `1` differ).

These three definitions/lemmas are the kernel-verified building block prepped in
`scratchpad/leanseq/Suffix.lean` (kept verbatim); `suffix_append_last_conflict`
is the emitter-facing corollary that specializes the whole to a `p ++ t` shape
(an arbitrary prefix `p` followed by a ground non-empty tail `t`), which is
exactly the `(seq.++ v3 v1)` structure the firewall grounds in. -/

/-- `seq.suffixof x y`: `x` is a suffix of `y` — some prefix `p` gives `y = p ++ x`. -/
def suffixOf {α : Type} (x y : List α) : Prop := ∃ p : List α, y = p ++ x

/-- **A non-empty suffix shares the last element.** If `x` is a suffix of `y` and
    `x` is non-empty, then `y` and `x` have the same `getLast?`. -/
theorem getLast?_of_suffix {α : Type} (x y : List α)
    (h : suffixOf x y) (hne : x ≠ []) : y.getLast? = x.getLast? := by
  obtain ⟨p, rfl⟩ := h
  rw [List.getLast?_append]
  cases hx : x.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hx) hne
  | some a => simp

/-- **Suffix last-element conflict.** A non-empty `x` ending in `a` cannot be a
    suffix of a `y` ending in a different `b`. -/
theorem suffix_last_conflict {α : Type} (x y : List α) (a b : α)
    (h : suffixOf x y) (hxne : x ≠ [])
    (hx : x.getLast? = some a) (hy : y.getLast? = some b) (hab : a ≠ b) : False := by
  have := getLast?_of_suffix x y h hxne
  rw [hx, hy] at this
  exact hab (Option.some.inj this.symm)

/-- **Suffix-of-`p ++ t` last-element conflict** (emitter-facing). If `x` is a
    suffix of `p ++ t` for an ARBITRARY prefix `p` and a ground non-empty tail
    `t`, then `x` and `t` share the last element: `p ++ t` ends where `t` ends. So
    a non-empty `x` ending in `a ≠ b = last t` can be a suffix of `p ++ t` for NO
    prefix `p` — the `(seq.suffixof x (seq.++ … t))` firewall shape. -/
theorem suffix_append_last_conflict {α : Type} (x p t : List α) (a b : α)
    (h : suffixOf x (p ++ t)) (hxne : x ≠ []) (htne : t ≠ [])
    (hx : x.getLast? = some a) (ht : t.getLast? = some b) (hab : a ≠ b) : False := by
  have hy : (p ++ t).getLast? = some b := by
    rw [getLast?_of_suffix t (p ++ t) ⟨p, rfl⟩ htne]; exact ht
  exact suffix_last_conflict x (p ++ t) a b h hxne hx hy hab

/-! ### Concrete, kernel-checked `seq.suffixof` conflict witness. -/

/-- **`seq_falsesat_suffixof_elem_mismatch` conflict.** `v2 = [-1,-1]` is asserted
    to be a suffix of `v3 ++ [1]` (with `v1 = [1]` non-empty). But `[-1,-1]` ends
    in `-1` and `v3 ++ [1]` ends in `1` for EVERY `v3`, and `-1 ≠ 1`, so no `v3`
    satisfies the suffix constraint — refuted for all `v3` via the general
    last-element conflict. -/
theorem ex_suffixof_elem_mismatch (v3 : List Int) :
    ¬ suffixOf ([-1, -1] : List Int) (v3 ++ [1]) :=
  fun h => suffix_append_last_conflict [-1, -1] v3 [1] (-1) 1 h
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## `seq.extract` slice model + out-of-bounds lemma, and `seq.replace`
    empty-needle.

The SMT `seq.extract s i n` returns the length-≤`n` slice starting at offset `i`,
with the standard convention that an out-of-range offset yields the empty
sequence. `seq.replace s needle t` with an EMPTY needle prepends `t` (the empty
needle matches at position 0). These are the kernel-verified building blocks
prepped in `scratchpad/leanseq/Extract.lean` (kept verbatim: `seqExtract`,
`seqExtract_oob`, `seqReplaceEmpty`, `seqReplaceEmpty_head`).

`seqExtract_oob_replace_head_conflict` is the emitter-facing corollary for the
`seqextract_oob` shape: an OOB extract gives `[]`, replacing with an empty needle
prepends `t`, so the head is pinned by `t`'s head; asserting the whole equals a
sequence whose head is `b` forces `head t = b`, a contradiction when `t`'s head is
a different `a`. -/

/-- `seq.extract s i n` = the length-≤n slice from offset i (SMT semantics:
    out-of-range offset yields empty). -/
def seqExtract {α : Type} (s : Seq α) (i n : Nat) : Seq α := (s.drop i).take n

/-- **Extract OOB → empty.** offset ≥ length ⇒ extract is empty. -/
theorem seqExtract_oob {α : Type} (s : Seq α) (i n : Nat) (h : s.length ≤ i) :
    seqExtract s i n = [] := by
  unfold seqExtract
  rw [List.drop_eq_nil_of_le h]; simp

/-- `seq.replace s needle t` with an EMPTY needle prepends t (SMT: empty needle
    matches at position 0). -/
def seqReplaceEmpty {α : Type} (s t : Seq α) : Seq α := t ++ s

/-- **Replace-empty head.** `(seqReplaceEmpty s t)` has head = t's head when t
    non-empty — so its first element is pinned by t, not s. -/
theorem seqReplaceEmpty_head {α : Type} (s t : Seq α) (a : α) (ht : t.head? = some a) :
    (seqReplaceEmpty s t).head? = some a := by
  unfold seqReplaceEmpty
  cases t with
  | nil => simp at ht
  | cons b t' => simp_all

/-! ### `seq.extract` OOB + `seq.replace` empty-needle conflict corollary. -/

/-- **Extract-OOB replace-empty head conflict** (emitter-facing). An OOB extract
    (`s.length ≤ i`) makes the replaced sequence empty, and replacing with an
    empty needle prepends `t`, so the whole `seqReplaceEmpty (seqExtract s i n) t`
    has head = `t`'s head `a`. Asserting the whole equals a sequence `whole` whose
    head is a *different* `b ≠ a` is therefore unsatisfiable: the head is pinned by
    `t`. This is exactly the `seqextract_oob` firewall shape (extract OOB → `[]`,
    replace-empty prepends `t`, whole asserted `= [0,1]` forces `head t = 0`, a
    contradiction when `t = [-2]`). The OOB offset is recorded via `_hoob` (its role
    is to guarantee the extract is empty, so the head is `t`'s alone). -/
theorem seqExtract_oob_replace_head_conflict {α : Type} (s t whole : Seq α)
    (i n : Nat) (a b : α) (_hoob : s.length ≤ i)
    (ht : t.head? = some a) (hb : whole.head? = some b) (hab : a ≠ b) :
    ¬ (seqReplaceEmpty (seqExtract s i n) t = whole) := by
  intro h
  have hhead := seqReplaceEmpty_head (seqExtract s i n) t a ht
  rw [h, hb] at hhead
  exact hab (Option.some.inj hhead).symm

/-! ### Concrete, kernel-checked `seq.extract`-OOB / `seq.replace`-empty witness. -/

/-- The one-element sequence `seq.unit 2 = [2]` over `Int`, for the `seqextract_oob`
    regression: extracting at offset `1` (OOB, since `len [2] = 1 ≤ 1`) yields `[]`. -/
def sExtractOob : Seq Int := [2]

/-- Concrete OOB extract: `seq.extract [2] 1 5 = []` — offset `1 ≥ len [2]`.
    Kernel-checked by `decide`, and also via the general `seqExtract_oob`. -/
theorem ex_seqExtract_oob_empty : seqExtract sExtractOob 1 5 = ([] : Seq Int) := by decide

/-- The same OOB-empty fact via the general principle. -/
theorem ex_seqExtract_oob_via_principle : seqExtract sExtractOob 1 5 = ([] : Seq Int) :=
  seqExtract_oob sExtractOob 1 5 (by decide)

/-- **`seqextract_oob` conflict.** With the extract OOB (`[]`), replacing with the
    empty needle prepends `t = [-2]`, so the whole is `[-2]`; asserting it equals
    `[0, 1]` is unsatisfiable (head `-2 ≠ 0`). Kernel-checked by `decide`. -/
theorem ex_seqExtract_oob_replace_conflict :
    ¬ (seqReplaceEmpty (seqExtract sExtractOob 1 5) ([-2] : Seq Int) = [0, 1]) := by
  decide

/-- The same conflict via the general principle: the whole's head is pinned by
    `t = [-2]` (`head = -2`), which clashes with `[0,1]`'s head `0`. -/
theorem ex_seqExtract_oob_replace_via_principle :
    ¬ (seqReplaceEmpty (seqExtract sExtractOob 1 5) ([-2] : Seq Int) = [0, 1]) :=
  seqExtract_oob_replace_head_conflict sExtractOob [-2] [0, 1] 1 5 (-2) 0
    (by decide) (by decide) (by decide) (by decide)

end AySoundness.SeqThy