/-!
Structural equality relations used when a source normalizer distributes an
 equality across an ITE. These lemmas give no signed-operation or query authority.
-/
namespace AySoundness.ConditionalEquality

theorem factor_left {α : Type} (condition : Bool) (anchor yes no : α) :
    (if condition then anchor = yes else anchor = no) ↔
      anchor = (if condition then yes else no) := by
  cases condition <;> rfl

theorem factor_right {α : Type} (condition : Bool) (anchor yes no : α) :
    (if condition then yes = anchor else no = anchor) ↔
      (if condition then yes else no) = anchor := by
  cases condition <;> rfl

theorem named_value {α : Type} (anchor value other : α) (h : anchor = value) :
    (anchor = other) ↔ (value = other) := by
  cases h
  rfl

end AySoundness.ConditionalEquality
