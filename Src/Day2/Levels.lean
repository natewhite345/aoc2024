namespace Levels
/-- A single data point in a `Report`. -/
structure Level where
  value : Int
  deriving DecidableEq, Repr
instance: OfNat Level n := ⟨{value:= Int.ofNat n}⟩
instance: Neg Level := ⟨ (fun l => ⟨Int.neg l.value⟩ )⟩
@[simp]
instance: LT Level := ⟨(fun a b  => a.value < b.value )⟩
instance : DecidableRel (· < · : Level → Level → Prop) :=
  fun a b => inferInstanceAs (Decidable (a.value < b.value))
instance: LE Level := ⟨(fun a b  => a.value ≤ b.value )⟩
instance : DecidableRel (· ≤ · : Level → Level → Prop) :=
  fun a b => inferInstanceAs (Decidable (a.value ≤ b.value))
-- instance: Coe Level Int := ⟨ fun l => l.value ⟩
-- instance: Coe Int Level:= ⟨ fun l => Level.mk l ⟩
-- instance: Coe Nat Level:= ⟨ fun l => Level.mk (Int.ofNat l) ⟩
-- instance: Coe (List Nat) (List Level) := ⟨ fun l => l.map (fun i => Level.mk (Int.ofNat i))⟩

namespace level_examples
  def level_50 : Level := 50 -- demo of type coercion
  def level_0 : Level := 0 -- ""
  def level_neg_20 : Level := -20 -- ""
  def level_neg_12 : Level := {value := -12 }
  #guard level_0 < level_50
  #guard level_neg_20 < level_0
  #guard level_50 > level_0
  #guard ¬ (level_0 > level_0)
  #guard level_0 ≤ level_0
  #guard ¬ (level_0 ≤ level_neg_20)

end level_examples

@[simp]
def List.AdjacentProperty {α : Type} (r : α → α → Prop): List α → Prop
  | [] => True
  | [_] => True
  | hd :: sec :: tl => r hd sec ∧ List.AdjacentProperty r (sec :: tl)
@[simp]
def gradual_change(a b : Level): Prop :=
  let diff := (a.value-b.value).natAbs
  diff ≤ 3 ∧ diff ≥ 1
@[simp]
def gradually_changing := List.AdjacentProperty gradual_change
@[simp]
def strictly_increasing : List Level → Prop := List.AdjacentProperty ( . < . )
@[simp]
def strictly_decreasing : List Level → Prop := List.AdjacentProperty ( . > . )
@[simp]
def safe_levels(levels: List Level) := gradually_changing levels ∧ (strictly_increasing levels ∨ strictly_decreasing levels)

inductive SafetyStatus(levels: List Level)
  | Safe : safe_levels levels →  SafetyStatus levels
  | Unsafe : ¬ safe_levels levels → SafetyStatus levels

end Levels
