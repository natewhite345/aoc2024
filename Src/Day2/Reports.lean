import Src.Day2.Levels
open Levels

structure Report where
  levels : List Level
  safety : SafetyStatus levels := by constructor; simp

def list_to_report : List Nat → List Level
  | l => l.map (fun x => ⟨Int.ofNat x ⟩)

instance: Coe (List Nat) (List Level ) := ⟨list_to_report ⟩

namespace report_examples
def report_no_levels : Report := {levels:=[]}
def report_safe_levels: Report := {levels:= [5,4,3,2]}
def x :List Level:= [⟨5⟩,⟨3⟩,⟨1⟩]
#eval Level.value 5 - Level.value 3 < 3
def report_unsafe_levels : Report := {levels:=([5,3,2]:List Level), safety:= (by
constructor;simp;
repeat rw [Level.value]
have : ∀x y , ∀  n : OfNat x y, Level.value y = y := by simp

rw [this Level, this 3]

)
}
def list_to_report : List Nat → List Level
  | l => l.map (fun x => ⟨Int.ofNat x ⟩)

end report_examples

def List.countWithPred{α : Type}(l: List α)(p: α → Bool): Nat := (l.filter p).length

def safe_safety_status {x: List Level}: SafetyStatus x →  Bool
  | SafetyStatus.Safe _ => true
  | SafetyStatus.Unsafe _ => false

structure ReportCollection where
  reports: List Report
  length: Nat
  len_eq : reports.all (fun r => r.levels.length = length) := by rfl
  safe_count : Nat
  safe_count_proof : safe_count = reports.countWithPred (fun r => safe_safety_status r.safety )

def create_report
