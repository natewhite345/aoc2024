import Lean.Parser





--

instance: Coe (List Level) (List Int) := ⟨ fun l => l.map (fun ll => ll.value)⟩
instance: Coe (List Int) (List Level) := ⟨ fun l => l.map (fun ll => ⟨ll⟩ )⟩
instance: Coe (List Nat) Report := ⟨ fun l => ⟨l.map (fun ll => ⟨ Int.ofNat ll⟩)⟩⟩

namespace _examples
def r : Report := [5,4,3]
end _examples








/-- Creates reports -/
def parse_reports( s: String): Option (List Report) :=
  let lines := s.splitOn "\n"
  if lines.length = 0 then Option.none else
  let lines := lines.map (fun line => line.splitOn " ")
  let lines : List (List (Option Level)):= lines.map (fun line => line.map String.toNat?)
  for line in lines
  if lines.all (fun line => line.all Option.isSome) then Option.some (lines.map (fun line => line.map Option.get_some)) else Option.none

#guard parse_reports """7 6 4 2 1
1 2 7 8 9
9 7 6 2 1
1 3 2 4 5
8 6 4 4 1
1 3 6 7 9""" = Option.some [
  [7, 6, 4, 2, 1],
  [1, 2, 7, 8, 9],
  [9, 7, 6, 2, 1],
  [1, 3, 2, 4, 5],
  [8, 6, 4, 4, 1],
  [1, 3, 6, 7, 9]
]

#guard parse_reports """5
4 3""" = Option.none

#guard parse_reports """
5    4 2

3 5     7

""" = Option.some [[5,4,2],[3,5,7]]
