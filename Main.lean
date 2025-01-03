import Src.Day1

def main : IO Unit :=
  let x := Day1.min_total_pairing_distance [5, 3, 2] [6, 7, 8]
  IO.println x
