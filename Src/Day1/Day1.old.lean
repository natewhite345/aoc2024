-- -- namespace sort
-- -- def sort : List Nat → List Nat
-- --   | [] => []
-- --   | (a :: []) => a :: []
-- --   | (a :: b :: c) => if b < a then (b:: sort (a :: c)) else (a :: sort ( b:: c))
-- -- namespace proofs
-- -- private def is_permutation(l1 l2 : List Nat): Prop :=
-- --   (∀ x, x ∈ l1 → x ∈ l2) ∧ (∀x, x ∈ l2 → x∈ l1)
-- -- def sorted_is_permutation : ∀ l1 : List Nat, is_permutation l1 (sort.sort l1) := sorry
-- -- end proofs
-- -- end sort

-- def sort.sort := 5
namespace Day1

@[simp]
def pair_distance: (Nat × Nat) →  Nat
  | (a, b) => if a > b then a -b else b-a

theorem pair_distance_zero_if_eq : ∀ p: Nat × Nat, p.fst = p.snd -> pair_distance p = 0 := by simp

#eval pair_distance (5,8)

/--
Pairs items of the list such that the smallest item of the first is with the smallest item of the second, the second smallest items are paired, etc; and then returns the sum of the differences of the pairs.
-/
@[reducible, simp]
def min_total_pairing_distance(a b : List Nat)(_ : a.length = b.length := by rfl): Nat :=
  List.sum (List.map pair_distance (List.zip (List.mergeSort a (. ≤ .)) (List.mergeSort b (. ≤ .))))
namespace _tests
@[simp]
def f := @min_total_pairing_distance
#guard f [] [] = 0
#guard f [5,4] [7,9] = 7
#guard f [1,2,3] [4,5,6] = 9
#guard f [0, 0, 0] [5, 9, 2] = 16
#guard f [0, 20] [0, 20] = 0

example: ∀ l: List Nat, f l l = 0 := by intro l; induction l with
  | nil => simp
  | cons hd tl ih => induction tl with
    | nil => simp
    | cons sec tl₂ ih₂ =>
      simp
      let sorted := (hd::sec::tl₂ ).mergeSort (. ≤ .)
      show (List.map pair_distance (List.zip sorted sorted)).sum = 0
      have zipped_list_identity : ∀ l : List Nat, List.all (List.zip l l) (fun p => p.fst == p.snd) := by
        intro l
        induction l with
          | nil => simp;
          | cons hd tl ih =>
            unfold List.zip
            unfold List.zipWith
            unfold List.zip at ih
            let f := (fun (p: Nat × Nat) => p.fst == p.snd)
            let hdp := Prod.mk hd hd
            let tlp := tl.zip tl
            unfold List.all
            unfold Bool.and
            have t : (fun p => p.fst == p.snd ) (hd, hd) = true := by
              simp
            rw [t]
            simp only []
            exact ih
      have h := zipped_list_identity sorted
      have dist0 : ∀ l : List (Nat× Nat), l.all (fun p => p.fst == p.snd) = true → l.all (fun p => pair_distance p == 0)  = true := by
        intro l h
        induction l with
          | nil => simp
          | cons hd tl ih =>
            unfold List.all
            unfold List.all at h
            rw [Bool.and_eq_true ] at h
            simp only at h
            have headproof : (fun p => pair_distance p == 0) hd := by
              have g := (pair_distance_zero_if_eq hd)
              have f:= g (of_decide_eq_true h.1)
              simp only
              rw [f]
              trivial
            have tailproof := ih h.2
            rw [headproof,tailproof]
            simp
      have dist0 := dist0 (sorted.zip sorted) h
      






example: ∀ n : Nat, min_total_pairing_distance [0] [n] = n
  := by intro n; unfold min_total_pairing_distance pair_distance; simp;

example: ∀ m n : Nat, m ≤ n → min_total_pairing_distance [m] [n] = n-m
  := by intro m n h; simp; intro c; have contra := (Nat.le_lt_asymm h) c; trivial;

end _tests

example {α : Type} [DecidableEq α] (x : α) : (x == 0) = true → x = 0 := by
  intro h
  have : x = 0 := ofDecideEqTrue h
  exact this





-- def main : IO Unit

theorem map_preserves_len : ∀ l : List α, ∀ f : α → β, l.length = (l.map f).length :=  by simp

theorem permutation_same_len(l: List α)(s: List.Perm l' l): l'.length = l.length := s.length_eq

def rearrangement (l : List α) := {l' : List α // List.Perm l' l}

def rearrangement_preserves_length{a: List α}{ b: List β} (p: a.length =b.length)(a' : rearrangement a)(b' : rearrangement b) : a'.val.length = b'.val.length := by
  have h1:  a'.val.length = a.length:= permutation_same_len a a'.property
  have h2:  b'.val.length = b.length:= permutation_same_len b b'.property
  rw [h1, h2, p]

theorem sort_same_head_tail : ∀ l: List Nat, ∀ l' : rearrangement l, l.length > 0 → ∃ hd : Nat, ∃ tl: List Nat, l.mergeSort = List.cons hd tl ∧ l'.val.mergeSort = List.cons hd tl := by
  intro l l' nonempty
  let l1 := l.mergeSort ( . ≤ .)
  have l'p := l'.property
  let l2 := l'.val.mergeSort (. ≤ .)
  have l'v := l'.val
  show ∃ hd tl, l1 = hd :: tl ∧ l2 = hd :: tl
  sorry


theorem rearrangement_preserves_sort (a : List Nat) (a' : rearrangement a) :
  List.mergeSort a = List.mergeSort a'.val := by sorry
--   induction a with
--     | nil => rw [List.perm_nil.mp a'.property]
--     | cons head tail ih =>
--       cases tail with
--         | nil =>
--           simp_all
--           simp at a'

--   have f := List.mergeSort_perm a (. ≤ .)
--   cases a' with
--     | mk l' p =>
--       simp_all
--       let l1 := a.mergeSort (. ≤ .)
--       let l2 := l'.mergeSort (. ≤ .)
--       have f : l1.Perm a := f
--       have g :
--       show l1 = l2
--       sorry


      -- induction p with
      -- | nil => simp
      -- | cons a'hd a'tl_p a'h =>
      --   rename_i l1 l2
      --   simp at a'h
      --   induction l2 with
      --     | nil =>
      --       cases l1 with
      --         | nil => rw [List.mergeSort_singleton]
      --         | cons => simp at a'tl_p
      --     | cons l2hd l2tl l2h =>
      --       induction l1 with
      --         | nil => simp at a'tl_p
      --         | cons l1hd l1tl l1h =>
      --           by_cases c1: l2hd < a'hd
      --           case pos =>
      --             rw [if_pos c1, sort.sort]
      --             by_cases c2 : l1hd < a'hd
      --             case pos =>
      --               rw [if_pos c2]
      --               sorry

      --             case neg =>
      --               rw [if_neg c2, ←a'h]
      --               sorry
      --           case neg => sorry

        -- rw [sort.sort]
        -- cases l1
        -- rw [sort.sort]
        -- rename_i second third
        -- rw [sort.sort] at ih
        -- cases third
        -- rw [sort.sort] at ih
        -- trivial
        -- simp at tl
        -- rename_i hd2 tl2
        -- cases l1
        -- cases tl2
        -- rw [sort.sort, sort.sort] at ih
        -- trivial
        -- rename_i hd3 tl3
        -- simp at tl
        -- rename_i hd4 tl4
        -- have tlinv := List.perm_comm.mp tl

        -- have f := rearrangement_preserves_sort (hd4::tl4) ⟨ (hd2:: tl2), tlinv ⟩
        -- rw [sort.sort,sort.sort]
        -- simp at f
        -- by_cases c1 : hd2 < hd
        -- rw [if_pos,f]
        -- by_cases c2 : hd4 < hd
        -- rw [if_pos]
      -- | swap x y l=>
      --   simp
      --   rw [List.sort]
      --   rw [sort.sort, sort.sort]
      --   by_cases h: y<x
      --   rw [if_pos]
      --   by_cases h2 : x<y
      --   rw [if_pos]
      --   have contra := Nat.lt_asymm h h2
      --   contradiction
      --   assumption
      --   rw [if_neg]
      --   assumption
      --   assumption
      --   rw [if_neg]
      --   by_cases h2: x<y
      --   rw [if_pos]
      --   assumption
      --   rw [if_neg]
      --   have f := Nat.eq_or_lt_of_not_lt h
      --   have f := Or.resolve_right f h2
      --   rw [f]
      --   assumption
      --   assumption
      -- | trans p1 p2 ih1 ih2 =>
      --   rename_i l1 l2 l3
      --   simp
      --   simp at ih1
      --   simp at ih2
      --   have p3 : l1.Perm l3 := List.Perm.trans p1 p2
      --   cases l3
      --   simp at p3
      --   rw [p3]
      --   rename_i hd tl
      --   rw [← ih1]
      --   assumption

  -- have perm_proof : List.Perm a' a := a'.snd
  -- induction perm_proof with
  -- | refl => rfl
  -- | swap x y l =>
  --   simp [sort]
  --   split
  --   · simp [sort]
  --   · simp [sort]
  -- | trans l₁ l₂ l₃ h₁ h₂ =>
  --   exact Eq.trans (perm_proof_ih_h₁ _) (perm_proof_ih_h₂ _)
  -- induction a
  -- rfl
  -- --with
  --   | List.nil => match a'.val with
  --     | [] => rfl
  --     | (hd :: tl) => sorry
  --   -- | (hd :: tl) => match a'.val with
  --   --   | _ => sorry

  -- -- rw [←sort.sort]
  -- -- have a'v := a'.val
  -- -- have a'p := a'.property
  -- -- generalize a'p = g
  -- -- cases g





  -- sorry

  -- rw [rearrangement] at a'

  -- cases a'.val with
  --   | nil => sorry
  --   | cons head tail => sorry

  -- | cons x y l =>
  --   simp [sort]
  --   split
  --   · simp [sort]
  --   · simp [sort]
  -- | trans l₁ l₂ l₃ h₁ h₂ =>
  --   exact Eq.trans (perm_proof_ih_h₁ _) (perm_proof_ih_h₂ _)

-- swapping the order of elements of the list has no effect
def order_agnostic: ∀ a b : List Nat,  ∀ a' : rearrangement a,
forall b' : rearrangement b,  ∀ p: a.length = b.length, min_total_pairing_distance a b p = min_total_pairing_distance a'.val b'.val (rearrangement_preserves_length p a' b') := by
  intro a b a' b' p
  rw [min_total_pairing_distance, min_total_pairing_distance, rearrangement_preserves_sort a a', rearrangement_preserves_sort b b']

-- any other pairing of elements in the lists will be higher


#eval min_total_pairing_distance [6, 4] [3, 2] rfl

end Day1
