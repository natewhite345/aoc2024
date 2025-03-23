namespace Day1

@[simp]
private def pair_distance: Nat → Nat →  Nat
  | a, b => if a < b then b - a else a - b

private abbrev pd := pair_distance
#guard pd 5 8 = 3
#guard pd 0 5 = 5
#guard pd 2 1 = 1
#guard pd 3 1 = 2

#check True

private theorem pair_distance_comm : ∀ a b : Nat, pair_distance a b = pair_distance b a := by
  intro a b
  rw [pair_distance, pair_distance]
  split
  . split <;> {
      rename_i h1 h2
      have ct := Nat.lt_asymm h1
      trivial
    }
  . split
    . rfl
    . rename_i h1 h2
      have eq := Nat.eq_iff_le_and_ge.mpr ⟨(Nat.not_lt.mp h1), (Nat.not_lt.mp h2)⟩
      rw [eq]

private theorem pair_distance_zip_comm (l1 l2 : List Nat): List.zipWith pair_distance l1 l2 = List.zipWith pair_distance l2 l1 := by
    cases l1 with
      | nil => simp
      | cons hd tl =>
        cases l2 with
          | nil => simp
          | cons sec tl2 =>
            rw [List.zipWith, List.zipWith]
            rw [pair_distance_comm]
            rw [pair_distance_zip_comm]

private theorem pair_distance_zero_if_eq : ∀ p: Nat, pair_distance p p = 0 := by simp

/--
Pairs items of the list such that the smallest item of the first is with the smallest item of the second, the second smallest items are paired, etc; and then returns the sum of the differences of the pairs.
-/
@[reducible, simp]
def min_total_pairing_distance(a b : List Nat)(_ : a.length = b.length := by rfl): Nat :=
  List.sum (List.zipWith pair_distance (List.mergeSort a (. ≤ .)) (List.mergeSort b (. ≤ .)))

private abbrev mtpd := @min_total_pairing_distance
#guard mtpd [] [] = 0
#guard mtpd [5,4] [7,9] = 7
#guard mtpd [1,2,3] [4,5,6] = 9
#guard mtpd [0, 0, 0] [5, 9, 2] = 16
#guard mtpd [0, 20] [0, 20] = 0

/-- min_total_pairing_distance is commutative -/
theorem comm : ∀ l1 l2 : List Nat, ∀ len_eq : l1.length = l2.length, min_total_pairing_distance l1 l2 len_eq = min_total_pairing_distance l2 l1 len_eq.symm := by
  intro l1 l2 len_eq
  have zip_comm := pair_distance_zip_comm (l1.mergeSort (. ≤ .)) (l2.mergeSort (. ≤ .))
  rw [min_total_pairing_distance, zip_comm]

theorem same_list_is_zero : ∀ l : List Nat, min_total_pairing_distance l l = 0 := by
  intro l
  rw [min_total_pairing_distance]
  let l := l.mergeSort (. ≤ . )
  show List.sum (List.zipWith pair_distance l l) = 0
  induction l with
    | nil => simp
    | cons hd tl ih =>
      rw [List.zipWith, pair_distance_zero_if_eq, List.sum_cons, ih]

/-- Converting from Nat.le_trans to accomodate the form for List.sorted_mergeSort -/
private theorem le_trans : ∀ (a b c : Nat), decide (a ≤ b) = true → decide (b ≤ c) = true → decide (a ≤ c) = true := by
        intro a b c h1 h2
        rw [eq_comm, true_eq_decide_iff] at h1
        rw [eq_comm, true_eq_decide_iff] at h2
        rw [eq_comm, true_eq_decide_iff]
        exact Nat.le_trans h1 h2

/-- Converting from Nat.le_trans to accomodate the form for List.sorted_mergeSort -/
private theorem le_total : ∀ (a b : Nat), a ≤ b || b ≤ a := by
        intro a b
        have := Nat.le_or_le a b
        cases this <;> simp_all

/-- Sorting two lists that are permutations will result in the same list -/
private theorem perm_unique_sort(l1 l2 : List Nat)(p: l1.Perm l2): l1.mergeSort = l2.mergeSort := by
  let l1' := l1.mergeSort
  let l2' := l2.mergeSort
  show l1' = l2'
  have c1 : ∀ a b, a ∈ l1' → b ∈ l2' → a ≤ b → b ≤ a → a = b := by
    intro a b inl inl' h1 h2
    exact Nat.eq_iff_le_and_ge.mpr ⟨h1, h2⟩
  have c2 : l1'.Pairwise (. ≤ .) := by
    have := List.sorted_mergeSort le_trans le_total l1
    simp_all
  have c3 : l2'.Pairwise (. ≤ .) := by
    have := List.sorted_mergeSort le_trans le_total l2
    simp_all
  have c4 : l1'.Perm l2' := by
    have l1p: l1'.Perm l1 := List.mergeSort_perm l1 (. ≤ .)
    have l2p: l2'.Perm l2 := List.mergeSort_perm l2 (. ≤ .)
    have l1'pl2 := List.Perm.trans l1p p
    exact List.Perm.trans l1'pl2 l2p.symm
  rw [List.Perm.eq_of_sorted c1 c2 c3 c4]

/-- The first list of min_total_pairing_distance ignores the ordering of its elements -/
theorem order_agnostic_arg_1 : ∀ l1 l1' l2 : List Nat, ∀ len_eq : l1.length = l2.length , List.Perm l1 l1' → ∃x, min_total_pairing_distance l1 l2 len_eq = min_total_pairing_distance l1' l2 x := by
  intro l1 l1' l2 len_eq p
  have len_eq2 := List.Perm.length_eq p
  rw [len_eq] at len_eq2
  exists len_eq2.symm
  simp
  have := perm_unique_sort l1 l1' p
  rw [this]

/-- The second list of min_total_pairing_distance ignores the ordering of its elements -/
theorem order_agnostic_arg_2 : ∀ l1 l2 l2': List Nat, ∀ len_eq : l1.length = l2.length , List.Perm l2 l2' → ∃x, min_total_pairing_distance l1 l2 len_eq = min_total_pairing_distance l1 l2' x := by
  intro l1 l2 l2' len_eq p
  obtain ⟨ x, h ⟩ := order_agnostic_arg_1 l2 l2' l1 len_eq.symm p
  rw [comm,comm l2' l1] at h
  exists x.symm

end Day1
