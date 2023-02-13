import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith

section timedSort

variable {α : Type uu} (r : α → α → Prop) [DecidableRel r]

local infixl:50 " ≼ " => r

@[simp] def orderedInsert (a : α) : List α → (List α × Nat)
  | []      => ([a], 0)
  | b :: l => if a ≼ b then (a :: b :: l, 1)
              else let (l', n) := orderedInsert a l
                   (b :: l', n + 1)

#eval orderedInsert (· ≤ ·) 2 [5, 3, 1, 4]
-- ([2, 5, 3, 1, 4], 1)

#eval orderedInsert (· ≤ ·) 9 [1, 0, 8]
-- ([1, 0, 8, 9], 3)

@[simp] def insertionSort : List α → (List α × Nat)
  | [] => ([], 0)
  | (h :: t) => let (l', n)  := insertionSort t
                let (l'', m) := orderedInsert r h l'
                (l'', n + m)

#eval insertionSort (· ≤ ·) [1, 2, 3, 4, 5]
-- ([1, 2, 3, 4, 5], 4)

#eval insertionSort (· ≤ ·) [5, 4, 3, 2, 1]
-- ([1, 2, 3, 4, 5], 10)

theorem orderedInsert_complexity (a : α) :
  ∀ l : List α, (orderedInsert r a l).snd ≤ l.length := fun l =>
  match l with
  | []     => by simp
  | b :: l' => by
    simp
    split_ifs with h
    { simp; apply Nat.succ_le_succ; exact Nat.zero_le (List.length l') }
    simp
    have ih := orderedInsert_complexity a l'
    exact Nat.add_le_add ih le_rfl

theorem orderedInsert_equivalence (a : α) : ∀ l : List α,
  (orderedInsert r a l).fst = List.orderedInsert r a l := fun l =>
  match l with
  | [] => by simp
  | b :: l' => by
    simp
    split_ifs with h
    { rfl }
    simp
    exact orderedInsert_equivalence a l'

theorem orderedInsert_increases_length (a : α) : ∀ l : List α,
  (orderedInsert r a l).fst.length = l.length + 1 := fun l =>
  match l with
  | [] => by simp
  | b :: l' => by
    simp
    split_ifs with h
    { rfl }
    simp
    exact orderedInsert_increases_length a l'

theorem insertionSort_preserves_length : ∀ l : List α,
  (insertionSort r l).fst.length = l.length := fun l =>
  match l with
  | [] => by simp
  | a :: l' => by
    simp
    rw [orderedInsert_increases_length r a (insertionSort r l').fst]
    simp
    exact insertionSort_preserves_length l'

#check add_le_add

theorem insertionSort_complexity :
  ∀ l : List α, (insertionSort r l).snd ≤ l.length * l.length := fun l =>
  match l with
  | [] => by simp
  | a :: l' => by
    simp
    have same_lengths := insertionSort_preserves_length r l'
    have mid :
      (insertionSort r l').snd + (orderedInsert r a (insertionSort r l').fst).snd ≤
      l'.length * l'.length + (orderedInsert r a (insertionSort r l').fst).snd :=
        add_le_add (insertionSort_complexity l') le_rfl
    have mid₂ :
      l'.length * l'.length + (orderedInsert r a (insertionSort r l').fst).snd ≤
      l'.length * l'.length + l'.length := by
        apply add_le_add le_rfl
        have orderedInsert_compl :=
          orderedInsert_complexity r a (insertionSort r l').fst
        rw [same_lengths] at orderedInsert_compl
        exact orderedInsert_compl
    apply le_trans mid
    apply le_trans mid₂
    linarith

theorem insertionSort_equivalence : ∀ l : List α,
  (insertionSort r l).fst = List.insertionSort r l := fun l =>
  match l with
  | [] => by simp
  | a :: l' => by
    simp
    rw [orderedInsert_equivalence, insertionSort_equivalence l']

end timedSort

