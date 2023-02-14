import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Log
import Runtime.MergeSort.LogLemmas

section timedSort

variable {α : Type uu} (r : α → α → Prop) [DecidableRel r]
local infixl:50 " ≼ " => r

@[simp] def split : List α → (List α × List α × ℕ)
  | []       => ([], [], 0)
  | (h :: t) => let (l₁, l₂, n) := split t
                (h :: l₂, l₁, n + 1)

theorem split_equivalence : ∀ (l : List α) ,
  (split l).fst = (List.split l).fst ∧ (split l).snd.fst = (List.split l).snd
  | [] => by simp [List.split, split, and_self]
  | (h :: t) => by
    simp [List.split, split]
    have ⟨ih_fst, ih_snd⟩ := split_equivalence t
    exact And.intro ih_snd ih_fst

theorem split_complexity : ∀ (l : List α) , (split l).snd.snd = l.length
| [] => by simp [List.length, split]
| (h :: t) => by
  simp [List.length, split]
  exact split_complexity t

theorem length_split_lt {a b: α} {l l₁ l₂ : List α} {n : ℕ}
  (h : split (a::b::l) = (l₁, l₂, n)):
    List.length l₁ < List.length (a::b::l) ∧
    List.length l₂ < List.length (a::b::l) := by
  have split_eq_full : l₁ = (a::b::l).split.fst ∧ l₂ = (a::b::l).split.snd := by
    have l₂_n_id : (l₂, n) = (split (a :: b :: l)).snd :=
      (congrArg Prod.snd h).congr_right.mpr rfl
    have l₂_id : l₂ = (split (a :: b :: l)).snd.fst :=
      (congrArg Prod.fst l₂_n_id).congr_right.mp rfl
    have l₁_id : l₁ = (split (a :: b :: l)).fst :=
      (congrArg Prod.fst h).congr_right.mpr rfl
    have split_eq := split_equivalence (a :: b :: l)
    /- apply And.intro -/
    /- { exact l₁_id } -/
    /- rw [split_eq_left] at l₁_id -/
    admit
    /- rw [split_eq_right] at l₂_id -/
    /- exact ⟨ l₁_id , l₂_id ⟩ -/
  admit
  /- cases split_eq_full, -/
  /- have reconstruct : (a::b::l).split = (l₁, l₂) := by -/
  /-   rw [split_eq_full_left] -/
  /-   rw [split_eq_full_right] -/
  /-   exact prod.ext rfl rfl -/
  /- exact List.length_split_lt reconstruct -/

end timedSort
