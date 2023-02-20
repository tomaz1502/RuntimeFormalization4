import Runtime.MergeSort.Split
import Runtime.MergeSort.Merge

universe u

variable {α : Type u} (r : α → α → Prop) [DecidableRel r]
local infixl:50 " ≼ " => r

def mergeSort : List α → (List α × Nat)
  | [] => ([], 0)
  | [a] => ([a], 0)
  | a :: b :: l => by
    cases r₁: split (a :: b :: l) with
    | mk ls₁ ls₂n =>
      cases r₂: ls₂n with
      | mk ls₂ n =>
        have e : split (a :: b :: l) = ⟨ls₁, ⟨ls₂, n⟩⟩ := by
          rw [r₁, r₂]
        have h := length_split_lt e
        have := h.1
        have := h.2
        let ⟨sorted_ls₁, m₁⟩ := mergeSort ls₁
        let ⟨sorted_ls₂, m₂⟩ := mergeSort ls₂
        let ⟨ls', m⟩ := merge r sorted_ls₁ sorted_ls₂
        exact ⟨ls', n + m₁ + m₂ + m⟩
  termination_by mergeSort l => List.length l

theorem mergeSort_cons_cons {a b} {l l₁ l₂ : List α} {n : Nat} (h : split (a :: b :: l) = (l₁, l₂, n)) :
    (mergeSort r (a :: b :: l)).1 = (merge r (mergeSort r l₁).1 (mergeSort r l₂).1).1 := by
    simp [mergeSort]
    simp at h
    have ⟨h₁, ⟨h₂, _⟩⟩ := h
    rw [← h₁, ← h₂]

theorem mergeSort_equivalence : ∀ (l : List α), (mergeSort r l).fst = List.mergeSort r l
| []          => by simp [mergeSort]
| [a]         => by simp [mergeSort]
| a :: b :: l => by
  have : (split (a :: b :: l)).fst.length < (a :: b :: l).length :=
    by cases e : split (a :: b :: l) with
       | mk l₁ l₂n =>
         have ⟨h₁, _⟩ := length_split_lt e
         exact h₁
  have : (split (a :: b :: l)).snd.fst.length < (a :: b :: l).length :=
    by cases e : split (a :: b :: l) with
       | mk l₁ l₂n =>
         have ⟨_, h₂⟩ := length_split_lt e
         exact h₂
  rw [List.mergeSort_cons_cons r (Prod.ext rfl rfl)]
  rw [mergeSort_cons_cons r (Prod.ext rfl (Prod.ext rfl rfl))]
  rw [merge_equivalence]
  rw [mergeSort_equivalence (split (a :: b :: l)).1]
  rw [mergeSort_equivalence (split (a :: b :: l)).2.1]
  rw [(split_equivalence (a :: b :: l)).left]
  rw [(split_equivalence (a :: b :: l)).right]
  termination_by mergeSort_equivalence l => List.length l

theorem mergeSort_cons_cons_snd {a b n} {l l₁ l₂ : List α}
  (hs : split (a :: b :: l) = (l₁, l₂, n)) :
    (mergeSort r (a :: b :: l)).snd =
    (split (a :: b :: l)).snd.snd + (mergeSort r l₁).snd + (mergeSort r l₂).snd +
    (merge r (mergeSort r l₁).fst (mergeSort r l₂).fst).snd := by
  simp at hs
  simp [mergeSort, hs]

theorem merge_sort_complexity : ∀ l : List α, (mergeSort r l).snd ≤ 8 * l.length * Nat.log 2 l.length := sorry
