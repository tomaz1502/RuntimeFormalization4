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
