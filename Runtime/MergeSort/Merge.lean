import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith

section timedSort

universe u

variable {α : Type u} (r : α → α → Prop) [DecidableRel r]
local infixl:50 " ≼ " => r

@[simp] def merge : List α → List α → (List α × Nat)
  | [], l₂ => (l₂, 0)
  | l₁, [] => (l₁, 0)
  | (h₁ :: t₁), (h₂ :: t₂) =>
    if h₁ ≼ h₂
    then let (l₃, n) := merge t₁ (h₂ :: t₂)
         (h₁ :: l₃, n + 1)
    else let (l₃, n) := merge (h₁ :: t₁) t₂
         (h₂ :: l₃, n + 1)
termination_by merge l₁ l₂ => List.length l₁ + List.length l₂

theorem merge_complexity : ∀ l₁ l₂ : List α,
  (merge r l₁ l₂).snd ≤ l₁.length + l₂.length
  | [], l₂ => by simp
  | (h₁ :: t₁), [] => by simp
  | (h₁ :: t₁), (h₂ :: t₂) => by
    unfold merge
    split_ifs with if_hyp
    { have ih := merge_complexity t₁ (h₂ :: t₂)
      cases e: merge r t₁ (h₂ :: t₂) with
      | mk l₁ l₂ =>
        rw [e] at ih
        simp at ih
        show l₂ + 1 ≤ t₁.length + 1 + t₂.length + 1
        simp
        have ih' : l₂ ≤ t₁.length + t₂.length + 1 := ih
        rw [Nat.add_assoc, add_comm t₂.length 1, ← Nat.add_assoc] at ih'
        exact ih'
    }
    { have ih := merge_complexity (h₁ :: t₁) t₂
      cases e: merge r (h₁ :: t₁) t₂ with
      | mk l₁ l₂ =>
        rw [e] at ih
        simp at ih
        show l₂ + 1 ≤ t₁.length + 1 + t₂.length + 1
        simp
        exact ih
    }
termination_by merge_complexity l₁ l₂ => List.length l₁ + List.length l₂

theorem merge_equivalence : ∀ l₁ l₂ : List α,
  (merge r l₁ l₂).fst = List.merge r l₁ l₂
| [],       []           => by simp; rw [List.merge]
| [],       (h₂ :: t₂)   => by simp; rw [List.merge]
| (h₁ :: t₁), []         => by simp; rw [List.merge]; simp
| (h₁ :: t₁), (h₂ :: t₂) => by
  unfold merge
  split_ifs with if_hyp
  { have ih := merge_equivalence t₁ (h₂ :: t₂)
    cases e : merge r t₁ (h₂ :: t₂) with
    | mk l₁ l₂ =>
      unfold List.merge
      rw [e] at ih
      simp at ih
      split_ifs
      simp
      exact ih
  }
  { have ih := merge_equivalence (h₁ :: t₁) t₂
    cases e : merge r (h₁ :: t₁) t₂ with
    | mk l₁ l₂ =>
      unfold List.merge
      rw [e] at ih
      split_ifs
      simp
      exact ih
  }
termination_by merge_equivalence l₁ l₂ => List.length l₁ + List.length l₂

end timedSort
