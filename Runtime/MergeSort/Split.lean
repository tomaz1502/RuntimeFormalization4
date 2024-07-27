import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Log
import Runtime.MergeSort.LogLemmas

section timedSort

universe u

variable {α : Type u}

theorem split_halves_length' : ∀ {l l₁ l₂ : List α},
  List.split l = (l₁, l₂) →
    2 * List.length l₁ ≤ List.length l + 1 ∧ 2 * List.length l₂ ≤ List.length l
  | []       => by
    intros h
    unfold List.split at h
    simp at h
    have ⟨h₁, h₂⟩ := h
    rw [← h₁, ← h₂]
    simp
  | (a :: t) => by
    intros h'
    cases e: List.split t with
    | mk t₁ t₂ =>
      have split_id : List.split (a :: t) = (a :: t₂, t₁) := by
        unfold List.split
        rw [e]
      rw [split_id] at h'
      injection h' with h₁ h₂
      have ⟨ih₁, ih₂⟩ := split_halves_length' e
      apply And.intro
      { rw [← h₁]
        simp
        exact @Nat.add_le_add (2 * List.length t₂) (List.length t) 2 2 ih₂ le_rfl
      }
      { rw [← h₂]
        simp [ih₁]
      }

theorem split_halves_length : ∀ {l l₁ l₂ : List α},
  List.split l = (l₁, l₂) →
    List.length l₁ ≤ (List.length l + 1) / 2 ∧
    List.length l₂ ≤ (List.length l) / 2 := by
  intros l l₁ l₂ h
  have ⟨pf₁, pf₂⟩ := split_halves_length' h
  exact ⟨div_two (l.length + 1) l₁.length pf₁, div_two l.length l₂.length pf₂⟩

/- theorem split_lengths : ∀ (l l₁ l₂ : List α) {n : Nat}, -/
/-   split l = (l₁, l₂, n) → l₁.length + l₂.length = l.length -/
/- | []  => by -/
/-   intros l₁ l₂ n -/
/-   simp -/ 
/-   intros h₁ h₂ _ -/
/-   rw [← h₁, ← h₂] -/
/-   simp -/
/- | [a] => by -/
/-   intros l₁ l₂ n -/
/-   simp -/
/-   intros h₁ h₂ _ -/
/-   rw [← h₁, ← h₂] -/
/-   simp -/
/- | (a :: b :: t) => by -/
/-   intros l₁ l₂ n h -/
/-   cases e : split t with -/
/-   | mk l₁' l₂'m => -/
/-     have ⟨l₂', m⟩ := l₂'m -/
/-     simp at h -/
/-     rw [e] at h -/
/-     unfold split at h -/
/-     have ih := split_lengths t l₁' l₂' e -/
/-     have ⟨h₁, ⟨h₂, _⟩⟩ := h -/
/-     rw [← h₁, ← h₂] -/
/-     simp -/
/-     show List.length l₁' + 1 + List.length l₂' + 1 = List.length t + 2 -/
/-     rw [add_comm, add_comm (List.length l₁'), add_assoc, ih] -/
/-     ring_nf -/

end timedSort
