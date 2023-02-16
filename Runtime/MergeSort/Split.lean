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
  | [] => by simp
  | (h :: t) => by
    simp
    have ⟨ih_fst, ih_snd⟩ := split_equivalence t
    exact And.intro ih_snd ih_fst

theorem split_complexity : ∀ (l : List α) , (split l).snd.snd = l.length
| [] => by simp
| (h :: t) => by
  simp
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
    have ⟨l₁_id', l₂_id'⟩ := split_equivalence (a :: b :: l)
    apply And.intro
    { rw [l₁_id'] at l₁_id; exact l₁_id }
    rw [l₂_id'] at l₂_id
    exact l₂_id
  have ⟨l₁_id, l₂_id⟩ := split_eq_full
  have reconstruct : List.split (a :: b :: l) = (l₁, l₂) := by
    rw [l₁_id, l₂_id]
  exact List.length_split_lt reconstruct

theorem split_halves_length : ∀ {l l₁ l₂ : List α} {n : ℕ},
  split l = (l₁, l₂, n) → 
    2 * List.length l₁ ≤ List.length l + 1 ∧ 2 * List.length l₂ ≤ List.length l
| []       => by
  intros h
  unfold split at h
  simp at h
  have ⟨h₁, ⟨h₂, _⟩⟩ := h
  rw [← h₁, ← h₂]
  simp
| (a :: t) => by
  intros h'
  cases e: split t with
  | mk t₁ t₂m =>
    have ⟨t₂, m⟩ := t₂m
    have split_id : split (a :: t) = (a :: t₂, t₁, m + 1) := by
      unfold split
      rw [e]
    rw [split_id] at h'
    injection h' with h₁' h''
    injection h'' with h₂' h₃'
    have ⟨ih₁, ih₂⟩ := split_halves_length e
    apply And.intro
    { rw [← h₁']
      simp
      exact @Nat.add_le_add (2 * List.length t₂) (List.length t) 2 2 ih₂ le_rfl
    }
    { rw [← h₂']
      simp
      exact ih₁
    }

theorem split_lengths : ∀ (l l₁ l₂ : List α) {n : ℕ},
  split l = (l₁, l₂, n) → l₁.length + l₂.length = l.length
| []  => by
  intros l₁ l₂ n
  simp 
  intros h₁ h₂ _
  rw [← h₁, ← h₂]
  simp
| [a] => by
  intros l₁ l₂ n
  simp
  intros h₁ h₂ _
  rw [← h₁, ← h₂]
  simp
| (a :: b :: t) => by
  intros l₁ l₂ n h
  cases e : split t with
  | mk l₁' l₂'m =>
    have ⟨l₂', m⟩ := l₂'m
    simp at h
    rw [e] at h
    unfold split at h
    have ih := split_lengths t l₁' l₂' e
    have ⟨h₁, ⟨h₂, _⟩⟩ := h
    rw [← h₁, ← h₂]
    simp
    show List.length l₁' + 1 + List.length l₂' + 1 = List.length t + 2
    rw [add_comm, add_comm (List.length l₁'), add_assoc, ih]
    ring_nf

end timedSort
