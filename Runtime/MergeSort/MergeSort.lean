import Runtime.MergeSort.LogLemmas
import Runtime.MergeSort.Merge
import Runtime.MergeSort.Split

universe u

variable {α : Type} (r : α → α → Prop) [DecidableRel r]
local infixl:50 " ≼ " => r

@[simp] def mergeSort : List α → (List α × Nat)
  | [] => ([], 0)
  | [a] => ([a], 0)
  | a :: b :: l => by
    cases r₁: List.split (a :: b :: l) with
    | mk l₁ l₂ =>
      have h := @List.length_split_lt α a b l l₁ l₂ r₁
      have := h.1
      have := h.2
      let ⟨sorted_ls₁, m₁⟩ := mergeSort l₁
      let ⟨sorted_ls₂, m₂⟩ := mergeSort l₂
      let ⟨ls', m⟩ := merge (r · ·) sorted_ls₁ sorted_ls₂
      exact ⟨ls', m₁ + m₂ + m⟩
  termination_by l => List.length l

theorem mergeSort_cons_cons {a b} {l l₁ l₂ : List α}
      (h : List.split (a :: b :: l) = (l₁, l₂)) :
      (mergeSort r (a :: b :: l)).1 = (merge (r · ·) (mergeSort r l₁).1 (mergeSort r l₂).1).1 :=
    by simp [mergeSort]
       simp at h
       have ⟨h₁, h₂⟩ := h
       rw [← h₁, ← h₂]

theorem mergeSort_equivalence : ∀ (l : List α), (mergeSort r l).fst = List.mergeSort r l
  | []          => by simp [mergeSort]
  | [a]         => by simp [mergeSort]
  | a :: b :: l => by
      have : (l.split.1).length < l.length + 1 := Nat.lt_add_one_of_le (List.length_split_fst_le l)
      have : (l.split.2).length < l.length + 1 := Nat.lt_add_one_of_le (List.length_split_snd_le l)
      rw [List.mergeSort_cons_cons r (Prod.ext rfl rfl)]
      rw [mergeSort_cons_cons r (Prod.ext rfl rfl)]
      rw [merge_equivalence]
      rw [mergeSort_equivalence (a :: l.split.1)]
      rw [mergeSort_equivalence (b :: l.split.2)]
    termination_by l => List.length l

theorem mergeSort_cons_cons_snd {a b} {l l₁ l₂ : List α}
  (hs : List.split (a :: b :: l) = (l₁, l₂)) :
    (mergeSort r (a :: b :: l)).snd =
    (mergeSort r l₁).snd + (mergeSort r l₂).snd +
    (merge (r · ·) (mergeSort r l₁).fst (mergeSort r l₂).fst).snd := by
  simp at hs
  simp [mergeSort, hs]

theorem mergeSort_complexity : ∀ l : List α,
    (mergeSort r l).snd ≤ 8 * l.length * Nat.log 2 l.length
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by
    cases e : List.split (a :: b :: l) with
    | mk l₁ l₂ =>
      rw [mergeSort_cons_cons_snd r e]
      cases e1 : mergeSort r l₁ with
      | mk ms1 n1 =>
        cases e2 : mergeSort r l₂ with
        | mk ms2 n2 =>
          simp
          have split_lt := @List.length_split_lt α a b l l₁ l₂ e
          have := split_lt.1
          have := split_lt.2

          have ih1 := mergeSort_complexity l₁
          have ih2 := mergeSort_complexity l₂
          rw [e1] at ih1
          simp at ih1
          rw [e2] at ih2
          simp at ih2

          have :
            n1 + n2 + (merge.loop (r · ·) ms1 ms2 []).2 ≤
            (8 * l₁.length * Nat.log 2 l₁.length) + n2 + (merge.loop (r · ·) ms1 ms2 []).2 :=
              by linarith

          apply le_trans this
          have :
            (8 * l₁.length * Nat.log 2 l₁.length) +
            n2 +
            (merge.loop (r · ·) ms1 ms2 []).2
            ≤
            (8 * l₁.length * Nat.log 2 l₁.length) +
            (8 * l₂.length * Nat.log 2 l₂.length) +
            (merge.loop (r · ·) ms1 ms2 []).2 := by linarith
          apply le_trans this
          have ⟨l₁_small, l₂_small⟩ := split_halves_length e

          admit

    termination_by l => List.length l

