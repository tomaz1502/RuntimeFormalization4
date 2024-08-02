import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem log_pred : ∀ (a : Nat) , Nat.log 2 a - 1 = Nat.log 2 (a / 2)
| 0 => by simp only [Nat.log_zero_right, Nat.zero_div]
| 1 => by norm_num
| (a + 2) => by
  rw [Nat.log]
  split_ifs with h
  { simp }
  simp at h

theorem log_2_val : Nat.log 2 2 = 1 := by rfl

theorem sum_2b (a b : Nat) : a ≤ 2 * b → a + 2 * b ≤ 4 * b := fun h =>
  calc a + 2 * b ≤ 2 * b + 2 * b := add_le_add h rfl.ge
       _         = 4 * b := by linarith

theorem log_2_times : ∀ (a : Nat), 2 * Nat.log 2 a ≤ a
| 0       => by simp
| (a + 1) => by
  have : (a + 1) / 2 < a + 1 := Nat.div_lt_self' a 0
  rw [Nat.log]
  split_ifs
  · have IH := log_2_times ((a + 1) / 2); omega
  · simp

theorem div_two (b a : ℕ) : 2 * a ≤ b → a ≤ b / 2 :=
  by simp_rw [Nat.le_div_iff_mul_le zero_lt_two, mul_comm, imp_self]

theorem sub_left_eq (a b c : Nat) (h : a = b) :  a - c = b - c := by rw [h]
