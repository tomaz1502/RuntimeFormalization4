import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem log_pred : ∀ (a : ℕ) , Nat.log 2 a - 1 = Nat.log 2 (a / 2)
| 0 => by simp only [Nat.log_zero_right, Nat.zero_div]
| 1 => by norm_num
| (a + 2) => by
  rw [Nat.log]
  split_ifs with h
  { simp [Nat.add_succ_sub_one, add_zero] }
  simp at h

theorem log_2_val : Nat.log 2 2 = 1 := by rfl
 
theorem sum_2b (a b : ℕ) : a ≤ 2 * b → a + 2 * b ≤ 4 * b := fun h =>
  calc a + 2 * b ≤ 2 * b + 2 * b := add_le_add h rfl.ge
       _         = 4 * b := by linarith


theorem log_2_times : ∀ (a : ℕ), 2 * Nat.log 2 (a + 2) ≤ a + 2
| 0       => by { rw [log_2_val] }
| (a + 1) => by
  have tmp : (a + 1) / 2 < a + 1 := Nat.div_lt_self' a 0
  rw [Nat.log]
  split_ifs
  { have ih := log_2_times ((a + 1) / 2)
    rw [mul_add]
    cases a with
    | zero    => rw [Nat.log]; simp
    | succ a' =>
        cases a' with
        | zero     => norm_num; rw [log_2_val]
        | succ a'' =>
          norm_num
          have add_one :
            2 * Nat.log 2 ((a''.succ.succ + 1) / 2).succ ≤
            2 * Nat.log 2 (((a''.succ.succ + 1) / 2) + 2) :=
              by apply Nat.mul_le_mul_left 2
                 apply Nat.log_monotone
                 exact Nat.le_succ ((a''.succ.succ + 1) / 2 + 1)
          apply le_trans add_one
          apply le_trans ih
          have succ_succ_two : a''.succ.succ + 1 = a'' + 3 := rfl
          have two_div_two : ∀ {y}, (y + 2) / 2 = y / 2 + 1 := by
            intro y; rw [(y + 2).div_eq 2]; simp
          have three_eq_one_plus_two : ∀ {y}, y + 3 = y + 1 + 2 := by
            intro y; rfl
          rw [ succ_succ_two
             , two_div_two
             , three_eq_one_plus_two
             , ← three_eq_one_plus_two
             ]
          apply flip add_le_add (le_refl 3)
          exact Nat.lt_succ_iff.mp (Nat.div_lt_self' a'' 0)
  }
  simp

theorem div_two (b a : ℕ) : 2 * a ≤ b → a ≤ b / 2 :=
  by simp_rw [Nat.le_div_iff_mul_le zero_lt_two, mul_comm, imp_self]
