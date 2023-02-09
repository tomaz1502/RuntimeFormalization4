import Mathlib.Data.List.Sort

#check List.orderedInsert
#check List.insertionSort

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

end timedSort

