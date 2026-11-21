import WaringLemma7

open Finset

/-! # `WaringLemma7` 的独立验证

1. 公理检查：主定理不依赖 `sorryAx`（只用标准三公理）。
2. 数值检查：`hmCount7` 的定义确实在计数（非平凡），并且界对小参数成立。
-/

-- 1. 公理检查
#print axioms Waring.hmCount7_le'
#print axioms Waring.hmCount7_le
#print axioms Waring.sum_Q7_sq_pos_le
#print axioms Waring.count7_eq_sum_sq
#print axioms Waring.Q7_le_sigma
#print axioms Waring.Q7_zero_le
#print axioms Waring.hmCount7_zero_left

-- 主定理的精确陈述
#check @Waring.hmCount7_le'

namespace CheckL7

/-- 可计算的 `q₇` 副本（仅用于数值验证，与 `Waring.Q7` 定义相同）。 -/
def box2c (lo hi : ℤ) : Finset (Fin 2 → ℤ) := Fintype.piFinset (fun _ : Fin 2 => Finset.Icc lo hi)

def Q7c (H M : ℕ) (n : ℤ) : ℕ :=
  ((((box2c (-(H : ℤ)) (H : ℤ)).erase 0).product (box2c (0 : ℤ) (M : ℤ))).filter
    (fun x : (Fin 2 → ℤ) × (Fin 2 → ℤ) => x.1 0 * x.2 0 + x.1 1 * x.2 1 = n)).card

def hBox7c (H : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 4 => (Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 0)

def mBox7c (M : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (0 : ℤ) (M : ℤ))

def hmCount7c (H M : ℕ) : ℕ :=
  (((hBox7c H).product (mBox7c M)).filter
    (fun hm => (∑ i : Fin 4, hm.1 i * hm.2 i) = 0)).card

-- 2. 数值检查
-- 手算：`q₇(1,1,0) = 14`（`h=(1,1),(-1,-1)` 各 1 个 + `h=(1,-1),(-1,1)` 各 2 个 + 4 个轴点各 2 个）
#eval Q7c 1 1 0
#eval Q7c 1 1 1
#eval Q7c 1 1 (-1)
-- 手算：`hmCount7(1,1) = Σ_{h∈{±1}⁴} #{T : Σ_{i∈T} hᵢ = 0} = 70`
#eval hmCount7c 1 1
#eval hmCount7c 1 2
#eval hmCount7c 2 2
#eval hmCount7c 2 3
-- 盒子大小：`H = 1` 时 `h` 有 `2^4 = 16` 个
#eval (hBox7c 1).card
#eval (mBox7c 1).card
-- 界
#eval (5250 * (1 * 1) ^ 3 : ℕ)
#eval (5250 * (2 * 2) ^ 3 : ℕ)
#eval (5250 * (2 * 3) ^ 3 : ℕ)

example : hmCount7c 1 1 = 70 := by native_decide
example : hmCount7c 1 1 ≤ 5250 * (1 * 1) ^ 3 := by native_decide
example : hmCount7c 2 2 ≤ 5250 * (2 * 2) ^ 3 := by native_decide
example : hmCount7c 2 3 ≤ 5250 * (2 * 3) ^ 3 := by native_decide

end CheckL7
