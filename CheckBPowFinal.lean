import WaringBPow

open Finset

namespace Waring

-- 定理的精确陈述
#check @normSq_pow_T_fiber
#check @BCount
#check @Qsum
#check @QSet
#check @PIdx
#check @dshift

#print axioms normSq_pow_T_fiber
#print axioms T_pow_expand
#print axioms conjT_pow_expand
#print axioms sum_diff_fiber_pi
#print axioms e_sum_finset

-- 一致性检查：`s = 1` 时 `sum_diff_fiber_pi` 与 `sum_diff_fiber` 是同一条分组
example (f : ℤ → ℤ) (N : ℕ) (h : ℤ) (α : ℝ) :
    ((Complex.normSq (T f N α h) : ℝ) : ℂ) ^ 1
      = ∑ Q ∈ QSet f N h 1, (BCount f N h 1 Q : ℂ) * e ((Q : ℝ) * α) :=
  normSq_pow_T_fiber f N h α 1 le_rfl

-- `s = 2` 特例（Weyl 归纳里最常用的四次幂）
example (f : ℤ → ℤ) (N : ℕ) (h : ℤ) (α : ℝ) :
    ((Complex.normSq (T f N α h) : ℝ) : ℂ) ^ 2
      = ∑ Q ∈ QSet f N h 2, (BCount f N h 2 Q : ℂ) * e ((Q : ℝ) * α) :=
  normSq_pow_T_fiber f N h α 2 (by norm_num)

-- `s = 4` 特例
example (f : ℤ → ℤ) (N : ℕ) (h : ℤ) (α : ℝ) :
    ((Complex.normSq (T f N α h) : ℝ) : ℂ) ^ 4
      = ∑ Q ∈ QSet f N h 4, (BCount f N h 4 Q : ℂ) * e ((Q : ℝ) * α) :=
  normSq_pow_T_fiber f N h α 4 (by norm_num)

end Waring
