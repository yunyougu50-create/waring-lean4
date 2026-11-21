import WaringTheorem2

/-!
# 最终审计：Waring 定理

-/

namespace Waring

-- 1. 目标定理的陈述（与 WaringStatement 的定义对照）
#check @WaringTheorem
#check @IsSumOfKthPowers
#check @positiveDensity
#check @waringTheorem

-- 2. 关键中间引理
#check @rCount
#check @rCount_eq_integral
#check @rCount_le_integral
#check @rCount_le_poly
#check @sum_rCount_ge

-- 3. 公理审计
#print axioms waringTheorem
#print axioms positiveDensity

end Waring
