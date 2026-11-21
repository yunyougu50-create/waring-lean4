import WaringIndStep2

/-!
# Theorem 1（一般 `k`）的自检

`WaringIndStep2.lean` 完成了 Jameson Theorem 1 的完整归纳：
`MeanValueBoundS 2`（基例）+ `MeanValueBoundS (d−1) → MeanValueBoundS d`（归纳步）
⟹ `∀ d ≥ 2, MeanValueBound d`。

本文件只做 `#check` + 公理审计。

**注意**：`WaringIndStep2` 与 `WaringInduction` 不能同时 import
（`Waring.MeanValueBoundS` 重名——前者为独立性逐字重述了它）。
`WaringIndStep2` 已包含 `meanValueBoundS_two`（加强版基例），所以
`WaringInduction` 的内容被完全覆盖。
-/

namespace Waring

-- 基例 / 归纳步 / 组装
#check @MeanValueBoundS
#check @MeanValueBound
#check @meanValueBoundS_two
#check @meanValueBoundS_succ
#check @meanValueBoundS_all
#check @meanValueBound_all

-- 证明链的关键中间引理
#check @pointwise_bound
#check @integral_bound
#check @four_sum_eq
#check @integral_norm_T_pow_le_R
#check @BCount_le_Rtot
#check @four_sum_le_count
#check @sum_QBox_le_MBox
#check @card_sym_shrink
#check @count_le
#check @Rd

#print axioms meanValueBoundS_two
#print axioms meanValueBoundS_succ
#print axioms meanValueBoundS_all
#print axioms meanValueBound_all

end Waring
