import WaringTheorem1
import WaringLinnik
import WaringEventually
import WaringBound
import WaringSigned
import WaringDensity
import WaringWeylDiff
import WaringExpSum
import WaringWeylInq
import WaringCoeffBound
import WaringHolder
import WaringLemma7
import WaringQuadratic
import WaringInduction
-- 注意：`WaringBPow` 与 `WaringQuadratic` 都定义 `Waring.e_sum`（命名冲突），
-- 所以这里不 import 它；`bpow` 的成果由独立的 `CheckBPowFinal.lean` 验证。

/-!
# 全链条自检（Waring 形式化）

- `k = 2` 的 Theorem 1（Jameson Lemma 8）：`sqEqCount_le`、`integral_normSq_pow_four_le`
- 两块：Lemma 6 平方版 `sum_sigmaMinusOne_sq_le`、Lemma 3 `Q_le_sigma`
- 底层：`sqEqCount_le_sum_Q_sq`、`integral_normSq_pow_four_eq`
- 密度 → Waring：`waringTheorem_of_positive_density`、`schnirelmann`

`#print axioms` 应全部只给 `[propext, Classical.choice, Quot.sound]`。
-/

namespace Waring

#check @sqEqCount_le
#check @integral_normSq_pow_four_le
#check @sum_sigmaMinusOne_sq_le
#check @Q_le_sigma
#check @sqEqCount_le_sum_Q_sq
#check @integral_normSq_pow_four_eq
#check @waringTheorem_of_positive_density
#check @schnirelmann
#check @isWaringBound_of_density
-- Weyl 差分的代数零件（k ≥ 3 归纳用）
#check @diffH_polyEval
#check @diffCoeff_eq_zero_of_le
#check @pow_diff
#check @diffH_scaled_polyEval
-- 指数和与 Weyl 差分不等式（k ≥ 3 归纳）
#check @e_add
#check @norm_e
#check @normSq_expSum
#check @theta_eq_expSum
#check @integral_e_mul_int
#check @sum_diff_group
#check @normSq_expSum_le
#check @normSq_expSum_le_zero
#check @T_zero
#check @norm_T_zero
#check @e_int
#check @T_period
#check @polyEval_dvd
#check @T_period_polyEval
#check @normSq_T
#check @sum_diff_fiber
#check @normSq_T_fiber
#check @T_alpha_zero
-- Lemma 7 的 h≠0 版本（Weyl 归纳用）
#check @hmCount7
#check @hmCount7_le'
#check @hmCount7_le
-- 一般二次形式的 k=2 基例（Jameson Lemma 8）
#check @qSum
#check @qEqCount
#check @qEqCount_le
#check @integral_normSq_pow_four_le_q
-- 归纳命题 P(d)（Jameson Theorem 1 的骨架）
#check @MeanValueBound
#check @meanValueBound_apply
#check @meanValueBound_two
#check @MeanValueBoundS
#check @MeanValueBound.of_S
#check @qEqCount_le_MN
#check @meanValueBoundS_two
#check @sum_qQ_sq_le_K
#check @qEqCount_le_form
#check @integral_normSq_pow_four_le_form
-- `|b_h|^{2s}` 的按频率展开见 `WaringBPow.lean`（与 WaringQuadratic 有 `e_sum` 冲突，
-- 单独用 `CheckBPowFinal.lean` 检查）
#check @abs_diffCoeff_le
#check @diffCoeff_bound
#check @sum_pow_le_card_pow_mul_sum_pow
#check @holder_step
#check @add_pow_le_two_pow
#check @normSq_pow_le
#check @integral_normSq_pow_le

#print axioms diffH_polyEval
#print axioms normSq_expSum_le
#print axioms normSq_expSum_le_zero
#print axioms diffCoeff_bound
#print axioms holder_step
#print axioms normSq_pow_le
#print axioms integral_normSq_pow_le
#print axioms normSq_expSum
#print axioms sqEqCount_le
#print axioms integral_normSq_pow_four_le
#print axioms sum_sigmaMinusOne_sq_le
#print axioms Q_le_sigma
#print axioms waringTheorem_of_positive_density
#print axioms schnirelmann

end Waring
