/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import WaringIndStep
import WaringLemma7
import WaringHolder
import WaringQuadSum
import WaringCoeffBound
import WaringQuadratic
import WaringLemma8Form

/-!
# 加强版归纳步 `MeanValueBoundS (d−1) → MeanValueBoundS d`

Jameson Theorem 1 的归纳步，加强版：求和长度 `M ≤ N`，系数尺度 `N`。

## 状态：**全部完成** ✅

本文件自包含给出完整的归纳：

* `meanValueBoundS_two : MeanValueBoundS 2`（基例，第 1 节末）；
* `meanValueBoundS_succ : 3 ≤ d → MeanValueBoundS (d−1) → MeanValueBoundS d`（归纳步）。

由此对一切 `d ≥ 2` 有 `MeanValueBoundS d`（外部用 `Nat.le_induction` 组装）。
**零 `sorry`/`admit`/`axiom`，编译 exit 0。**

> 文件末尾（第 13 节）保留了两段**注释掉的早期尝试**（旧 `count_le`、旧
> `meanValueBoundS_succ` 的算术），仅作参考，不参与编译。

## 记号

`m := 8^{d−2}`（`d ≥ 3` 时 `m ≥ 8`），于是 `8^{d−1} = 8m`，且 `m = 2s`，
`s = 4·8^{d−3}`（供 `integral_sum_pow_four` 使用）。

## 分块（全部已证明）

1. `pointwise_bound`（第 1–4 步）：`‖S‖^{8m} ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·B^4)`，
   其中 `B = Σ_{h≠0}‖b_h‖^m`（`SigTerm`）；辅助：`pow_four_bound`、`pointwise_alg`；
2. `integral_bound`（第 5 步）：逐项积分
   `∫‖S‖^{8m} ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·∫B^4)`；
3. `four_sum_eq`（第 6 步）：`∫ (Σ_h‖b_h‖^m)^4` 的四重和展开（`integral_sum_pow_four`，
   取 `s = 4·8^{d−3}`，`2s = m`，见 `two_mul_s`/`one_le_s`）；
4. `integral_norm_T_pow_le_R`（第 7 步）：由 `MVSBound (d−1) R₀` 得
   `∫‖b_h‖^{8^{d−2}} ≤ max(R₀(C),1)·N^{8^{d−2}−(d−1)}`（`C = coeffConst c d`）；
5. `BCount_le_Rtot`（第 6 步前半 + 第 7 步）：每个 `BCount` 同界；
6. `four_sum_le_count`（第 8 步）：
   `∫(Σ‖b_h‖^m)^4 ≤ Rtot^4 · #{(h₁..h₄, Q₁..Q₄) : Qᵢ ∈ QSet hᵢ, Q₁+…+Q₄ = 0}`；
7. 第 9 步的**准备**：
   * `QSet_exists`：`Q ∈ QSet` 可写成两个 `Qsum` 之差；
   * `QSet_dvd`：`f = polyEval a d` 时 `h ∣ Q`；
   * `polyEval_diffCoeff_abs_le`：`|φ(n)| ≤ (d+1)·coeffConst·N^{d−1}`（`|n|,|h| ≤ N`）；
   * `QSet_div_abs_le`：`Q ∈ QSet`、`h ≠ 0` ⟹ `|Q/h| ≤ 2s(d+1)·coeffConst·N^{d−1} =: Kf c d N`；
   * `sum_piFinset_fin4`：`Fintype.piFinset` 在 `Fin 4` 上展开成 4 层求和
     （把 8 层求和折叠成 `Fin 4 → ℤ` 上的求和所需的桥）；
8. **第 9 步 (9a) 已完成**：`sum_QBox_le_MBox`：
   `∑_{Q ∈ QSet⁴} [Q₁+…+Q₄ = 0] ≤ ∑_{m ∈ ([−Kf,Kf])⁴} [h₁m₁+…+h₄m₄ = 0]`
   （映射 `Q ↦ fun i => Q i / hh i`，单射性来自 `QSet_dvd`，像落在 `Kf` 盒来自
   `QSet_div_abs_le`）；
9. **第 9 步 (9b) 已完成**：`card_sym_shrink`：
   `#{h ∈ hBox7 M, m ∈ ([−K,K])⁴, Σ hᵢmᵢ = 0} ≤ 16·hmCount7 M K`。
   映射 `sgnMap : (h, m) ↦ ((sgn(mᵢ)·hᵢ, |mᵢ|), sgn(mᵢ))` —— **符号翻转作用在 `hᵢ` 上**，
   故 `Σᵢ (sgn(mᵢ)hᵢ)·|mᵢ| = Σᵢ hᵢ(sgn(mᵢ)|mᵢ|) = Σᵢ hᵢmᵢ`，方程保持不变；
   像落在 `hmCount7 的盒子 × SymBox`（`SymBox = {±1}⁴`，`card = 16`）；
10. **基例（自包含）**：`meanValueBoundS_two : MeanValueBoundS 2`，
    连同 `polyEval_two_eq`、`expSum_polyEval_two`、`qEqCount_le_MN`
    （从 `WaringInduction` 逐字搬入；因 `import WaringQuadratic` 无命名冲突）；
11. **第 9 步 (9c) 已完成**：`count_le`：
    `∑_{h₁..h₄} ∑_{Q₁∈QSet hᵢ} [Q₁+…+Q₄ = 0] ≤ 16·5250·(M·Kf)³`。
    证明链：`sum_four_Q_le_MBox`（4 层 `Q ↦ Q/h` 逐层放大到 `Kf` 盒子，
    用 `Finset.sum_image` + `QSet_dvd` + `QSet_div_abs_le`，**不展开 `QSet`**）
    → `sum_piFinset_fin4`（`hBox7 M` 与 `KB` 的 4 层折叠）
    → `card_filter`（`∑ if … then 1 else 0 = card`，先 `ℕ` 后 `exact_mod_cast`）
    → `card_sym_shrink`（9b）→ `hmCount7_le'`（Lemma 7，需 `M ≤ Kf`，由 `le_Kf`）。
    辅助：`sum_piFinset_fin4_dep`、`one_le_c`、`coeffConst_pos`、`le_Kf`、`QSf`。

## 第 10 步（常数账 + 组装，已完成）

`Rd d R₀ c = 2^{4(m−1)}·8·(2^{4m} + 2^{4(m−1)}·Rmax⁴·16·5250·Ck³)`，其中
`Rmax = max(R₀(C),1)`、`Ck = 2s(d+1)·coeffConst`，于是
`∫ ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·Rmax⁴·N^{4(m−(d−1))}·16·5250·Ck³·N^{3d})`
= `Rd·N^{8m−d}`。指数核对：`4(m−1) + 4(m−(d−1)) + 3d = 8m − d` ✓
（`3d = 3 + 3(d−1)`：`M ≤ N` 贡献 `3`，`Kf = Ck·N^{d−1}` 贡献 `3(d−1)`）。
关键辅助：`hKf`（`Kf = Ck·N^{d−1}`）、`hmge : d−1 ≤ m`（`Nat.lt_two_pow_self`
+ `8 = 2^3`）、`hexp1`、`hNfin`、`hP1`、`hP2`、`hP2` 的 `mul_le_mul` 需先给
`intervalIntegral.integral_nonneg`。

## 环境说明

`WaringIndStep`（依赖 `WaringBPow`/`WaringQuadSum`）与 `WaringInduction`（依赖
`WaringQuadratic`）因 `e_sum` 命名冲突不能同时 import，故本文件**逐字重述**
`MeanValueBoundS` 的定义（与 `WaringInduction.MeanValueBoundS` 完全相同）。
注意：`WaringQuadratic`/`WaringLemma8Form` **可以**与本文件的 `WaringIndStep` 链
一起 import（`WaringBPow` 的 `e_sum` 已改名 `e_sum_finset`），基例因此可以自包含。
-/

open Finset intervalIntegral

namespace Waring

/-! ## 0. 命题陈述（与 `WaringInduction.MeanValueBoundS` 逐字相同） -/

/-- **加强版归纳命题**（`M ≤ N`）：求和长度 `M` 可以小于系数尺度的 `N`，
但界仍然用 `N`。 -/
def MeanValueBoundS (d : ℕ) : Prop :=
  ∃ R : ℕ → ℝ, (∀ c, 0 < R c) ∧
    ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
      (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
      (∫ α in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
        ≤ R c * (N : ℝ) ^ (8 ^ (d - 1) - d)

/-! 由 `MeanValueBoundS d` 取 `M = N` 得原版（与 `WaringInduction` 的同名引理一致）。 -/

/-- `MeanValueBoundS d` 的显式应用形式（解包 `∃ R`）。 -/
theorem MeanValueBoundS.apply {d : ℕ} (h : MeanValueBoundS d) (c N M : ℕ)
    (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hMN : M ≤ N) (a : ℕ → ℤ) (had : a d ≠ 0)
    (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) :
    ∃ R : ℝ, 0 < R ∧
      (∫ α in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
        ≤ R * (N : ℝ) ^ (8 ^ (d - 1) - d) := by
  obtain ⟨R, hR, hbound⟩ := h
  exact ⟨R c, hR c, hbound c N M hN hM1 hMN a had ha⟩

/-! ## 1. 第 1–4 步：点态界 -/

/-- `B = Σ_{h≠0, |h|≤M} ‖b_h‖^m`，其中 `m = 8^{d−2}`。 -/
noncomputable def SigTerm (a : ℕ → ℤ) (d M : ℕ) (α : ℝ) : ℝ :=
  ∑ h ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
    ‖T (fun n => polyEval a d n) M α h‖ ^ (8 ^ (d - 2))

/-- `(A+B)^4 ≤ 8(A^4 + B^4)`（`A, B ≥ 0`）。 -/
theorem pow_four_bound (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A + B) ^ 4 ≤ 8 * (A ^ 4 + B ^ 4) := by
  have h := add_pow_le_two_pow A B hA hB 4 (by norm_num)
  norm_num at h
  linarith

/-- 纯代数整理（第 2–4 步）：
`(2^{m−1}·((M+1)^m + (2M)^{m−1}·T))^4 ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·T^4)`。 -/
theorem pointwise_alg (M m : ℕ) (Tv : ℝ) (hTv : 0 ≤ Tv) :
    (2 ^ (m - 1) * ((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv)) ^ 4
      ≤ 2 ^ (4 * (m - 1)) * 8 * ((M + 1 : ℝ) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * Tv ^ 4) := by
  have h1 : (2 ^ (m - 1) * ((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv)) ^ 4
      = 2 ^ (4 * (m - 1))
        * (((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv) ^ 4) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm (m - 1) 4]
  rw [h1]
  have hA0 : (0 : ℝ) ≤ (M + 1 : ℝ) ^ m := by positivity
  have hB0 : (0 : ℝ) ≤ (2 * (M : ℝ)) ^ (m - 1) * Tv := by positivity
  have h2 := pow_four_bound _ _ hA0 hB0
  have h3 : (((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv) ^ 4)
      ≤ 8 * ((M + 1 : ℝ) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * Tv ^ 4) := by
    refine le_trans h2 (le_of_eq ?_)
    congr 2
    · rw [← pow_mul, Nat.mul_comm m 4]
    · rw [mul_pow, ← pow_mul, Nat.mul_comm (m - 1) 4]
  calc 2 ^ (4 * (m - 1))
        * (((M + 1 : ℝ) ^ m + (2 * (M : ℝ)) ^ (m - 1) * Tv) ^ 4)
      ≤ 2 ^ (4 * (m - 1)) * (8 * ((M + 1 : ℝ) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * Tv ^ 4)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 ^ (4 * (m - 1)) * 8 * ((M + 1 : ℝ) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * Tv ^ 4) := by ring

/-- **第 1–4 步（点态）**：`‖S‖^{8^{d−1}} ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·B^4)`。 -/
theorem pointwise_bound {d : ℕ} (hd : 3 ≤ d) (a : ℕ → ℤ) {M : ℕ} (hM1 : 1 ≤ M) (α : ℝ) :
    ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1))
      ≤ 2 ^ (4 * (8 ^ (d - 2) - 1)) * 8 *
          ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
            + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1)) * (SigTerm a d M α) ^ 4) := by
  have hm1 : 1 ≤ 8 ^ (d - 2) := by
    have h : (0 : ℕ) < 8 ^ (d - 2) := pow_pos (by norm_num) _
    omega
  have hpt := normSq_pow_le (fun n => polyEval a d n) M α (8 ^ (d - 2)) hm1 hM1
  have hTv : 0 ≤ SigTerm a d M α := by
    apply Finset.sum_nonneg
    intro h _
    positivity
  have hpow : 8 ^ (d - 1) = (2 * 8 ^ (d - 2)) * 4 := by
    have h1 : d - 1 = (d - 2) + 1 := by omega
    rw [h1, pow_succ]
    ring
  rw [hpow, pow_mul]
  exact le_trans (pow_le_pow_left₀ (by positivity) hpt 4)
    (pointwise_alg M (8 ^ (d - 2)) (SigTerm a d M α) hTv)

/-! ## 2. 第 5 步：积分 -/

/-- **第 5 步（积分）**：
`∫‖S‖^{8m} ≤ 2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·∫B^4)`。 -/
theorem integral_bound {d : ℕ} (hd : 3 ≤ d) (a : ℕ → ℤ) {M : ℕ} (hM1 : 1 ≤ M) :
    (∫ α in (0 : ℝ)..1, ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
      ≤ 2 ^ (4 * (8 ^ (d - 2) - 1)) * 8 *
          ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
            + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
              * ∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4) := by
  set g : ℝ → ℝ := fun α => 2 ^ (4 * (8 ^ (d - 2) - 1)) * 8 *
      ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
        + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1)) * (SigTerm a d M α) ^ 4) with hg
  have hcont1 : Continuous fun α : ℝ =>
      ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)) := by
    unfold expSum e
    fun_prop
  have hcont2 : Continuous fun α : ℝ => (SigTerm a d M α) ^ 4 := by
    unfold SigTerm T e
    fun_prop
  have hcontg : Continuous g := by
    rw [hg]
    simp only [mul_assoc]
    unfold SigTerm T e
    fun_prop
  have hmono : (∫ α in (0 : ℝ)..1, ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
      ≤ ∫ α in (0 : ℝ)..1, g α := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      (hcont1.intervalIntegrable 0 1) (hcontg.intervalIntegrable 0 1) ?_
    intro α _
    rw [hg]
    exact pointwise_bound hd a hM1 α
  have hsplit : (∫ x in (0 : ℝ)..1, ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
        + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1)) * SigTerm a d M x ^ 4))
      = (M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
        + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
          * (∫ x in (0 : ℝ)..1, SigTerm a d M x ^ 4) := by
    have step1 : (∫ x in (0 : ℝ)..1, ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
          + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1)) * SigTerm a d M x ^ 4))
        = (∫ x in (0 : ℝ)..1, ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))))
          + (∫ x in (0 : ℝ)..1, ((2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
              * SigTerm a d M x ^ 4)) :=
      intervalIntegral.integral_add intervalIntegrable_const
        ((continuous_const.mul hcont2).intervalIntegrable 0 1)
    rw [step1, intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
    ring
  have hgi : (∫ α in (0 : ℝ)..1, g α)
      = 2 ^ (4 * (8 ^ (d - 2) - 1)) * 8 *
          ((M + 1 : ℝ) ^ (4 * 8 ^ (d - 2))
            + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
              * ∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4) := by
    rw [hg]
    simp only [mul_assoc]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hsplit]
  exact le_trans hmono (le_of_eq hgi)

/-! ## 3. 第 6 步：四重和与正交性 -/

/-- 展开 `∫ (Σ_h ‖b_h‖^m)^4`（`m = 8^{d−2} = 2s`，`s = 4·8^{d−3}`）。 -/
theorem four_sum_eq {d : ℕ} (hd : 3 ≤ d) (a : ℕ → ℤ) (M : ℕ) :
    (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
      = ∑ h1 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h2 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h3 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h4 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ Q1 ∈ QSet (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)),
        ∑ Q2 ∈ QSet (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)),
        ∑ Q3 ∈ QSet (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)),
        ∑ Q4 ∈ QSet (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)),
          (if Q1 + Q2 + Q3 + Q4 = 0 then
            (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1
              * BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2
              * BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3
              * BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ)
          else 0) := by
  have hs1 : 1 ≤ 4 * 8 ^ (d - 3) := by
    have h : 0 < 4 * 8 ^ (d - 3) := by positivity
    omega
  have h2s : 2 * (4 * 8 ^ (d - 3)) = 8 ^ (d - 2) := by
    have h1 : d - 2 = (d - 3) + 1 := by omega
    rw [h1, pow_succ]
    ring
  have h := integral_sum_pow_four (fun n => polyEval a d n) M (4 * 8 ^ (d - 3)) hs1
  rw [h2s] at h
  exact h

/-! ## 4. 第 7 步：每个 `∫₀¹‖b_h‖^{8^{d−2}}` 的上界（用 `P(d−1)`）

`P(d−1)` 的解包形式：常数族 `R` 与界。 -/

/-- `P(k)` 的显式形式（`R` 固定）。 -/
def MVSBound (k : ℕ) (R : ℕ → ℝ) : Prop :=
  ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a k ≠ 0 →
    (∀ j, j ≤ k → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (k - j)) →
    (∫ α in (0 : ℝ)..1, ‖expSum (fun n => polyEval a k n) M α‖ ^ (8 ^ (k - 1)))
      ≤ R c * (N : ℝ) ^ (8 ^ (k - 1) - k)

set_option maxHeartbeats 4000000 in
/-- **第 7 步**：`P(d−1) ⇒ ∫₀¹‖b_h‖^{8^{d−2}} ≤ max(R(C),1)·N^{8^{d−2}−(d−1)}`。 -/
theorem integral_norm_T_pow_le_R {d : ℕ} (hd : 3 ≤ d) {R₀ : ℕ → ℝ}
    (hMV : MVSBound (d - 1) R₀) :
    ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
    (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
    ∀ h ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      (∫ α in (0 : ℝ)..1, ‖T (fun n => polyEval a d n) M α h‖ ^ (8 ^ (d - 2)))
        ≤ max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := by
  intro c N M hN hM1 hMN a had ha
  have hd1 : 1 ≤ d := by omega
  have hexp : (d - 1) - 1 = d - 2 := by omega
  intro h hS
  rw [Finset.mem_erase, Finset.mem_Icc] at hS
  obtain ⟨hne, hle1, hle2⟩ := hS
  have main : ∀ (g : ℤ), 0 < g → g.toNat ≤ M →
      (∫ α in (0 : ℝ)..1, ‖T (fun n => polyEval a d n) M α g‖ ^ (8 ^ (d - 2)))
        ≤ max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := by
    intro g hg hgM
    rw [integral_norm_T_pow_eq (a := a) (d := d) (N := M) (h := g) hg hgM (8 ^ (d - 2))]
    -- 次数从 `d` 降到 `d−1`
    have hstep : (∫ β in (0 : ℝ)..1,
        ‖expSum (fun n => polyEval (diffCoeff a d g) d n) (M - g.toNat) β‖ ^ (8 ^ (d - 2)))
        = ∫ β in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) (M - g.toNat) β‖ ^
            (8 ^ (d - 2)) := by
      apply intervalIntegral.integral_congr
      intro β _
      have hfun : (fun n => polyEval (diffCoeff a d g) d n)
          = (fun n => polyEval (diffCoeff a d g) (d - 1) n) := by
        funext n
        exact polyEval_eq_of_last_zero (diffCoeff a d g) hd1 (diffCoeff_eq_zero_of_le le_rfl) n
      rw [hfun]
    rw [hstep]
    rcases Nat.eq_zero_or_pos (M - g.toNat) with h0 | h1pos
    · -- 长度为零：指数和只有一项
      rw [h0]
      have hpt : ∀ β : ℝ,
          ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ ^ (8 ^ (d - 2)) ≤ 1 := by
        intro β
        have hnorm : ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ = 1 := by
          unfold expSum
          rw [Finset.range_one, Finset.sum_singleton, norm_e]
        rw [hnorm, one_pow]
      have hcont : Continuous fun β : ℝ =>
          ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ ^ (8 ^ (d - 2)) := by
        unfold expSum e
        fun_prop
      have hbound : (∫ β in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ ^ (8 ^ (d - 2))) ≤ 1 := by
        calc (∫ β in (0 : ℝ)..1,
              ‖expSum (fun n => polyEval (diffCoeff a d g) (d - 1) n) 0 β‖ ^ (8 ^ (d - 2)))
            ≤ ∫ β in (0 : ℝ)..1, (1 : ℝ) :=
              intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable 0 1)
                intervalIntegrable_const (fun x _ => hpt x)
          _ = 1 := by simp
      refine le_trans hbound ?_
      have h1 : (1 : ℝ) ≤ max (R₀ (coeffConst c d)) 1 := le_max_right _ _
      have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := one_le_pow₀ (by exact_mod_cast hN)
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) :=
            mul_le_mul h1 h2 (by norm_num) (by linarith)
    · -- 一般情形：用 `P(d−1)`
      have htoNatZ : ((g.toNat : ℕ) : ℤ) = g := Int.toNat_of_nonneg (le_of_lt hg)
      have habs : |g| ≤ (N : ℤ) := by
        have h2 : ((g.toNat : ℕ) : ℤ) ≤ (N : ℤ) := by
          have h3 : g.toNat ≤ N := le_trans hgM hMN
          exact_mod_cast h3
        rw [htoNatZ] at h2
        rw [abs_of_pos hg]
        exact h2
      have hcoeff : ∀ j, j ≤ d - 1 →
          |diffCoeff a d g j| ≤ (coeffConst c d : ℤ) * (N : ℤ) ^ ((d - 1) - j) := by
        intro j hj
        exact diffCoeff_bound' (a := a) (d := d) (h := g) (c := c) (N := N) ha habs j (by omega)
      have hblast : diffCoeff a d g (d - 1) ≠ 0 := by
        rw [diffCoeff_last hd1 g]
        exact mul_ne_zero had (by exact_mod_cast (show d ≠ 0 by omega))
      have hres := hMV (coeffConst c d) N (M - g.toNat) hN h1pos (by omega)
        (diffCoeff a d g) hblast hcoeff
      rw [hexp] at hres
      refine le_trans hres ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- `h < 0`：换成 `−h > 0`
    have htoNat : (-h).toNat ≤ M := by
      have h1 : (((-h).toNat : ℕ) : ℤ) = -h := Int.toNat_of_nonneg (by omega)
      have h2 : (((-h).toNat : ℕ) : ℤ) ≤ (M : ℤ) := by rw [h1]; linarith
      exact_mod_cast h2
    have heq : (∫ α in (0 : ℝ)..1, ‖T (fun n => polyEval a d n) M α h‖ ^ (8 ^ (d - 2)))
        = ∫ α in (0 : ℝ)..1, ‖T (fun n => polyEval a d n) M α (-h)‖ ^ (8 ^ (d - 2)) := by
      apply intervalIntegral.integral_congr
      intro α _
      have hh := norm_T_neg (f := fun n => polyEval a d n) (N := M) (h := -h) (by omega) htoNat α
      show ‖T (fun n => polyEval a d n) M α h‖ ^ (8 ^ (d - 2))
        = ‖T (fun n => polyEval a d n) M α (-h)‖ ^ (8 ^ (d - 2))
      rw [show ‖T (fun n => polyEval a d n) M α h‖ = ‖T (fun n => polyEval a d n) M α (-h)‖ by
        simpa using hh]
    rw [heq]
    exact main (-h) (by omega) htoNat
  · -- `h > 0`
    have htoNatM : h.toNat ≤ M := by
      have h1 : ((h.toNat : ℕ) : ℤ) = h := Int.toNat_of_nonneg (by omega)
      have h2 : ((h.toNat : ℕ) : ℤ) ≤ (M : ℤ) := by rw [h1]; exact hle2
      exact_mod_cast h2
    exact main h hpos htoNatM

/-! ## 5. 第 8 步：四重和逐项放大到 `Rtot^4` 乘计数 -/

/-- `2·(4·8^{d−3}) = 8^{d−2}`（`d ≥ 3`）。 -/
theorem two_mul_s {d : ℕ} (hd : 3 ≤ d) : 2 * (4 * 8 ^ (d - 3)) = 8 ^ (d - 2) := by
  have h1 : d - 2 = (d - 3) + 1 := by omega
  rw [h1, pow_succ]
  ring

/-- `1 ≤ 4·8^{d−3}`。 -/
theorem one_le_s (d : ℕ) : 1 ≤ 4 * 8 ^ (d - 3) := by
  have h : 0 < 4 * 8 ^ (d - 3) := by positivity
  omega

/-- **每个 `BCount` 的上界**（第 6 步前半 + 第 7 步）。 -/
theorem BCount_le_Rtot {d : ℕ} (hd : 3 ≤ d) {R₀ : ℕ → ℝ}
    (hMV : MVSBound (d - 1) R₀) :
    ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
    (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
    ∀ (h : ℤ), h ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0 → ∀ Q : ℤ,
      (BCount (fun n => polyEval a d n) M h (4 * 8 ^ (d - 3)) Q : ℝ)
        ≤ max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := by
  intro c N M hN hM1 hMN a had ha h hS Q
  have h1 := BCount_le_integral (fun n => polyEval a d n) M h (4 * 8 ^ (d - 3))
    (one_le_s d) Q
  rw [two_mul_s hd] at h1
  exact le_trans h1 (integral_norm_T_pow_le_R hd hMV c N M hN hM1 hMN a had ha h hS)

/-- **第 8 步**：四重和被 `Rtot^4` 乘「满足 `Q₁+…+Q₄ = 0` 的项数」控制。 -/
theorem four_sum_le_count {d : ℕ} (hd : 3 ≤ d) {R₀ : ℕ → ℝ}
    (hMV : MVSBound (d - 1) R₀) :
    ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
    (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
    (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
      ≤ (max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1))) ^ 4
        * (∑ h1 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
          ∑ h2 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
          ∑ h3 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
          ∑ h4 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
          ∑ Q1 ∈ QSet (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)),
          ∑ Q2 ∈ QSet (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)),
          ∑ Q3 ∈ QSet (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)),
          ∑ Q4 ∈ QSet (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)),
            (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0)) := by
  intro c N M hN hM1 hMN a had ha
  rw [four_sum_eq hd a M]
  set Rt : ℝ := max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) with hRt
  have hRtpos : 0 < Rt := by
    rw [hRt]
    have h1 : (0 : ℝ) < max (R₀ (coeffConst c d)) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have h3 : (0 : ℝ) < (N : ℝ) ^ (8 ^ (d - 2) - (d - 1)) := by
      have : (0:ℝ) < N := by exact_mod_cast hN
      positivity
    exact mul_pos h1 h3
  have hRt0 : 0 ≤ Rt := le_of_lt hRtpos
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum (fun h1 h1S => Finset.sum_le_sum (fun h2 h2S =>
    Finset.sum_le_sum (fun h3 h3S => Finset.sum_le_sum (fun h4 h4S =>
    Finset.sum_le_sum (fun Q1 Q1S => Finset.sum_le_sum (fun Q2 Q2S =>
    Finset.sum_le_sum (fun Q3 Q3S => Finset.sum_le_sum (fun Q4 Q4S => ?_))))))))
  have hB1 : (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ) ≤ Rt := by
    rw [hRt]; exact BCount_le_Rtot hd hMV c N M hN hM1 hMN a had ha h1 h1S Q1
  have hB2 : (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ) ≤ Rt := by
    rw [hRt]; exact BCount_le_Rtot hd hMV c N M hN hM1 hMN a had ha h2 h2S Q2
  have hB3 : (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ) ≤ Rt := by
    rw [hRt]; exact BCount_le_Rtot hd hMV c N M hN hM1 hMN a had ha h3 h3S Q3
  have hB4 : (BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ) ≤ Rt := by
    rw [hRt]; exact BCount_le_Rtot hd hMV c N M hN hM1 hMN a had ha h4 h4S Q4
  have hC1 : (0 : ℝ) ≤ (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ) := by
    positivity
  have hC2 : (0 : ℝ) ≤ (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ) := by
    positivity
  have hC3 : (0 : ℝ) ≤ (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ) := by
    positivity
  have hC4 : (0 : ℝ) ≤ (BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ) := by
    positivity
  have hP : (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ)
      * (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ)
      * (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ)
      * (BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ) ≤ Rt ^ 4 := by
    have h12 : (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ)
        * (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ) ≤ Rt * Rt :=
      mul_le_mul hB1 hB2 hC2 hRt0
    have h123 : (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ)
        * (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ)
        * (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ) ≤ Rt * Rt * Rt :=
      mul_le_mul h12 hB3 hC3 (by positivity)
    have h1234 := mul_le_mul h123 hB4 hC4 (by positivity)
    calc (BCount (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)) Q1 : ℝ)
          * (BCount (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)) Q2 : ℝ)
          * (BCount (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)) Q3 : ℝ)
          * (BCount (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)) Q4 : ℝ)
        ≤ Rt * Rt * Rt * Rt := h1234
      _ = Rt ^ 4 := by ring
  by_cases hc : Q1 + Q2 + Q3 + Q4 = 0
  · rw [if_pos hc, if_pos hc, mul_one]
    exact hP
  · rw [if_neg hc, if_neg hc, mul_zero]

/-! ## 6. 第 9 步：计数桥接的准备（`QSet ⊆ hℤ` 与 `|Q/h|` 的界） -/

/-- `n ∈ TS M h ⇒ n ≤ M`。 -/
theorem mem_TS_le {M : ℕ} {h : ℤ} {n : ℕ} (hn : n ∈ TS M h) : n ≤ M := by
  rw [TS, Finset.mem_filter, Finset.mem_range] at hn
  omega

/-- `Q ∈ QSet` 可以写成两个 `Qsum` 之差。 -/
theorem QSet_exists {f : ℤ → ℤ} {M : ℕ} {h : ℤ} {s : ℕ} {Q : ℤ}
    (hQ : Q ∈ QSet f M h s) :
    ∃ u ∈ PIdx M h s, ∃ v ∈ PIdx M h s, Q = Qsum f h u - Qsum f h v := by
  classical
  rw [QSet] at hQ
  obtain ⟨a, ha, hQa⟩ := Finset.mem_biUnion.mp hQ
  rw [Finset.mem_image] at ha hQa
  obtain ⟨v, hv, hav⟩ := ha
  obtain ⟨b, hb, hQb⟩ := hQa
  rw [Finset.mem_image] at hb
  obtain ⟨u, hu, hbu⟩ := hb
  subst hav hbu
  exact ⟨u, hu, v, hv, hQb.symm⟩

/-- 多项式情形：`QSet` 中的每个频率都被 `h` 整除。 -/
theorem QSet_dvd {a : ℕ → ℤ} {d : ℕ} {M : ℕ} {h : ℤ} {s : ℕ} {Q : ℤ}
    (hQ : Q ∈ QSet (fun n => polyEval a d n) M h s) : h ∣ Q := by
  obtain ⟨u, hu, v, hv, hQeq⟩ := QSet_exists hQ
  rw [hQeq, Qsum_polyEval, Qsum_polyEval]
  exact ⟨(∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ))
      - (∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ)), by ring⟩

/-- `φ(n) = polyEval (diffCoeff a d h) d n` 在 `|n| ≤ N` 上的界。 -/
theorem polyEval_diffCoeff_abs_le {a : ℕ → ℤ} {d : ℕ} {h : ℤ} {c N : ℕ}
    (hd : 1 ≤ d) (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j))
    (hh : |h| ≤ (N : ℤ)) {n : ℤ} (hn : |n| ≤ (N : ℤ)) :
    |polyEval (diffCoeff a d h) d n| ≤ (((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1) := by
  unfold polyEval
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ j ∈ Finset.range (d + 1),
      |diffCoeff a d h j * n ^ j| ≤ ((coeffConst c d : ℤ) * (N : ℤ) ^ (d - 1)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases lt_or_eq_of_le (show j ≤ d from by omega) with hjd | hjd
    · rw [abs_mul, abs_pow]
      have h1 := diffCoeff_bound' (a := a) (d := d) (h := h) (c := c) (N := N) ha hh j hjd
      have hnabs : |n| ^ j ≤ (N : ℤ) ^ j := pow_le_pow_left₀ (abs_nonneg n) hn j
      have hN0 : (0 : ℤ) ≤ (N : ℤ) := by positivity
      calc |diffCoeff a d h j| * |n| ^ j
          ≤ ((coeffConst c d : ℤ) * (N : ℤ) ^ (d - 1 - j)) * (N : ℤ) ^ j :=
            mul_le_mul h1 hnabs (by positivity) (by positivity)
        _ = (coeffConst c d : ℤ) * ((N : ℤ) ^ (d - 1 - j) * (N : ℤ) ^ j) := by ring
        _ = (coeffConst c d : ℤ) * (N : ℤ) ^ ((d - 1 - j) + j) := by rw [pow_add]
        _ = (coeffConst c d : ℤ) * (N : ℤ) ^ (d - 1) := by
            rw [show d - 1 - j + j = d - 1 by omega]
    · rw [hjd, diffCoeff_eq_zero_of_le le_rfl]
      simp only [zero_mul, abs_zero]
      positivity
  calc ∑ j ∈ Finset.range (d + 1), |diffCoeff a d h j * n ^ j|
      ≤ ∑ j ∈ Finset.range (d + 1), ((coeffConst c d : ℤ) * (N : ℤ) ^ (d - 1)) :=
        Finset.sum_le_sum hterm
    _ = ((d + 1 : ℕ) : ℤ) * ((coeffConst c d : ℤ) * (N : ℤ) ^ (d - 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1) := by
        push_cast
        ring

/-- **频率比的大小界**：`Q ∈ QSet`、`h ≠ 0` 时 `|Q/h| ≤ 2s·(d+1)·coeffConst·N^{d−1}`。 -/
theorem QSet_div_abs_le {a : ℕ → ℤ} {d : ℕ} {c N M : ℕ} {h : ℤ} {s : ℕ} {Q : ℤ}
    (hd : 1 ≤ d) (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j))
    (hhN : |h| ≤ (N : ℤ)) (hNM : M ≤ N) (hh0 : h ≠ 0)
    (hQ : Q ∈ QSet (fun n => polyEval a d n) M h s) :
    |Q / h| ≤ ((2 * s * ((d + 1) * coeffConst c d) * N ^ (d - 1) : ℕ) : ℤ) := by
  obtain ⟨u, hu, v, hv, hQeq⟩ := QSet_exists hQ
  have hU : ∀ i, u i ∈ TS M h := fun i => Fintype.mem_piFinset.mp hu i
  have hV : ∀ i, v i ∈ TS M h := fun i => Fintype.mem_piFinset.mp hv i
  have hb : ∀ (w : Fin s → ℕ), (∀ i, w i ∈ TS M h) →
      |∑ i : Fin s, polyEval (diffCoeff a d h) d (w i : ℤ)|
        ≤ (s : ℤ) * ((((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1)) := by
    intro w hw
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ i : Fin s, |polyEval (diffCoeff a d h) d (w i : ℤ)|
        ≤ (((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1) := by
      intro i
      have hi : w i ≤ M := mem_TS_le (hw i)
      have hn : |((w i : ℕ) : ℤ)| ≤ (N : ℤ) := by
        rw [abs_of_nonneg (by positivity)]
        have h1 : ((w i : ℕ) : ℤ) ≤ (M : ℤ) := by exact_mod_cast hi
        have h2 : (M : ℤ) ≤ (N : ℤ) := by exact_mod_cast hNM
        linarith
      exact polyEval_diffCoeff_abs_le hd ha hhN hn
    calc ∑ i : Fin s, |polyEval (diffCoeff a d h) d (w i : ℤ)|
        ≤ ∑ i : Fin s, (((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = (s : ℤ) * ((((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hQeq, Qsum_polyEval, Qsum_polyEval]
  have heq : (h * (∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ))
        - h * (∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ))) / h
      = (∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ))
        - (∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ)) := by
    rw [show h * (∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ))
          - h * (∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ))
        = h * ((∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ))
          - (∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ))) by ring]
    exact Int.mul_ediv_cancel_left _ hh0
  rw [heq]
  have h1 := hb u hU
  have h2 := hb v hV
  have h3 : |(∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ))
      - (∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ))|
      ≤ |∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ)|
        + |∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ)| := abs_sub _ _
  have h4 : |(∑ i : Fin s, polyEval (diffCoeff a d h) d (u i : ℤ))
      - (∑ i : Fin s, polyEval (diffCoeff a d h) d (v i : ℤ))|
      ≤ (s : ℤ) * ((((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1))
        + (s : ℤ) * ((((d + 1) * coeffConst c d : ℕ) : ℤ) * (N : ℤ) ^ (d - 1)) := by
    linarith
  refine le_trans h4 (le_of_eq ?_)
  push_cast
  ring

/-! ## 7. 第 9 步：把 8 层求和折叠成 `Fin 4 → ℤ` 上的计数 -/

/-- `Fintype.piFinset` 在 `Fin 4` 上展开成 4 层求和。 -/
theorem sum_piFinset_fin4 {α : Type*} [DecidableEq α] (S : Finset α)
    (F : (Fin 4 → α) → ℝ) :
    (∑ f ∈ Fintype.piFinset (fun _ : Fin 4 => S), F f)
      = ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, ∑ d ∈ S,
          F (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d) := by
  classical
  let g : α × (α × (α × α)) → ℝ := fun y => F (fun i => if i = 0 then y.1
    else if i = 1 then y.2.1 else if i = 2 then y.2.2.1 else y.2.2.2)
  have hsplit : (∑ x ∈ S ×ˢ (S ×ˢ (S ×ˢ S)), g x)
      = ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, ∑ d ∈ S,
          F (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d) := by
    have h1 : (∑ x ∈ S ×ˢ (S ×ˢ (S ×ˢ S)), g x)
        = ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, ∑ d ∈ S, g (a, (b, (c, d))) := by
      simp only [Finset.sum_product]
    rw [h1]
  rw [← hsplit]
  refine Finset.sum_bij
    (fun (f : Fin 4 → α) (_ : f ∈ Fintype.piFinset (fun _ : Fin 4 => S)) =>
      (f 0, (f 1, (f 2, f 3)))) ?_ ?_ ?_ ?_
  · -- 像落入盒子
    intro f hf
    rw [Fintype.mem_piFinset] at hf
    rw [Finset.mem_product, Finset.mem_product, Finset.mem_product]
    exact ⟨hf 0, hf 1, hf 2, hf 3⟩
  · -- 单射
    intro f _ f' _ heq
    have h1 : f 0 = f' 0 := by simpa using congrArg (fun z => z.1) heq
    have h2 : f 1 = f' 1 := by simpa using congrArg (fun z => z.2.1) heq
    have h3 : f 2 = f' 2 := by simpa using congrArg (fun z => z.2.2.1) heq
    have h4 : f 3 = f' 3 := by simpa using congrArg (fun z => z.2.2.2) heq
    funext i
    fin_cases i <;> assumption
  · -- 满射
    intro x hx
    rw [Finset.mem_product, Finset.mem_product, Finset.mem_product] at hx
    obtain ⟨ha, hb, hc, hd⟩ := hx
    obtain ⟨a, b, c, d⟩ := x
    refine ⟨fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d,
      ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      fin_cases i <;> simp [ha, hb, hc, hd]
    · simp
  · -- 被求和项一致
    intro f _
    show F f = g (f 0, (f 1, (f 2, f 3)))
    simp only [g]
    congr 1
    funext i
    fin_cases i <;> simp

/-! ## 8. 第 9 步 (9a)：`Q ↦ Q/h` 把 `QSet` 上的和放大到 `K` 盒子 -/

/-- 第 9 步的 `K`：`|Q/h| ≤ K`（`Q ∈ QSet`，`h ≠ 0`）。 -/
def Kf (c d N : ℕ) : ℕ :=
  2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d) * N ^ (d - 1)

/-- **(9a) 计数桥接 I**：`Q ↦ Q/h` 是单射，像落在 `K` 盒中，故
`∑_{Q ∈ QSet⁴} [Q₁+…+Q₄ = 0] ≤ ∑_{m ∈ ([−K,K])⁴} [h₁m₁+…+h₄m₄ = 0]`。 -/
theorem sum_QBox_le_MBox {d : ℕ} (hd : 3 ≤ d) (c N M : ℕ) (hNM : M ≤ N)
    (a : ℕ → ℤ) (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) :
    ∀ (hh : Fin 4 → ℤ), (∀ i, hh i ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0) →
      (∑ Q ∈ Fintype.piFinset
          (fun i => QSet (fun n => polyEval a d n) M (hh i) (4 * 8 ^ (d - 3))),
          (if Q 0 + Q 1 + Q 2 + Q 3 = 0 then (1 : ℝ) else 0))
        ≤ ∑ m ∈ Fintype.piFinset
            (fun _ : Fin 4 => Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ)),
          (if hh 0 * m 0 + hh 1 * m 1 + hh 2 * m 2 + hh 3 * m 3 = 0 then (1 : ℝ) else 0) := by
  classical
  intro hh hH
  set QBox : Finset (Fin 4 → ℤ) :=
    Fintype.piFinset (fun i => QSet (fun n => polyEval a d n) M (hh i) (4 * 8 ^ (d - 3))) with hQBox
  set MBox : Finset (Fin 4 → ℤ) :=
    Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ))
    with hMBox
  set Φ : (Fin 4 → ℤ) → (Fin 4 → ℤ) := fun Q i => Q i / hh i with hΦ
  have hne : ∀ i, hh i ≠ 0 := fun i => (Finset.mem_erase.mp (hH i)).1
  have hNle : ∀ i, |hh i| ≤ (N : ℤ) := by
    intro i
    have h1 := (Finset.mem_erase.mp (hH i)).2
    rw [Finset.mem_Icc] at h1
    have h2 : (M : ℤ) ≤ (N : ℤ) := by exact_mod_cast hNM
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  have hmem : ∀ Q ∈ QBox, ∀ i, Q i ∈ QSet (fun n => polyEval a d n) M (hh i) (4 * 8 ^ (d - 3)) := by
    intro Q hQ i
    exact Fintype.mem_piFinset.mp hQ i
  have hdvd : ∀ Q ∈ QBox, ∀ i, hh i ∣ Q i := by
    intro Q hQ i
    exact QSet_dvd (hmem Q hQ i)
  have hval : ∀ Q ∈ QBox, ∀ i, hh i * (Φ Q i) = Q i := by
    intro Q hQ i
    have h := Int.ediv_mul_cancel (hdvd Q hQ i)
    calc hh i * (Φ Q i) = Q i / hh i * hh i := by rw [hΦ]; ring
      _ = Q i := h
  have hinj : Set.InjOn Φ (↑QBox : Set (Fin 4 → ℤ)) := by
    intro Q hQ Q' hQ' heq
    funext i
    have h1 : Q i / hh i = Q' i / hh i := by
      have hc := congrFun heq i
      simpa [hΦ] using hc
    calc Q i = hh i * (Q i / hh i) := (hval Q hQ i).symm
      _ = hh i * (Q' i / hh i) := by rw [h1]
      _ = Q' i := hval Q' hQ' i
  have himage : ∀ Q ∈ QBox, Φ Q ∈ MBox := by
    intro Q hQ
    rw [hMBox, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h := QSet_div_abs_le (a := a) (d := d) (c := c) (N := N) (M := M) (h := hh i)
      (s := 4 * 8 ^ (d - 3)) (Q := Q i) (by omega) ha (hNle i) hNM (hne i) (hmem Q hQ i)
    rw [abs_le] at h
    exact h
  have hsingle : ∀ Q ∈ QBox, (if Q 0 + Q 1 + Q 2 + Q 3 = 0 then (1 : ℝ) else 0)
      = (if hh 0 * (Φ Q 0) + hh 1 * (Φ Q 1) + hh 2 * (Φ Q 2) + hh 3 * (Φ Q 3) = 0
          then (1 : ℝ) else 0) := by
    intro Q hQ
    have e0 := hval Q hQ 0
    have e1 := hval Q hQ 1
    have e2 := hval Q hQ 2
    have e3 := hval Q hQ 3
    rw [← e0, ← e1, ← e2, ← e3]
  rw [Finset.sum_congr rfl hsingle]
  rw [← Finset.sum_image (f := fun m : Fin 4 → ℤ =>
      (if hh 0 * m 0 + hh 1 * m 1 + hh 2 * m 2 + hh 3 * m 3 = 0 then (1 : ℝ) else 0))
    (g := Φ) (s := QBox) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨Q, hQ, rfl⟩ := hm
    exact himage Q hQ
  · intro m _ _
    positivity

/-! ## 9. 第 9 步 (9b)：符号收缩 `|mᵢ| ≤ K` → `0 ≤ mᵢ ≤ K`（代价 `2⁴ = 16`） -/

/-- 符号函数（`z = 0` 时取 `1`）。 -/
def sgn (z : ℤ) : ℤ := if 0 ≤ z then 1 else -1

theorem sgn_mul_abs (z : ℤ) : sgn z * |z| = z := by
  rw [sgn]
  by_cases h : 0 ≤ z
  · rw [if_pos h, one_mul, abs_of_nonneg h]
  · rw [if_neg h, neg_one_mul, abs_of_neg (by omega)]
    ring

theorem sgn_ne_zero (z : ℤ) : sgn z ≠ 0 := by
  rw [sgn]; split <;> norm_num

theorem sgn_abs (z : ℤ) : |sgn z| = 1 := by
  rw [sgn]; split <;> norm_num

theorem sgn_mul_self (z : ℤ) : sgn z * sgn z = 1 := by
  rw [sgn]; split <;> norm_num

/-- 符号收缩映射 `(h, m) ↦ ((sgn(mᵢ)·hᵢ, |mᵢ|), sgn(mᵢ))`。 -/
noncomputable def sgnMap :
    (Fin 4 → ℤ) × (Fin 4 → ℤ) → ((Fin 4 → ℤ) × (Fin 4 → ℤ)) × (Fin 4 → ℤ) :=
  fun p => ((fun i => sgn (p.2 i) * p.1 i, fun i => |p.2 i|), fun i => sgn (p.2 i))

/-- 符号向量盒子 `{±1}⁴`。 -/
noncomputable def SymBox : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 4 => ({1, -1} : Finset ℤ))

theorem SymBox_card : SymBox.card = 16 := by
  rw [SymBox, Fintype.card_piFinset]
  simp

/-- **(9b) 符号收缩**：`|mᵢ| ≤ K` 的四元组计数不超过 `16·hmCount7 M K`。

映射 `sgnMap : (h, m) ↦ ((sgn(mᵢ)·hᵢ, |mᵢ|), sgn(mᵢ))` 把 `h` 的符号翻转与 `m` 一起，
故 `Σᵢ (sgn(mᵢ)hᵢ)·|mᵢ| = Σᵢ hᵢmᵢ`，方程保持不变；像落在 `hmCount7` 的盒子 `× SymBox`。 -/
theorem card_sym_shrink (M K : ℕ) :
    ((hBox7 M ×ˢ (Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(K : ℤ)) (K : ℤ)))).filter
        (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => ∑ i, p.1 i * p.2 i = 0)).card
      ≤ 16 * hmCount7 M K := by
  classical
  set Msign : Finset (Fin 4 → ℤ) :=
    Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(K : ℤ)) (K : ℤ)) with hMsign
  set A : Finset ((Fin 4 → ℤ) × (Fin 4 → ℤ)) :=
    (hBox7 M ×ˢ Msign).filter (fun p => ∑ i, p.1 i * p.2 i = 0) with hA
  set B : Finset ((Fin 4 → ℤ) × (Fin 4 → ℤ)) :=
    (hBox7 M ×ˢ mBox7 K).filter (fun p => ∑ i, p.1 i * p.2 i = 0) with hB
  have hBcard : B.card = hmCount7 M K := by
    rw [hB, hmCount7, show (hBox7 M).product (mBox7 K) = hBox7 M ×ˢ mBox7 K from rfl]
  have hmain : A.card ≤ (B ×ˢ SymBox).card := by
    refine Finset.card_le_card_of_injOn sgnMap ?_ ?_
    · -- 像落在 `B × SymBox`
      intro p hp
      rw [Finset.mem_coe, hA, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hp1, hp2⟩, hp0⟩ := hp
      rw [hBox7, Fintype.mem_piFinset] at hp1
      rw [hMsign, Fintype.mem_piFinset] at hp2
      rw [Finset.mem_coe, Finset.mem_product, hB, Finset.mem_filter, Finset.mem_product]
      simp only [sgnMap]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · -- `sgn m * h ∈ hBox7 M`
        rw [hBox7, Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_erase, Finset.mem_Icc]
        have h1 := hp1 i
        rw [Finset.mem_erase, Finset.mem_Icc] at h1
        have habs : |p.1 i| ≤ (M : ℤ) := abs_le.mpr h1.2
        have hmul : |sgn (p.2 i) * p.1 i| = |p.1 i| := by
          rw [abs_mul, sgn_abs, one_mul]
        have habs' : |sgn (p.2 i) * p.1 i| ≤ (M : ℤ) := by
          rw [hmul]; exact habs
        exact ⟨mul_ne_zero (sgn_ne_zero _) h1.1, (abs_le.mp habs').1, (abs_le.mp habs').2⟩
      · -- `|m| ∈ mBox7 K`
        rw [mBox7, Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_Icc]
        have h2 := hp2 i
        rw [Finset.mem_Icc] at h2
        have h2' : |p.2 i| ≤ (K : ℤ) := by
          rw [abs_le]; exact h2
        exact ⟨abs_nonneg _, h2'⟩
      · -- 和为零
        have hsum : (∑ i : Fin 4, (sgn (p.2 i) * p.1 i) * |p.2 i|)
            = ∑ i : Fin 4, p.1 i * p.2 i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          calc (sgn (p.2 i) * p.1 i) * |p.2 i| = p.1 i * (sgn (p.2 i) * |p.2 i|) := by ring
            _ = p.1 i * p.2 i := by rw [sgn_mul_abs]
        rw [hsum]
        exact hp0
      · -- `sgn m ∈ {±1}⁴`
        rw [SymBox, Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_insert, Finset.mem_singleton]
        by_cases h : 0 ≤ p.2 i
        · rw [sgn, if_pos h]; exact Or.inl rfl
        · rw [sgn, if_neg h]; exact Or.inr rfl
    · -- 单射
      intro p hp q hq heq
      simp only [sgnMap, Prod.mk.injEq] at heq
      obtain ⟨⟨h1, h2⟩, h3⟩ := heq
      have hm : p.2 = q.2 := by
        funext i
        have e1 := congrFun h3 i
        have e2 := congrFun h2 i
        calc p.2 i = sgn (p.2 i) * |p.2 i| := (sgn_mul_abs _).symm
          _ = sgn (q.2 i) * |q.2 i| := by rw [e1, e2]
          _ = q.2 i := sgn_mul_abs _
      have hh : p.1 = q.1 := by
        funext i
        have e1 := congrFun h1 i
        have e3 := congrFun h3 i
        have hfin : sgn (p.2 i) * p.1 i = sgn (p.2 i) * q.1 i := by rw [e1, ← e3]
        calc p.1 i = sgn (p.2 i) * (sgn (p.2 i) * p.1 i) := by
              rw [← mul_assoc, sgn_mul_self, one_mul]
          _ = sgn (p.2 i) * (sgn (p.2 i) * q.1 i) := by rw [hfin]
          _ = q.1 i := by rw [← mul_assoc, sgn_mul_self, one_mul]
      exact Prod.ext hh hm
  rw [Finset.card_product, hBcard, SymBox_card] at hmain
  linarith

/-! ## 10. 基例 `MeanValueBoundS 2`（自包含）

`WaringIndStep` 链与 `WaringInduction` 因 `e_sum` 命名冲突不能同时 import，
故此处逐字重述基例（依赖 `WaringQuadratic` 的二次形式计数）。 -/

/-- `polyEval a 2` 与 `qf (a 2) (a 1)` 差一个常数项。 -/
theorem polyEval_two_eq (a : ℕ → ℤ) (n : ℤ) :
    polyEval a 2 n = qf (a 2) (a 1) n + a 0 := by
  unfold polyEval qf
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, Nat.reduceAdd]
  ring

/-- `expSum` 与 `qSum` 差一个模 1 的因子。 -/
theorem expSum_polyEval_two (a : ℕ → ℤ) (N : ℕ) (α : ℝ) :
    expSum (fun n => polyEval a 2 n) N α
      = e ((a 0 : ℝ) * α) * qSum (a 2) (a 1) N α := by
  unfold expSum qSum
  rw [Fin.sum_univ_eq_sum_range
    (f := fun m : ℕ => e (((qf (a 2) (a 1) (m : ℤ) : ℤ) : ℝ) * α))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hbeta : (fun n => polyEval a 2 n) (n : ℤ) = polyEval a 2 (n : ℤ) := rfl
  rw [hbeta, polyEval_two_eq]
  have hsplit : (((qf (a 2) (a 1) (n : ℤ) + a 0 : ℤ)) : ℝ) * α
      = ((qf (a 2) (a 1) (n : ℤ) : ℤ) : ℝ) * α + ((a 0 : ℤ) : ℝ) * α := by
    push_cast
    ring
  rw [hsplit, e_add]
  ring

/-- **加强版基例的计数界**（求和长度 `M ≤ N`、系数尺度 `N`）。 -/
theorem qEqCount_le_MN (a b : ℤ) (ha : a ≠ 0) (c₁ c₂ N M : ℕ)
    (hM1 : 1 ≤ M) (hM : M ≤ N) (ha2 : a.natAbs ≤ c₂) (hb1 : b.natAbs ≤ c₁ * N) :
    qEqCount a b M ≤ 10000 * (4 * c₂ + 2 * c₁) * N ^ 6 := by
  classical
  -- 链：`qEqCount ≤ qHMCount ≤ Σ qQ² ≤ 10000·qK·M⁴`
  have hstep : (qEqCount a b M : ℚ) ≤ 10000 * (qK a b M : ℚ) * (M : ℚ) ^ 4 := by
    have h1 : (qEqCount a b M : ℚ) ≤ (qHMCount a b M : ℚ) := by
      exact_mod_cast qEqCount_le_qHMCount a b M
    have h2 : (qHMCount a b M : ℚ)
        ≤ ((∑ n ∈ Finset.Icc (-(qK a b M)) (qK a b M), qQ a b M (2 * M) n ^ 2 : ℕ) : ℚ) := by
      exact_mod_cast qHMCount_le_sum_sq a b M
    exact le_trans h1 (le_trans h2 (sum_qQ_sq_le_K a b ha M hM1))
  -- `qK ≤ (4c₂+2c₁)·N·M`
  have hKz : qK a b M ≤ ((4 * (c₂ : ℤ) + 2 * (c₁ : ℤ)) * (N : ℤ)) * (M : ℤ) := by
    have h1 : (a.natAbs : ℤ) ≤ (c₂ : ℤ) := by exact_mod_cast ha2
    have h2 : (b.natAbs : ℤ) ≤ (c₁ : ℤ) * (N : ℤ) := by
      have hcast : ((c₁ * N : ℕ) : ℤ) = (c₁ : ℤ) * (N : ℤ) := by push_cast; ring
      rw [← hcast]
      exact_mod_cast hb1
    have hM0 : (0 : ℤ) ≤ (M : ℤ) := by positivity
    have hMN : (M : ℤ) ≤ (N : ℤ) := by exact_mod_cast hM
    have hsq : (M : ℤ) ^ 2 ≤ (N : ℤ) * (M : ℤ) := by nlinarith [hM0, hMN]
    have hA : 4 * (M : ℤ) ^ 2 * (a.natAbs : ℤ) ≤ 4 * (N : ℤ) * (M : ℤ) * (c₂ : ℤ) := by
      nlinarith [hsq, h1, hM0, hMN]
    have hB : 2 * (M : ℤ) * (b.natAbs : ℤ) ≤ 2 * (N : ℤ) * (M : ℤ) * (c₁ : ℤ) := by
      nlinarith [h2, hM0]
    unfold qK
    calc 4 * (M : ℤ) ^ 2 * (a.natAbs : ℤ) + 2 * (M : ℤ) * (b.natAbs : ℤ)
        ≤ 4 * (N : ℤ) * (M : ℤ) * (c₂ : ℤ) + 2 * (N : ℤ) * (M : ℤ) * (c₁ : ℤ) := by
          linarith [hA, hB]
      _ = ((4 * (c₂ : ℤ) + 2 * (c₁ : ℤ)) * (N : ℤ)) * (M : ℤ) := by ring
  -- 合并（ℚ）
  have hKq : (qK a b M : ℚ)
      ≤ ((4 * (c₂ : ℚ) + 2 * (c₁ : ℚ)) * (N : ℚ)) * (M : ℚ) := by
    exact_mod_cast hKz
  have hMq1 : (1 : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM1
  have hMNq : (M : ℚ) ≤ (N : ℚ) := by exact_mod_cast hM
  have hfinal : (qEqCount a b M : ℚ) ≤ 10000 * (4 * (c₂ : ℚ) + 2 * (c₁ : ℚ)) * (N : ℚ) ^ 6 := by
    refine le_trans hstep ?_
    have h4 : (0 : ℚ) ≤ (M : ℚ) ^ 4 := by positivity
    have h16 : (10000 : ℚ) * (qK a b M : ℚ) * (M : ℚ) ^ 4
        ≤ 10000 * (((4 * (c₂ : ℚ) + 2 * (c₁ : ℚ)) * (N : ℚ)) * (M : ℚ)) * (M : ℚ) ^ 4 := by
      nlinarith [hKq, h4, sq_nonneg (M : ℚ)]
    refine le_trans h16 ?_
    have hM5 : (M : ℚ) ^ 5 ≤ (N : ℚ) ^ 5 := pow_le_pow_left₀ (by positivity) hMNq 5
    nlinarith [hM5, hMNq, pow_pos (by positivity : (0 : ℚ) < (M : ℚ)) 5]
  exact_mod_cast hfinal

/-- **加强版基例 `P(2)`**（`M ≤ N`）：`≤ R(c)·N⁶`。 -/
theorem meanValueBoundS_two : MeanValueBoundS 2 := by
  refine ⟨fun c : ℕ => 100000 * (((4 * c + 2 * c + 1 : ℕ) : ℝ) ^ 4), ?_, ?_⟩
  · intro c
    positivity
  · intro c N M hN hM1 hM a ha2nz ha
    have h2 : (a 2).natAbs ≤ c := by
      have h := ha 2 (le_refl 2)
      rw [pow_zero, mul_one] at h
      rw [Int.abs_eq_natAbs] at h
      exact_mod_cast h
    have h1 : (a 1).natAbs ≤ c * N := by
      have h := ha 1 (by norm_num)
      rw [pow_one] at h
      rw [Int.abs_eq_natAbs] at h
      exact_mod_cast h
    have h2' : (a 2 : ℤ) ≠ 0 := ha2nz
    have hfun : ∀ α : ℝ, ‖expSum (fun n => polyEval a 2 n) M α‖ ^ (8 ^ (2 - 1))
        = (Complex.normSq (qSum (a 2) (a 1) M α)) ^ 4 := by
      intro α
      rw [expSum_polyEval_two, norm_mul, norm_e, one_mul]
      rw [Complex.normSq_eq_norm_sq]
      norm_num
      ring
    simp_rw [hfun]
    rw [integral_normSq_pow_four_q]
    -- `qEqCount a b M ≤ 10⁴(4c+2c)N⁶`
    have hcnt := qEqCount_le_MN (a 2) (a 1) h2' c c N M hM1 hM h2 h1
    have hc : (qEqCount (a 2) (a 1) M : ℝ) ≤ 10000 * ((4 * c + 2 * c : ℕ) : ℝ) * (N : ℝ) ^ 6 := by
      exact_mod_cast hcnt
    refine le_trans hc ?_
    have hR : (10000 : ℝ) * ((4 * c + 2 * c : ℕ) : ℝ) * (N : ℝ) ^ 6
        ≤ 100000 * (((4 * c + 2 * c + 1 : ℕ) : ℝ) ^ 4) * (N : ℝ) ^ (8 ^ (2 - 1) - 2) := by
      have hexp : (8 ^ (2 - 1) - 2 : ℕ) = 6 := by norm_num
      rw [hexp]
      have h1 : (1 : ℝ) ≤ ((4 * c + 2 * c + 1 : ℕ) : ℝ) := by
        have : (1 : ℕ) ≤ 4 * c + 2 * c + 1 := by omega
        exact_mod_cast this
      have h2 : ((4 * c + 2 * c : ℕ) : ℝ) ≤ ((4 * c + 2 * c + 1 : ℕ) : ℝ) ^ 4 := by
        have hle : ((4 * c + 2 * c : ℕ) : ℝ) ≤ ((4 * c + 2 * c + 1 : ℕ) : ℝ) := by
          push_cast
          linarith only [h1]
        calc ((4 * c + 2 * c : ℕ) : ℝ) ≤ ((4 * c + 2 * c + 1 : ℕ) : ℝ) := hle
          _ = ((4 * c + 2 * c + 1 : ℕ) : ℝ) ^ 1 := by ring
          _ ≤ ((4 * c + 2 * c + 1 : ℕ) : ℝ) ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
      have hkey : (10000 : ℝ) * ((4 * c + 2 * c : ℕ) : ℝ)
          ≤ 100000 * (((4 * c + 2 * c + 1 : ℕ) : ℝ) ^ 4) := by
        nlinarith [h2, pow_nonneg (by linarith only [h1] : (0:ℝ) ≤ ((4 * c + 2 * c + 1 : ℕ) : ℝ)) 4]
      exact mul_le_mul_of_nonneg_right hkey (by positivity)
    exact hR

/-! ## 11. 第 9 步 (9c)：应用 Lemma 7 -/

/-- `Fintype.piFinset` 在 `Fin 4` 上展开成 4 层求和（`S` 可依赖坐标）。 -/
theorem sum_piFinset_fin4_dep {α : Type*} [DecidableEq α] (S : Fin 4 → Finset α)
    (F : (Fin 4 → α) → ℝ) :
    (∑ f ∈ Fintype.piFinset S, F f)
      = ∑ a ∈ S 0, ∑ b ∈ S 1, ∑ c ∈ S 2, ∑ d ∈ S 3,
          F (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d) := by
  classical
  let g : α × (α × (α × α)) → ℝ := fun y => F (fun i => if i = 0 then y.1
    else if i = 1 then y.2.1 else if i = 2 then y.2.2.1 else y.2.2.2)
  have hsplit : (∑ x ∈ S 0 ×ˢ (S 1 ×ˢ (S 2 ×ˢ S 3)), g x)
      = ∑ a ∈ S 0, ∑ b ∈ S 1, ∑ c ∈ S 2, ∑ d ∈ S 3,
          F (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d) := by
    have h1 : (∑ x ∈ S 0 ×ˢ (S 1 ×ˢ (S 2 ×ˢ S 3)), g x)
        = ∑ a ∈ S 0, ∑ b ∈ S 1, ∑ c ∈ S 2, ∑ d ∈ S 3, g (a, (b, (c, d))) := by
      simp only [Finset.sum_product]
    rw [h1]
  rw [← hsplit]
  refine Finset.sum_bij
    (fun (f : Fin 4 → α) (_ : f ∈ Fintype.piFinset S) => (f 0, (f 1, (f 2, f 3)))) ?_ ?_ ?_ ?_
  · intro f hf
    rw [Fintype.mem_piFinset] at hf
    rw [Finset.mem_product, Finset.mem_product, Finset.mem_product]
    exact ⟨hf 0, hf 1, hf 2, hf 3⟩
  · intro f _ f' _ heq
    have h1 : f 0 = f' 0 := by simpa using congrArg (fun z => z.1) heq
    have h2 : f 1 = f' 1 := by simpa using congrArg (fun z => z.2.1) heq
    have h3 : f 2 = f' 2 := by simpa using congrArg (fun z => z.2.2.1) heq
    have h4 : f 3 = f' 3 := by simpa using congrArg (fun z => z.2.2.2) heq
    funext i
    fin_cases i <;> assumption
  · intro x hx
    rw [Finset.mem_product, Finset.mem_product, Finset.mem_product] at hx
    obtain ⟨ha, hb, hc, hd⟩ := hx
    obtain ⟨a, b, c, d⟩ := x
    refine ⟨fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d,
      ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      fin_cases i <;> simp [ha, hb, hc, hd]
    · simp
  · intro f _
    show F f = g (f 0, (f 1, (f 2, f 3)))
    simp only [g]
    congr 1
    funext i
    fin_cases i <;> simp

/-- 由 `a d ≠ 0` 与系数界得 `1 ≤ c`。 -/
theorem one_le_c {a : ℕ → ℤ} {d c N : ℕ} (had : a d ≠ 0)
    (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) : 1 ≤ c := by
  have h := ha d le_rfl
  rw [Nat.sub_self, pow_zero, mul_one] at h
  have h1 : (1 : ℤ) ≤ |a d| := abs_pos.mpr had
  have h2 : (1 : ℤ) ≤ (c : ℤ) := le_trans h1 h
  exact_mod_cast h2

/-- `1 ≤ coeffConst c d`（`c ≥ 1`，`d ≥ 1`）。 -/
theorem coeffConst_pos {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) : 1 ≤ coeffConst c d := by
  unfold coeffConst
  have h0 : (0 : ℕ) ∈ Finset.range d := Finset.mem_range.mpr (by omega)
  have h00 : (0 : ℕ) ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  have hinner : (1 : ℕ) ≤ ∑ j ∈ Finset.range (d + 1), Nat.choose j 0 := by
    have hle : Nat.choose 0 0 ≤ ∑ j ∈ Finset.range (d + 1), Nat.choose j 0 :=
      Finset.single_le_sum (f := fun j => Nat.choose j 0) (fun i _ => by positivity) h00
    simpa using hle
  have houter : (1 : ℕ) ≤ ∑ r ∈ Finset.range d, ∑ j ∈ Finset.range (d + 1), Nat.choose j r := by
    have hle : (∑ j ∈ Finset.range (d + 1), Nat.choose j 0)
        ≤ ∑ r ∈ Finset.range d, ∑ j ∈ Finset.range (d + 1), Nat.choose j r :=
      Finset.single_le_sum (f := fun r => ∑ j ∈ Finset.range (d + 1), Nat.choose j r)
        (fun i _ => by positivity) h0
    exact le_trans hinner hle
  calc (1 : ℕ) = 1 * 1 := by ring
    _ ≤ c * ∑ r ∈ Finset.range d, ∑ j ∈ Finset.range (d + 1), Nat.choose j r :=
        Nat.mul_le_mul hc houter

/-- `M ≤ Kf c d N`（`1 ≤ c`、`d ≥ 3`、`N ≥ 1`、`M ≤ N`）。 -/
theorem le_Kf {c d N M : ℕ} (hd : 3 ≤ d) (hc : 1 ≤ c) (hN : 1 ≤ N) (hM : M ≤ N) :
    M ≤ Kf c d N := by
  have hC : 1 ≤ coeffConst c d := coeffConst_pos hc (by omega)
  have hCc : 1 ≤ (d + 1) * coeffConst c d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hNle : N ≤ N ^ (d - 1) := by
    have h1 : N ^ 1 ≤ N ^ (d - 1) := pow_le_pow_right₀ hN (by omega)
    simpa using h1
  have hcoef : 8 ≤ 2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d) := by
    have h1 : 4 ≤ 4 * 8 ^ (d - 3) := by have := one_le_s d; omega
    nlinarith
  unfold Kf
  calc M ≤ N := hM
    _ ≤ N ^ (d - 1) := hNle
    _ ≤ 8 * N ^ (d - 1) := by omega
    _ ≤ (2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d)) * N ^ (d - 1) :=
        Nat.mul_le_mul_right _ hcoef
    _ = 2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d) * N ^ (d - 1) := by ring

/-- `QSf a d M h = QSet (polyEval a d) M h (4·8^{d−3})`（缩短记号，控制 `whnf` 开销）。 -/
noncomputable def QSf (a : ℕ → ℤ) (d M : ℕ) (h : ℤ) : Finset ℤ :=
  QSet (fun n => polyEval a d n) M h (4 * 8 ^ (d - 3))

/- **未完成**：以下 (9c) 的证明触发 `QSet`/`Finset.pi` 的 `whnf` 复杂度爆炸
（`deterministic timeout`，即使 `maxHeartbeats = 2·10⁶`）。数学路线正确
（8 层和 → `hBox7 × QBox` → `K` 盒子 → `hmCount7` → Lemma 7），
工程上的出路是把 `QSet` 的定义换成不做 `Fintype.piFinset` 嵌套的表示，
或把 `sum_piFinset_fin4_dep` 的匹配改成 `Finset.sum_bij` 手写。
暂注释，见文件头「剩余缺口」。

set_option maxHeartbeats 2000000 in
/-- **(9c)**：满足 `Q₁+…+Q₄ = 0` 的 `(h,Q)` 四元组计数 ≤ `16·5250·(M·Kf)³`。 -/
theorem count_le {d : ℕ} (hd : 3 ≤ d) (c N M : ℕ) (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hNM : M ≤ N)
    (a : ℕ → ℤ) (had : a d ≠ 0)
    (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) :
    (∑ h1 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      ∑ h2 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      ∑ h3 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      ∑ h4 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      ∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
      ≤ (16 * (5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ) := by
  classical
  have hc : 1 ≤ c := one_le_c had ha
  have hMK : M ≤ Kf c d N := le_Kf hd hc hN hNM
  set S8 : Finset ℤ := (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0 with hS8
  -- 内层 4 层 `Q` 求和折叠成 `QBox`
  have hQfold : ∀ h : Fin 4 → ℤ,
      (∑ Q1 ∈ QSf a d M (h 0), ∑ Q2 ∈ QSf a d M (h 1),
        ∑ Q3 ∈ QSf a d M (h 2), ∑ Q4 ∈ QSf a d M (h 3),
        (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
        = ∑ Q ∈ Fintype.piFinset (fun i => QSf a d M (h i)),
            (if Q 0 + Q 1 + Q 2 + Q 3 = 0 then (1 : ℝ) else 0) := by
    intro h
    have key := sum_piFinset_fin4_dep (S := fun i => QSf a d M (h i))
      (F := fun Q : Fin 4 → ℤ => (if Q 0 + Q 1 + Q 2 + Q 3 = 0 then (1 : ℝ) else 0))
    simp only [Fin.isValue, ↓reduceIte] at key
    exact key.symm
  -- 第 1 步：8 层 → `hBox7 M` 上的 2 层
  have hstep1 : (∑ h1 ∈ S8, ∑ h2 ∈ S8, ∑ h3 ∈ S8, ∑ h4 ∈ S8,
      ∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
      = ∑ h ∈ hBox7 M, ∑ Q ∈ Fintype.piFinset (fun i => QSf a d M (h i)),
          (if Q 0 + Q 1 + Q 2 + Q 3 = 0 then (1 : ℝ) else 0) := by
    rw [show (∑ h1 ∈ S8, ∑ h2 ∈ S8, ∑ h3 ∈ S8, ∑ h4 ∈ S8,
        ∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
          (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
        = ∑ h1 ∈ S8, ∑ h2 ∈ S8, ∑ h3 ∈ S8, ∑ h4 ∈ S8,
          ∑ Q ∈ Fintype.piFinset (fun i => QSf a d M ((fun i => if i = 0 then h1
            else if i = 1 then h2 else if i = 2 then h3 else h4) i)),
            (if Q 0 + Q 1 + Q 2 + Q 3 = 0 then (1 : ℝ) else 0) from
      Finset.sum_congr rfl (fun h1 _ => Finset.sum_congr rfl (fun h2 _ =>
        Finset.sum_congr rfl (fun h3 _ => Finset.sum_congr rfl (fun h4 _ =>
          by simpa using hQfold _))))]
    rw [show hBox7 M = Fintype.piFinset (fun _ : Fin 4 => S8) from rfl]
    rw [← sum_piFinset_fin4 (S := S8) (F := fun h : Fin 4 → ℤ =>
      ∑ Q ∈ Fintype.piFinset (fun i => QSf a d M (h i)),
        (if Q 0 + Q 1 + Q 2 + Q 3 = 0 then (1 : ℝ) else 0))]
  rw [hstep1]
  -- 第 2 步（9a）：`QSet` → `K` 盒子
  have hstep2 : (∑ h ∈ hBox7 M, ∑ Q ∈ Fintype.piFinset (fun i => QSf a d M (h i)),
        (if Q 0 + Q 1 + Q 2 + Q 3 = 0 then (1 : ℝ) else 0))
      ≤ ∑ h ∈ hBox7 M,
          ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 =>
            Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ)),
          (if h 0 * m 0 + h 1 * m 1 + h 2 * m 2 + h 3 * m 3 = 0 then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum (fun h hh => ?_)
    exact sum_QBox_le_MBox hd c N M hNM a ha h (fun i => ?_)
    obtain ⟨h1, h2, h3⟩ := mem_hBox7.mp hh i
    exact Finset.mem_erase.mpr ⟨h1, Finset.mem_Icc.mpr ⟨h2, h3⟩⟩
  refine le_trans hstep2 ?_
  -- 第 3 步：把两层求和写成 `card`
  have hstep3 : (∑ h ∈ hBox7 M,
        ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 =>
          Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ)),
        (if h 0 * m 0 + h 1 * m 1 + h 2 * m 2 + h 3 * m 3 = 0 then (1 : ℝ) else 0))
      = (((hBox7 M ×ˢ Fintype.piFinset (fun _ : Fin 4 =>
            Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ))).filter
          (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => ∑ i : Fin 4, p.1 i * p.2 i = 0)).card : ℝ) := by
    rw [← Finset.sum_product]
    rw [← Finset.card_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    congr 1
    rw [Fin.sum_univ_four]
  rw [hstep3]
  -- 第 4 步（9b）+ 第 5 步（Lemma 7）
  have hA := card_sym_shrink M (Kf c d N)
  have hB := hmCount7_le' M (Kf c d N) hMK
  have hA' : (((hBox7 M ×ˢ Fintype.piFinset (fun _ : Fin 4 =>
        Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ))).filter
        (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => ∑ i : Fin 4, p.1 i * p.2 i = 0)).card : ℝ)
      ≤ 16 * (hmCount7 M (Kf c d N) : ℝ) := by
    have := hA
    exact_mod_cast this
  have hB' : (hmCount7 M (Kf c d N) : ℝ) ≤ ((5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hB
  have hfin : (16 * (hmCount7 M (Kf c d N) : ℝ) : ℝ)
      ≤ (16 * (5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ) := by
    have := hB'
    nlinarith
  exact le_trans hA' hfin
-/

set_option maxHeartbeats 800000 in
/-- 4 层 `QSet` 求和放大到 `K` 盒子（逐层 `Q ↦ Q/h`，**不展开 `QSet`/`Finset.pi`**）。 -/
theorem sum_four_Q_le_MBox {d : ℕ} (hd : 3 ≤ d) (c N M : ℕ) (hNM : M ≤ N)
    (a : ℕ → ℤ) (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j))
    {h1 h2 h3 h4 : ℤ} (hb1 : |h1| ≤ (M : ℤ)) (hb2 : |h2| ≤ (M : ℤ))
    (hb3 : |h3| ≤ (M : ℤ)) (hb4 : |h4| ≤ (M : ℤ))
    (hn1 : h1 ≠ 0) (hn2 : h2 ≠ 0) (hn3 : h3 ≠ 0) (hn4 : h4 ≠ 0) :
    (∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
      ≤ ∑ m1 ∈ Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ),
          ∑ m2 ∈ Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ),
          ∑ m3 ∈ Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ),
          ∑ m4 ∈ Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ),
          (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * m4 = 0 then (1 : ℝ) else 0) := by
  classical
  have hd1 : 1 ≤ d := by omega
  set KB : Finset ℤ := Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ) with hKB
  -- 除法还原：`h * (Q / h) = Q`（`Q ∈ QSet` 时 `h ∣ Q`）
  have hdiv : ∀ (h Q : ℤ), Q ∈ QSf a d M h → h * (Q / h) = Q := by
    intro h Q hQ
    have hd' := QSet_dvd hQ
    calc h * (Q / h) = Q / h * h := by ring
      _ = Q := Int.ediv_mul_cancel hd'
  -- `Q ↦ Q/h` 在 `QSet` 上单射
  have hinj : ∀ (h : ℤ), h ≠ 0 → Set.InjOn (fun Q : ℤ => Q / h) (↑(QSf a d M h) : Set ℤ) := by
    intro h _ Q hQ Q' hQ' heq
    simp only at heq
    calc Q = h * (Q / h) := (hdiv h Q hQ).symm
      _ = h * (Q' / h) := by rw [heq]
      _ = Q' := hdiv h Q' hQ'
  -- 像落在 `K` 盒子
  have hmem : ∀ (h : ℤ), h ≠ 0 → |h| ≤ (M : ℤ) → ∀ Q ∈ QSf a d M h, Q / h ∈ KB := by
    intro h hh0 hhb Q hQ
    rw [hKB, Finset.mem_Icc]
    have hNabs : |h| ≤ (N : ℤ) := le_trans hhb (by exact_mod_cast hNM)
    have hb := QSet_div_abs_le (a := a) (d := d) (c := c) (N := N) (M := M) (h := h)
      (s := 4 * 8 ^ (d - 3)) (Q := Q) hd1 ha hNabs hNM hh0 hQ
    rw [abs_le] at hb
    exact hb
  -- 单层：`∑_{Q ∈ QSet h} F (Q/h) ≤ ∑_{m ∈ KB} F m`
  have step : ∀ (h : ℤ), h ≠ 0 → |h| ≤ (M : ℤ) → ∀ (F : ℤ → ℝ), (∀ Q, 0 ≤ F Q) →
      (∑ Q ∈ QSf a d M h, F (Q / h)) ≤ ∑ m ∈ KB, F m := by
    intro h hh0 hhb F hF
    rw [← Finset.sum_image (f := F) (g := fun Q : ℤ => Q / h) (s := QSf a d M h) (hinj h hh0)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨Q, hQ, rfl⟩ := hm
      exact hmem h hh0 hhb Q hQ
    · intro m _ _; exact hF m
  calc (∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
      = (∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if h1 * (Q1 / h1) + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl (fun Q1 hQ1 => Finset.sum_congr rfl (fun Q2 _ =>
          Finset.sum_congr rfl (fun Q3 _ => Finset.sum_congr rfl (fun Q4 _ => ?_))))
        rw [hdiv h1 Q1 hQ1]
    _ = (∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if h1 * (Q1 / h1) + h2 * (Q2 / h2) + Q3 + Q4 = 0 then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl (fun Q1 _ => Finset.sum_congr rfl (fun Q2 hQ2 =>
          Finset.sum_congr rfl (fun Q3 _ => Finset.sum_congr rfl (fun Q4 _ => ?_))))
        rw [hdiv h2 Q2 hQ2]
    _ = (∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if h1 * (Q1 / h1) + h2 * (Q2 / h2) + h3 * (Q3 / h3) + Q4 = 0 then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl (fun Q1 _ => Finset.sum_congr rfl (fun Q2 _ =>
          Finset.sum_congr rfl (fun Q3 hQ3 => Finset.sum_congr rfl (fun Q4 _ => ?_))))
        rw [hdiv h3 Q3 hQ3]
    _ = (∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if h1 * (Q1 / h1) + h2 * (Q2 / h2) + h3 * (Q3 / h3) + h4 * (Q4 / h4) = 0
          then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl (fun Q1 _ => Finset.sum_congr rfl (fun Q2 _ =>
          Finset.sum_congr rfl (fun Q3 _ => Finset.sum_congr rfl (fun Q4 hQ4 => ?_))))
        rw [hdiv h4 Q4 hQ4]
    _ ≤ (∑ m1 ∈ KB, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if h1 * m1 + h2 * (Q2 / h2) + h3 * (Q3 / h3) + h4 * (Q4 / h4) = 0
          then (1 : ℝ) else 0)) :=
        step h1 hn1 hb1 (fun m1 => ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3,
          ∑ Q4 ∈ QSf a d M h4,
          (if h1 * m1 + h2 * (Q2 / h2) + h3 * (Q3 / h3) + h4 * (Q4 / h4) = 0
            then (1 : ℝ) else 0)) (fun _ => by positivity)
    _ ≤ (∑ m1 ∈ KB, ∑ m2 ∈ KB, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if h1 * m1 + h2 * m2 + h3 * (Q3 / h3) + h4 * (Q4 / h4) = 0
          then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum (fun m1 _ => ?_)
        exact step h2 hn2 hb2 (fun m2 => ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
          (if h1 * m1 + h2 * m2 + h3 * (Q3 / h3) + h4 * (Q4 / h4) = 0
            then (1 : ℝ) else 0)) (fun _ => by positivity)
    _ ≤ (∑ m1 ∈ KB, ∑ m2 ∈ KB, ∑ m3 ∈ KB, ∑ Q4 ∈ QSf a d M h4,
        (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * (Q4 / h4) = 0
          then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum (fun m1 _ => Finset.sum_le_sum (fun m2 _ => ?_))
        exact step h3 hn3 hb3 (fun m3 => ∑ Q4 ∈ QSf a d M h4,
          (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * (Q4 / h4) = 0
            then (1 : ℝ) else 0)) (fun _ => by positivity)
    _ ≤ (∑ m1 ∈ KB, ∑ m2 ∈ KB, ∑ m3 ∈ KB, ∑ m4 ∈ KB,
        (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * m4 = 0 then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum (fun m1 _ => Finset.sum_le_sum (fun m2 _ =>
          Finset.sum_le_sum (fun m3 _ => ?_)))
        exact step h4 hn4 hb4 (fun m4 => (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * m4 = 0
          then (1 : ℝ) else 0)) (fun _ => by positivity)

set_option maxHeartbeats 1600000 in
/-- **(9c)**：满足 `Q₁+…+Q₄ = 0` 的 `(h,Q)` 四元组计数 ≤ `16·5250·(M·Kf)³`。 -/
theorem count_le {d : ℕ} (hd : 3 ≤ d) (c N M : ℕ) (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hNM : M ≤ N)
    (a : ℕ → ℤ) (had : a d ≠ 0)
    (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) :
    (∑ h1 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      ∑ h2 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      ∑ h3 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      ∑ h4 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
      ∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
        (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
      ≤ (16 * (5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ) := by
  classical
  have hc : 1 ≤ c := one_le_c had ha
  have hMK : M ≤ Kf c d N := le_Kf hd hc hN hNM
  set S8 : Finset ℤ := (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0 with hS8
  set KB : Finset ℤ := Finset.Icc (-((Kf c d N : ℕ) : ℤ)) ((Kf c d N : ℕ) : ℤ) with hKB
  -- 第 1 步：4 层 `Q` → 4 层 `m`（逐层 `Q ↦ Q/h`，见 `sum_four_Q_le_MBox`）
  have hstep1 : (∑ h1 ∈ S8, ∑ h2 ∈ S8, ∑ h3 ∈ S8, ∑ h4 ∈ S8,
        ∑ Q1 ∈ QSf a d M h1, ∑ Q2 ∈ QSf a d M h2, ∑ Q3 ∈ QSf a d M h3, ∑ Q4 ∈ QSf a d M h4,
          (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
      ≤ ∑ h1 ∈ S8, ∑ h2 ∈ S8, ∑ h3 ∈ S8, ∑ h4 ∈ S8,
          ∑ m1 ∈ KB, ∑ m2 ∈ KB, ∑ m3 ∈ KB, ∑ m4 ∈ KB,
          (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * m4 = 0 then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum (fun h1 hh1 => Finset.sum_le_sum (fun h2 hh2 =>
      Finset.sum_le_sum (fun h3 hh3 => Finset.sum_le_sum (fun h4 hh4 => ?_))))
    obtain ⟨hn1, hI1⟩ := Finset.mem_erase.mp hh1
    obtain ⟨hlo1, hhi1⟩ := Finset.mem_Icc.mp hI1
    obtain ⟨hn2, hI2⟩ := Finset.mem_erase.mp hh2
    obtain ⟨hlo2, hhi2⟩ := Finset.mem_Icc.mp hI2
    obtain ⟨hn3, hI3⟩ := Finset.mem_erase.mp hh3
    obtain ⟨hlo3, hhi3⟩ := Finset.mem_Icc.mp hI3
    obtain ⟨hn4, hI4⟩ := Finset.mem_erase.mp hh4
    obtain ⟨hlo4, hhi4⟩ := Finset.mem_Icc.mp hI4
    have hb1 : |h1| ≤ (M : ℤ) := abs_le.mpr ⟨hlo1, hhi1⟩
    have hb2 : |h2| ≤ (M : ℤ) := abs_le.mpr ⟨hlo2, hhi2⟩
    have hb3 : |h3| ≤ (M : ℤ) := abs_le.mpr ⟨hlo3, hhi3⟩
    have hb4 : |h4| ≤ (M : ℤ) := abs_le.mpr ⟨hlo4, hhi4⟩
    exact sum_four_Q_le_MBox hd c N M hNM a ha hb1 hb2 hb3 hb4 hn1 hn2 hn3 hn4
  refine le_trans hstep1 ?_
  -- 第 2 步：折叠成 `hBox7 M × (KB)⁴` 上的两层求和
  have hstep2 : (∑ h1 ∈ S8, ∑ h2 ∈ S8, ∑ h3 ∈ S8, ∑ h4 ∈ S8,
        ∑ m1 ∈ KB, ∑ m2 ∈ KB, ∑ m3 ∈ KB, ∑ m4 ∈ KB,
          (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * m4 = 0 then (1 : ℝ) else 0))
      = ∑ h ∈ hBox7 M, ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 => KB),
          (if h 0 * m 0 + h 1 * m 1 + h 2 * m 2 + h 3 * m 3 = 0 then (1 : ℝ) else 0) := by
    rw [show (∑ h1 ∈ S8, ∑ h2 ∈ S8, ∑ h3 ∈ S8, ∑ h4 ∈ S8,
        ∑ m1 ∈ KB, ∑ m2 ∈ KB, ∑ m3 ∈ KB, ∑ m4 ∈ KB,
          (if h1 * m1 + h2 * m2 + h3 * m3 + h4 * m4 = 0 then (1 : ℝ) else 0))
        = ∑ h1 ∈ S8, ∑ h2 ∈ S8, ∑ h3 ∈ S8, ∑ h4 ∈ S8,
          ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 => KB),
            (if h1 * (m 0) + h2 * (m 1) + h3 * (m 2) + h4 * (m 3) = 0 then (1 : ℝ) else 0) from by
      refine Finset.sum_congr rfl (fun h1 _ => Finset.sum_congr rfl (fun h2 _ =>
        Finset.sum_congr rfl (fun h3 _ => Finset.sum_congr rfl (fun h4 _ => ?_))))
      have key := sum_piFinset_fin4 (S := KB) (F := fun m : Fin 4 → ℤ =>
        (if h1 * (m 0) + h2 * (m 1) + h3 * (m 2) + h4 * (m 3) = 0 then (1 : ℝ) else 0))
      simp only [Fin.isValue, ↓reduceIte] at key
      exact key.symm]
    rw [show hBox7 M = Fintype.piFinset (fun _ : Fin 4 => S8) from rfl]
    have key2 := sum_piFinset_fin4 (S := S8) (F := fun h : Fin 4 → ℤ =>
      ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 => KB),
        (if h 0 * m 0 + h 1 * m 1 + h 2 * m 2 + h 3 * m 3 = 0 then (1 : ℝ) else 0))
    simp only [Fin.isValue, ↓reduceIte] at key2
    exact key2.symm
  rw [hstep2]
  -- 第 3 步：两层求和 → `card`（先在 `ℕ` 上做，再提升到 `ℝ`）
  have hstep3nat : (∑ h ∈ hBox7 M, ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 => KB),
        (if h 0 * m 0 + h 1 * m 1 + h 2 * m 2 + h 3 * m 3 = 0 then (1 : ℕ) else 0))
      = ((hBox7 M ×ˢ Fintype.piFinset (fun _ : Fin 4 => KB)).filter
          (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => ∑ i : Fin 4, p.1 i * p.2 i = 0)).card := by
    rw [show (∑ h ∈ hBox7 M, ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 => KB),
        (if h 0 * m 0 + h 1 * m 1 + h 2 * m 2 + h 3 * m 3 = 0 then (1 : ℕ) else 0))
        = ∑ h ∈ hBox7 M, ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 => KB),
          (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
            (if p.1 0 * p.2 0 + p.1 1 * p.2 1 + p.1 2 * p.2 2 + p.1 3 * p.2 3 = 0
              then (1 : ℕ) else 0)) (h, m) from rfl]
    rw [← Finset.sum_product (s := hBox7 M) (t := Fintype.piFinset (fun _ : Fin 4 => KB))
      (f := fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
        (if p.1 0 * p.2 0 + p.1 1 * p.2 1 + p.1 2 * p.2 2 + p.1 3 * p.2 3 = 0
          then (1 : ℕ) else 0))]
    have hcf := Finset.card_filter
      (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => ∑ i : Fin 4, p.1 i * p.2 i = 0)
      (hBox7 M ×ˢ Fintype.piFinset (fun _ : Fin 4 => KB))
    have h1 : (∑ x ∈ hBox7 M ×ˢ Fintype.piFinset (fun _ : Fin 4 => KB),
        (if x.1 0 * x.2 0 + x.1 1 * x.2 1 + x.1 2 * x.2 2 + x.1 3 * x.2 3 = 0
          then (1 : ℕ) else 0))
        = ∑ x ∈ hBox7 M ×ˢ Fintype.piFinset (fun _ : Fin 4 => KB),
          (if ∑ i : Fin 4, x.1 i * x.2 i = 0 then (1 : ℕ) else 0) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      congr 1
      rw [Fin.sum_univ_four]
    rw [h1, ← hcf]
  have hstep3 : (∑ h ∈ hBox7 M, ∑ m ∈ Fintype.piFinset (fun _ : Fin 4 => KB),
        (if h 0 * m 0 + h 1 * m 1 + h 2 * m 2 + h 3 * m 3 = 0 then (1 : ℝ) else 0))
      = (((hBox7 M ×ˢ Fintype.piFinset (fun _ : Fin 4 => KB)).filter
          (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => ∑ i : Fin 4, p.1 i * p.2 i = 0)).card : ℝ) := by
    have h := hstep3nat
    exact_mod_cast h
  rw [hstep3]
  -- 第 4 步（9b）+ 第 5 步（Lemma 7）
  have hA : (((hBox7 M ×ˢ Fintype.piFinset (fun _ : Fin 4 => KB)).filter
        (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => ∑ i : Fin 4, p.1 i * p.2 i = 0)).card : ℝ)
      ≤ 16 * (hmCount7 M (Kf c d N) : ℝ) := by
    rw [hKB]
    have h := card_sym_shrink M (Kf c d N)
    exact_mod_cast h
  have hB : (hmCount7 M (Kf c d N) : ℝ) ≤ ((5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hmCount7_le' M (Kf c d N) hMK
  have hfin : (16 * (hmCount7 M (Kf c d N) : ℝ) : ℝ)
      ≤ (16 * (5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ) := by
    nlinarith
  exact le_trans hA hfin

/-! ## 12. 第 10 步：常数账与组装 -/

/-- 归纳步的显式常数 `R_d(c)`（只依赖 `c`，不依赖 `N`/`M`）。 -/
noncomputable def Rd (d : ℕ) (R₀ : ℕ → ℝ) (c : ℕ) : ℝ :=
  let m := 8 ^ (d - 2)
  let Ck : ℝ := ((2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d) : ℕ) : ℝ)
  let Rmax : ℝ := max (R₀ (coeffConst c d)) 1
  2 ^ (4 * (m - 1)) * 8 *
    (2 ^ (4 * m) + 2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)

/- **未完成（第 10 步组装）**：`meanValueBoundS_succ` 的算术证明。
数学上一切就绪（`integral_bound` + `four_sum_le_count` + `count_le` + `Rd`），
剩余是约 150 行的纯算术：把
`2^{4(m−1)}·8·((M+1)^{4m} + (2M)^{4(m−1)}·Rmax⁴·N^{4(m−(d−1))}·16·5250·Ck³·N^{3d})`
整理成 `Rd·N^{8m−d}`。所需的工具性事实已全部写在这个块里（`hKf`、`hexp1`、
`hNfin`、`hexpand` 等），剩余是 `positivity`/`gcongr` 的局部修正
（`Ck`/`Rmax` 非负性需显式 `have`，`pow_le_pow_right₀` 对 `2^(d−1) ≤ 8^(d−2)`
需先 `8 = 2^3`）。

set_option maxHeartbeats 2000000 in
/-- **加强版归纳步**：`MeanValueBoundS (d−1) → MeanValueBoundS d`（`d ≥ 3`）。 -/
theorem meanValueBoundS_succ {d : ℕ} (hd : 3 ≤ d) (h : MeanValueBoundS (d - 1)) :
    MeanValueBoundS d := by
  obtain ⟨R₀, hR₀pos, hR₀b⟩ := h
  have hMV : MVSBound (d - 1) R₀ := hR₀b
  refine ⟨fun c => Rd d R₀ c, ?hpos, ?hbound⟩
  · -- `R_d(c) > 0`
    intro c
    have h1 : (0 : ℝ) < max (R₀ (coeffConst c d)) 1 :=
      lt_of_lt_of_le (hR₀pos _) (le_max_left _ _)
    simp only [Rd]
    positivity
  · -- 主不等式
    intro c N M hN hM1 hMN a had ha
    have hc : 1 ≤ c := one_le_c had ha
    have hMK : M ≤ Kf c d N := le_Kf hd hc hN hMN
    set m : ℕ := 8 ^ (d - 2) with hm
    set Ck : ℝ := ((2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d) : ℕ) : ℝ) with hCk
    set Rmax : ℝ := max (R₀ (coeffConst c d)) 1 with hRmax
    have hRmax0 : 0 < Rmax := lt_of_lt_of_le (hR₀pos _) (le_max_left _ _)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hMN' : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_trans zero_le_one hN1
    -- `Kf = Ck * N^{d−1}`
    have hKf : ((Kf c d N : ℕ) : ℝ) = Ck * (N : ℝ) ^ (d - 1) := by
      simp only [hCk, Kf]
      push_cast
      ring
    -- 四重和的界
    have hcount := count_le hd c N M hN hM1 hMN a had ha
    have hcount' : (∑ h1 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h2 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h3 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h4 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ Q1 ∈ QSet (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)),
        ∑ Q2 ∈ QSet (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)),
        ∑ Q3 ∈ QSet (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)),
        ∑ Q4 ∈ QSet (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)),
          (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
        ≤ (16 * (5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ) := by
      simpa only [QSf] using hcount
    have hfour := four_sum_le_count hd (R₀ := R₀) hMV c N M hN hM1 hMN a had ha
    -- `∫ (Σ‖b_h‖^m)^4 ≤ Rmax^4·N^{4(m−(d−1))}·(16·5250·Ck^3·N^{3d})`
    have hint4 : (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
        ≤ Rmax ^ 4 * (N : ℝ) ^ (4 * (m - (d - 1)))
          * (16 * 5250 * Ck ^ 3 * (N : ℝ) ^ (3 * d)) := by
      refine le_trans hfour ?_
      have hR4 : (0 : ℝ) ≤ (max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (m - (d - 1))) ^ 4 := by
        positivity
      have hstep : (max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (m - (d - 1))) ^ 4
          * (16 * (5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ)
          ≤ Rmax ^ 4 * (N : ℝ) ^ (4 * (m - (d - 1)))
            * (16 * 5250 * Ck ^ 3 * (N : ℝ) ^ (3 * d)) := by
        have h1 : (max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (m - (d - 1))) ^ 4
            = Rmax ^ 4 * (N : ℝ) ^ (4 * (m - (d - 1))) := by
          rw [hRmax, mul_pow, ← pow_mul, Nat.mul_comm]
        have hM3 : (M : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hMN' 3
        have hKf3 : ((Kf c d N : ℕ) : ℝ) ^ 3 = Ck ^ 3 * (N : ℝ) ^ (3 * (d - 1)) := by
          rw [hKf, mul_pow, ← pow_mul, Nat.mul_comm]
        have hKeq : (3 : ℕ) * (d - 1) + 3 = 3 * d := by omega
        have hcast : ((5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ)
            = 5250 * (M : ℝ) ^ 3 * ((Kf c d N : ℕ) : ℝ) ^ 3 := by push_cast; ring
        have hNexp : (N : ℝ) ^ (3 * (d - 1)) * (N : ℝ) ^ 3 = (N : ℝ) ^ (3 * d) := by
          rw [← pow_add, hKeq]
        have hN3 : (0 : ℝ) ≤ (N : ℝ) ^ (3 * (d - 1)) := by positivity
        have h2 : (16 * (5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ)
            ≤ 16 * 5250 * Ck ^ 3 * (N : ℝ) ^ (3 * d) := by
          rw [hcast, hKf3]
          have hprod : (M : ℝ) ^ 3 * ((N : ℝ) ^ (3 * (d - 1)))
              ≤ (N : ℝ) ^ 3 * ((N : ℝ) ^ (3 * (d - 1))) :=
            mul_le_mul_of_nonneg_right hM3 hN3
          calc 16 * (5250 * (M : ℝ) ^ 3 * (Ck ^ 3 * (N : ℝ) ^ (3 * (d - 1))))
              = 16 * 5250 * Ck ^ 3 * ((M : ℝ) ^ 3 * ((N : ℝ) ^ (3 * (d - 1)))) := by ring
            _ ≤ 16 * 5250 * Ck ^ 3 * ((N : ℝ) ^ 3 * ((N : ℝ) ^ (3 * (d - 1)))) :=
                mul_le_mul_of_nonneg_left hprod (by positivity)
            _ = 16 * 5250 * Ck ^ 3 * (N : ℝ) ^ (3 * d) := by
                rw [mul_comm ((N:ℝ)^3) ((N:ℝ)^(3*(d-1))), hNexp]
        rw [h1]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      exact le_trans (mul_le_mul_of_nonneg_left hcount' hR4) hstep
    -- 合并到 `N^{8m−d}`
    have hmge : d - 1 ≤ m := by
      rw [hm]
      have h1 : d - 1 < 2 ^ (d - 1) := Nat.lt_two_pow_self _
      have h2 : 2 ^ (d - 1) ≤ 8 ^ (d - 2) := by
        apply pow_le_pow_right₀ (by norm_num)
        omega
      omega
    have hexp1 : 4 * (m - 1) + 4 * (m - (d - 1)) + 3 * d = 8 * m - d := by omega
    have hsum : ((M : ℝ) + 1) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
        ≤ (2 ^ (4 * m) + 2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
          * (N : ℝ) ^ (8 * m - d) := by
      have hM1 : (M : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
      have hp1 : ((M : ℝ) + 1) ^ (4 * m) ≤ 2 ^ (4 * m) * (N : ℝ) ^ (4 * m) := by
        calc ((M : ℝ) + 1) ^ (4 * m) ≤ (2 * (N : ℝ)) ^ (4 * m) :=
              pow_le_pow_left₀ (by positivity) hM1 _
          _ = 2 ^ (4 * m) * (N : ℝ) ^ (4 * m) := by rw [mul_pow]
      have hp2 : (2 * (M : ℝ)) ^ (4 * (m - 1)) ≤ 2 ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - 1)) := by
        have h : 2 * (M : ℝ) ≤ 2 * (N : ℝ) := by linarith
        calc (2 * (M : ℝ)) ^ (4 * (m - 1)) ≤ (2 * (N : ℝ)) ^ (4 * (m - 1)) :=
              pow_le_pow_left₀ (by positivity) h _
          _ = 2 ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - 1)) := by rw [mul_pow]
      have hM4 : (2 * (M : ℝ)) ^ (4 * (m - 1))
          * (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
          ≤ (2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
            * ((N : ℝ) ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - (d - 1)))
              * (N : ℝ) ^ (3 * d)) := by
        refine le_trans (mul_le_mul hp2 hint4 (by positivity) (by positivity)) ?_
        have hz : (0 : ℝ) ≤ 2 ^ (4 * (m - 1)) := by positivity
        calc 2 ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - 1))
              * (Rmax ^ 4 * (N : ℝ) ^ (4 * (m - (d - 1)))
                * (16 * 5250 * Ck ^ 3 * (N : ℝ) ^ (3 * d)))
            = (2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
              * ((N : ℝ) ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - (d - 1)))
                * (N : ℝ) ^ (3 * d)) := by ring
      have hNfin : (N : ℝ) ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - (d - 1)))
            * (N : ℝ) ^ (3 * d) = (N : ℝ) ^ (8 * m - d) := by
        rw [← pow_add, ← pow_add, hexp1]
      rw [hNfin] at hM4
      have heq1 : 2 ^ (4 * m) * (N : ℝ) ^ (4 * m)
          ≤ 2 ^ (4 * m) * (N : ℝ) ^ (8 * m - d) := by
        have hle : 4 * m ≤ 8 * m - d := by omega
        have := pow_le_pow_right₀ hN1 hle
        exact mul_le_mul_of_nonneg_left this (by positivity)
      have hexpand : (2 ^ (4 * m) + 2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
            * (N : ℝ) ^ (8 * m - d)
          = 2 ^ (4 * m) * (N : ℝ) ^ (8 * m - d)
            + (2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3) * (N : ℝ) ^ (8 * m - d) := by
        ring
      rw [hexpand]
      linarith
    -- 组装
    have hmain : (∫ α in (0 : ℝ)..1, ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
        ≤ 2 ^ (4 * (m - 1)) * 8 *
            ((2 ^ (4 * m) + 2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
              * (N : ℝ) ^ (8 * m - d)) := by
      refine le_trans (integral_bound hd a hM1) ?_
      have hbase : ((M : ℝ) + 1) ^ (4 * 8 ^ (d - 2))
            + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
              * (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
          ≤ (2 ^ (4 * m) + 2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
            * (N : ℝ) ^ (8 * m - d) := by
        rw [hm]
        exact hsum
      exact mul_le_mul_of_nonneg_left hbase (by positivity)
    refine le_trans hmain (le_of_eq ?_)
    rw [show 8 ^ (d - 1) = 8 * m from by rw [hm]; rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]; ring]
    simp only [Rd]
    rw [hm]
    ring
-/

set_option maxHeartbeats 2000000 in
/-- **加强版归纳步**：`MeanValueBoundS (d−1) → MeanValueBoundS d`（`d ≥ 3`）。 -/
theorem meanValueBoundS_succ {d : ℕ} (hd : 3 ≤ d) (h : MeanValueBoundS (d - 1)) :
    MeanValueBoundS d := by
  obtain ⟨R₀, hR₀pos, hR₀b⟩ := h
  have hMV : MVSBound (d - 1) R₀ := hR₀b
  refine ⟨fun c => Rd d R₀ c, ?hpos, ?hbound⟩
  · -- `R_d(c) > 0`
    intro c
    have h1 : (0 : ℝ) < max (R₀ (coeffConst c d)) 1 :=
      lt_of_lt_of_le (hR₀pos _) (le_max_left _ _)
    have h2 : (0 : ℝ) ≤ ((2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d) : ℕ) : ℝ) := by
      positivity
    show (0 : ℝ) < Rd d R₀ c
    simp only [Rd]
    apply mul_pos
    · exact mul_pos (by positivity) (by norm_num)
    · apply add_pos_of_pos_of_nonneg (by positivity)
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
        (pow_nonneg (le_of_lt h1) 4)) (by norm_num)) (by norm_num)) (pow_nonneg h2 3)
  · -- 主不等式
    intro c N M hN hM1 hMN a had ha
    have hc : 1 ≤ c := one_le_c had ha
    have hMK : M ≤ Kf c d N := le_Kf hd hc hN hMN
    set m : ℕ := 8 ^ (d - 2) with hm
    set Ck : ℝ := ((2 * (4 * 8 ^ (d - 3)) * ((d + 1) * coeffConst c d) : ℕ) : ℝ) with hCk
    set Rmax : ℝ := max (R₀ (coeffConst c d)) 1 with hRmax
    have hRmax0 : 0 < Rmax := by
      rw [hRmax]; exact lt_of_lt_of_le (hR₀pos _) (le_max_left _ _)
    have hmax0 : (0 : ℝ) ≤ max (R₀ (coeffConst c d)) 1 := by
      rw [← hRmax]; exact le_of_lt hRmax0
    have hCk0 : 0 ≤ Ck := by rw [hCk]; positivity
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hMN' : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
    have hm1 : 1 ≤ m := by rw [hm]; exact Nat.one_le_pow _ _ (by norm_num)
    -- `Kf = Ck · N^{d−1}`
    have hKf : ((Kf c d N : ℕ) : ℝ) = Ck * (N : ℝ) ^ (d - 1) := by
      rw [hCk]; simp only [Kf]; push_cast; ring
    -- 指数恒等式
    have hmge : d - 1 ≤ m := by
      have h1 : d - 1 < 2 ^ (d - 1) := Nat.lt_two_pow_self
      have h2 : 2 ^ (d - 1) ≤ 8 ^ (d - 2) := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      rw [hm]; omega
    have hexp1 : 4 * (m - 1) + 4 * (m - (d - 1)) + 3 * d = 8 * m - d := by omega
    have h4md : 4 * m ≤ 8 * m - d := by omega
    -- 计数界（9c）
    have hcount := count_le hd c N M hN hM1 hMN a had ha
    have hcount' : (∑ h1 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h2 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h3 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ h4 ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0,
        ∑ Q1 ∈ QSet (fun n => polyEval a d n) M h1 (4 * 8 ^ (d - 3)),
        ∑ Q2 ∈ QSet (fun n => polyEval a d n) M h2 (4 * 8 ^ (d - 3)),
        ∑ Q3 ∈ QSet (fun n => polyEval a d n) M h3 (4 * 8 ^ (d - 3)),
        ∑ Q4 ∈ QSet (fun n => polyEval a d n) M h4 (4 * 8 ^ (d - 3)),
          (if Q1 + Q2 + Q3 + Q4 = 0 then (1 : ℝ) else 0))
        ≤ (16 * (5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ) := by
      simpa only [QSf] using hcount
    have hfour := four_sum_le_count hd (R₀ := R₀) hMV c N M hN hM1 hMN a had ha
    -- `Count ≤ 16·5250·Ck³·N^{3d}`
    have hCnt : (16 * (5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ)
        ≤ 16 * 5250 * Ck ^ 3 * (N : ℝ) ^ (3 * d) := by
      have hM3 : (M : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hMN' 3
      have hKf3 : ((Kf c d N : ℕ) : ℝ) ^ 3 = Ck ^ 3 * (N : ℝ) ^ (3 * (d - 1)) := by
        rw [hKf, mul_pow, ← pow_mul, Nat.mul_comm]
      have hKeq : (3 : ℕ) * (d - 1) + 3 = 3 * d := by omega
      have hcast : ((5250 * (M * Kf c d N) ^ 3 : ℕ) : ℝ)
          = 5250 * ((M : ℝ) ^ 3 * ((Kf c d N : ℕ) : ℝ) ^ 3) := by push_cast; ring
      have hNexp : (N : ℝ) ^ (3 * (d - 1)) * (N : ℝ) ^ 3 = (N : ℝ) ^ (3 * d) := by
        rw [← pow_add, hKeq]
      have hN3 : (0 : ℝ) ≤ (N : ℝ) ^ (3 * (d - 1)) := by positivity
      have hCk30 : (0 : ℝ) ≤ Ck ^ 3 := pow_nonneg hCk0 3
      have hprod : (M : ℝ) ^ 3 * (N : ℝ) ^ (3 * (d - 1))
          ≤ (N : ℝ) ^ 3 * (N : ℝ) ^ (3 * (d - 1)) :=
        mul_le_mul_of_nonneg_right hM3 hN3
      rw [hcast, hKf3]
      have heq1 : 16 * (5250 * ((M : ℝ) ^ 3 * (Ck ^ 3 * (N : ℝ) ^ (3 * (d - 1)))))
          = 16 * 5250 * Ck ^ 3 * ((M : ℝ) ^ 3 * (N : ℝ) ^ (3 * (d - 1))) := by ring
      have heq2 : 16 * 5250 * Ck ^ 3 * (N : ℝ) ^ (3 * d)
          = 16 * 5250 * Ck ^ 3 * ((N : ℝ) ^ 3 * (N : ℝ) ^ (3 * (d - 1))) := by
        rw [show (N : ℝ) ^ (3 * d) = (N : ℝ) ^ (3 + 3 * (d - 1)) by congr 1; omega,
          pow_add]
      rw [heq1, heq2]
      exact mul_le_mul_of_nonneg_left hprod (by nlinarith [hCk30])
    -- `∫ SigTerm^4` 的界
    have hint4 : (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
        ≤ Rmax ^ 4 * (N : ℝ) ^ (4 * (m - (d - 1)))
          * (16 * 5250 * Ck ^ 3 * (N : ℝ) ^ (3 * d)) := by
      refine le_trans hfour ?_
      have hR4 : (0 : ℝ) ≤ (max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (m - (d - 1))) ^ 4 :=
        pow_nonneg (mul_nonneg hmax0 (by positivity)) 4
      refine le_trans (mul_le_mul_of_nonneg_left hcount' hR4) ?_
      have h1 : (max (R₀ (coeffConst c d)) 1 * (N : ℝ) ^ (m - (d - 1))) ^ 4
          = Rmax ^ 4 * (N : ℝ) ^ (4 * (m - (d - 1))) := by
        rw [← hRmax, mul_pow, ← pow_mul, Nat.mul_comm]
      rw [h1]
      exact mul_le_mul_of_nonneg_left hCnt
        (mul_nonneg (pow_nonneg (le_of_lt hRmax0) 4) (by positivity))
    -- 合并到 `N^{8m−d}`
    have hNfin : (N : ℝ) ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - (d - 1)))
          * (N : ℝ) ^ (3 * d) = (N : ℝ) ^ (8 * m - d) := by
      rw [← pow_add, ← pow_add, hexp1]
    have hfit : ((M : ℝ) + 1) ^ (4 * m)
          + (2 * (M : ℝ)) ^ (4 * (m - 1)) * (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
        ≤ (2 ^ (4 * m) + 2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
          * (N : ℝ) ^ (8 * m - d) := by
      have hM1 : (M : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
      have hP1 : ((M : ℝ) + 1) ^ (4 * m) ≤ 2 ^ (4 * m) * (N : ℝ) ^ (8 * m - d) := by
        calc ((M : ℝ) + 1) ^ (4 * m) ≤ (2 * (N : ℝ)) ^ (4 * m) :=
              pow_le_pow_left₀ (by positivity) hM1 _
          _ = 2 ^ (4 * m) * (N : ℝ) ^ (4 * m) := by rw [mul_pow]
          _ ≤ 2 ^ (4 * m) * (N : ℝ) ^ (8 * m - d) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN1 h4md) (by positivity)
      have hP2 : (2 * (M : ℝ)) ^ (4 * (m - 1))
            * (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
          ≤ (2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3) * (N : ℝ) ^ (8 * m - d) := by
        have hp : (2 * (M : ℝ)) ^ (4 * (m - 1))
            ≤ 2 ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - 1)) := by
          have h : 2 * (M : ℝ) ≤ 2 * (N : ℝ) := by linarith
          calc (2 * (M : ℝ)) ^ (4 * (m - 1)) ≤ (2 * (N : ℝ)) ^ (4 * (m - 1)) :=
                pow_le_pow_left₀ (by positivity) h _
            _ = 2 ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - 1)) := by rw [mul_pow]
        have hint0 : (0 : ℝ) ≤ ∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4 :=
          intervalIntegral.integral_nonneg (by norm_num) (fun x _ => by positivity)
        calc (2 * (M : ℝ)) ^ (4 * (m - 1))
              * (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
            ≤ (2 ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - 1)))
              * (Rmax ^ 4 * (N : ℝ) ^ (4 * (m - (d - 1)))
                * (16 * 5250 * Ck ^ 3 * (N : ℝ) ^ (3 * d))) :=
                mul_le_mul hp hint4 hint0 (by positivity)
          _ = (2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
                * ((N : ℝ) ^ (4 * (m - 1)) * (N : ℝ) ^ (4 * (m - (d - 1)))
                  * (N : ℝ) ^ (3 * d)) := by ring
          _ = (2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
                * (N : ℝ) ^ (8 * m - d) := by rw [hNfin]
      have hexpand : (2 ^ (4 * m) + 2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
            * (N : ℝ) ^ (8 * m - d)
          = 2 ^ (4 * m) * (N : ℝ) ^ (8 * m - d)
            + (2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
              * (N : ℝ) ^ (8 * m - d) := by ring
      rw [hexpand]
      linarith
    -- 组装
    have hmain : (∫ α in (0 : ℝ)..1, ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
        ≤ 2 ^ (4 * (m - 1)) * 8 *
            ((2 ^ (4 * m) + 2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
              * (N : ℝ) ^ (8 * m - d)) := by
      refine le_trans (integral_bound hd a hM1) ?_
      have hbase : ((M : ℝ) + 1) ^ (4 * 8 ^ (d - 2))
            + (2 * (M : ℝ)) ^ (4 * (8 ^ (d - 2) - 1))
              * (∫ α in (0 : ℝ)..1, (SigTerm a d M α) ^ 4)
          ≤ (2 ^ (4 * m) + 2 ^ (4 * (m - 1)) * Rmax ^ 4 * 16 * 5250 * Ck ^ 3)
            * (N : ℝ) ^ (8 * m - d) := by
        rw [← hm]
        exact hfit
      exact mul_le_mul_of_nonneg_left hbase (by positivity)
    refine le_trans hmain (le_of_eq ?_)
    have h8 : 8 ^ (d - 1) = 8 * m := by
      rw [hm, show d - 1 = (d - 2) + 1 by omega, pow_succ]
      ring
    rw [h8]
    simp only [Rd]
    rw [hm]
    ring

/-! ## 第 11 节：组装 `∀ d ≥ 2`（B3） -/

/-- 加强版蕴含原版（取 `M = N`）。 -/
theorem MeanValueBound.of_S {d : ℕ} (h : MeanValueBoundS d) : MeanValueBound d := by
  obtain ⟨R, hR, hb⟩ := h
  exact ⟨R, hR, fun c N hN a had ha => hb c N N hN hN le_rfl a had ha⟩

/-- **对一切 `d ≥ 2`，`P(d)` 成立**（基例 `P(2)` + 归纳步）。 -/
theorem meanValueBoundS_all (d : ℕ) (hd : 2 ≤ d) : MeanValueBoundS d := by
  induction d, hd using Nat.le_induction with
  | base => exact meanValueBoundS_two
  | succ m hm ih =>
      exact meanValueBoundS_succ (d := m + 1) (by omega) (by simpa using ih)

/-- **Jameson Theorem 1**（一般 `k`，均值估计）：对一切 `d ≥ 2`。 -/
theorem meanValueBound_all (d : ℕ) (hd : 2 ≤ d) : MeanValueBound d :=
  MeanValueBound.of_S (meanValueBoundS_all d hd)

end Waring
