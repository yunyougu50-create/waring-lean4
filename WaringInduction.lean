/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import WaringQuadratic
import WaringLemma8Form
import WaringWeylDiff
import WaringHolder

/-!
# Jameson Theorem 1 的归纳骨架

**归纳命题 `P(d)`**（`MeanValueBound d`）：

```text
∃ R : ℕ → ℝ, (∀ c, 0 < R c) ∧
  ∀ (c N : ℕ) (a : ℕ → ℤ), 1 ≤ N →
    (∀ j ≤ d, |a_j| ≤ c·N^{d−j}) →
    ∫₀¹ ‖Σ_{n≤N} e(α·polyEval a d n)‖^{8^{d−1}} dα ≤ R c · N^{8^{d−1}−d}
```

`R c` 只在系数界常数 `c` 上依赖，**不依赖 `N`**——这是归纳能进行的关键。

* 基例 `P(2)`：由 `WaringQuadratic`（一般二次形式）给出，常数 `c` 对应
  Jameson 的 `max(c₂, c₁)`。
* 归纳步 `P(d−1) → P(d)`：
  Weyl 差分（`WaringWeylInq.normSq_expSum_le_zero`）→ `φ` 的系数界
  （`WaringCoeffBound.diffCoeff_bound`）→ Hölder（`WaringHolder.integral_normSq_pow_le`）
  → 对每个 `b_h` 用 `P(d−1)` → 四重和 + Lemma 7（`WaringLemma7.hmCount7_le'`）。

本文件只放**陈述**（和它的基本推论），归纳步在后续文件。
-/

open intervalIntegral Finset

namespace Waring

/-- **归纳命题 `P(d)`**（Jameson Theorem 1 的精确形式）：存在常数族 `R(c)`，
使得任何整系数 `d` 次多项式（系数界 `|a_j| ≤ c·N^{d−j}`）的指数和的
`8^{d−1}` 阶矩不超过 `R(c)·N^{8^{d−1}−d}`。 -/
def MeanValueBound (d : ℕ) : Prop :=
  ∃ R : ℕ → ℝ, (∀ c, 0 < R c) ∧
    ∀ (c : ℕ) (N : ℕ), 1 ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
      (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
      (∫ α in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval a d n) N α‖ ^ (8 ^ (d - 1)))
        ≤ R c * (N : ℝ) ^ (8 ^ (d - 1) - d)

/-- `P(d)` 给出常数依赖的显式形式（解包 `∃ R`）。 -/
theorem meanValueBound_apply {d : ℕ} (h : MeanValueBound d) (c N : ℕ) (hN : 1 ≤ N)
    (a : ℕ → ℤ) (had : a d ≠ 0)
    (ha : ∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) :
    ∃ R : ℝ, 0 < R ∧
      (∫ α in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval a d n) N α‖ ^ (8 ^ (d - 1)))
        ≤ R * (N : ℝ) ^ (8 ^ (d - 1) - d) := by
  obtain ⟨R, hR, hbound⟩ := h
  exact ⟨R c, hR c, hbound c N hN a had ha⟩

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

/-- **加强版归纳命题**（`M ≤ N`）：求和长度 `M` 可以小于系数尺度的 `N`，
但界仍然用 `N`。这是归纳步真正需要的形式——变量替换后 `b_h` 的求和长度是
`N−h+1 < N`，而系数界是 `N` 尺度的（见 `WARING-M3-PLAN.md` §11 的障碍 B）。 -/
def MeanValueBoundS (d : ℕ) : Prop :=
  ∃ R : ℕ → ℝ, (∀ c, 0 < R c) ∧
    ∀ (c N M : ℕ), 1 ≤ N → 1 ≤ M → M ≤ N → ∀ (a : ℕ → ℤ), a d ≠ 0 →
      (∀ j, j ≤ d → |a j| ≤ (c : ℤ) * (N : ℤ) ^ (d - j)) →
      (∫ α in (0 : ℝ)..1,
          ‖expSum (fun n => polyEval a d n) M α‖ ^ (8 ^ (d - 1)))
        ≤ R c * (N : ℝ) ^ (8 ^ (d - 1) - d)

/-- 加强版蕴含原版（取 `M = N`）。 -/
theorem MeanValueBound.of_S {d : ℕ} (h : MeanValueBoundS d) : MeanValueBound d := by
  obtain ⟨R, hR, hb⟩ := h
  exact ⟨R, hR, fun c N hN a had ha => hb c N N hN hN le_rfl a had ha⟩

/-- **基例 `P(2)`**：一般二次形式的八阶矩界（由 `WaringLemma8Form` 给出）。 -/
theorem meanValueBound_two : MeanValueBound 2 := by
  refine ⟨fun c : ℕ => 100000 * (((2 * c + c + 1 : ℕ) : ℝ) ^ 4), ?_, ?_⟩
  · intro c
    positivity
  · intro c N hN a ha2nz ha
    -- 系数界：`|a 2| ≤ c`、`|a 1| ≤ c·N`
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
    -- `∫‖S‖^8 = ∫(normSq qSum)^4`
    have hfun : ∀ α : ℝ, ‖expSum (fun n => polyEval a 2 n) N α‖ ^ (8 ^ (2 - 1))
        = (Complex.normSq (qSum (a 2) (a 1) N α)) ^ 4 := by
      intro α
      rw [expSum_polyEval_two, norm_mul, norm_e, one_mul]
      rw [Complex.normSq_eq_norm_sq]
      norm_num
      ring
    simp_rw [hfun]
    refine le_trans (integral_normSq_pow_four_le_form (a 2) (a 1) h2' c c N hN h2 h1) ?_
    · -- 目标常数比较：`10⁶(2c+c+1)⁴ N⁶ ≤ 10⁶(2c+c+1)⁴ N⁶`
      rfl

/-! ## 加强版基例（`M ≤ N`）

关键：`sum_qQ_sq_le_K` 给 `Σ qQ² ≤ 10000·qK·M⁴`，而
`qK a b M = 4M²|a| + 2M|b| ≤ 4c₂M² + 2c₁MN ≤ (4c₂+2c₁)·M·N`
（用 `M ≤ N`），于是 `10000·qK·M⁴ ≤ 10000(4c₂+2c₁)M⁵N ≤ 10000(4c₂+2c₁)N⁶`。 -/

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

end Waring
