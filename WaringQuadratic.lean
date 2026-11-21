/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import WaringExpSum
import WaringCount
import WaringLemma3
import WaringSymm
import WaringTheorem1

/-!
# Jameson Lemma 8 的一般二次形式版本

`k = 2` 的圆法（`WaringTheorem1.integral_normSq_pow_four_le`）只处理
`f(n) = n²`。本文件把它推广到**一般整系数二次形式**

```text
f(n) = a₂ n² + a₁ n,      a₂ ≠ 0,
```

并证明八次矩界

```text
∫₀¹ |∑_{n=0}^{N} e(α f(n))|⁸ dα ≤ C(a₂,a₁) · N⁶.
```

证明路线（与 `k = 2` 的情形平行，但常数只依赖 `a₂, a₁`）：

1. **矩 = 计数**：`∫₀¹|S|⁸ = #{(p,q) ∈ [0,N]⁸ : ∑ f(pᵢ) = ∑ f(qᵢ)}`；
2. **换变量** `hᵢ = pᵢ − qᵢ`、`mᵢ = pᵢ + qᵢ`，用
   `f(p) − f(q) = (p−q)(a₂(p+q) + a₁)` 把方程变成 `∑ hᵢ(a₂mᵢ+a₁) = 0`；
3. **Fubini 拆分**：把四个坐标分成两组，计数化为二元部分和 `qQ` 的平方和；
4. **部分和的逐点界**：对固定的 `(h₁,h₂) ≠ 0`，方程
   `a₂h₁m₁ + a₂h₂m₂ = n − a₁(h₁+h₂)` 在 `[0,M]²` 中的解数用
   `WaringLemma3.fiber_le_gcd` 控制（`≤ M/max|prim| + 1`）。

关键的数学观察：因为 `gcd(h₁,h₂) | h₁ + h₂`，纤维非空蕴含
`gcd(h₁,h₂) | n`（而不是依赖 `h₁+h₂` 的条件）。所以 Jameson 的
`gcd` 重索引（`sum_inv_prim_le`）可以原封不动地使用。`a₂` 只通过
`prim (a₂·h)` 进入，而 `prim (a₂·h)` 与 `prim h` 的坐标绝对值相同，
因此逐项界与 `f(n)=n²` 情形完全一致。
-/

open Finset intervalIntegral

set_option maxHeartbeats 1000000

namespace Waring

/-! ## 第一部分：指数和与八次矩的展开 -/

/-- `e(Σ x) = ∏ e(x)`。 -/
theorem e_sum (ι : Type) [Fintype ι] (x : ι → ℝ) : e (∑ i, x i) = ∏ i, e (x i) := by
  unfold e
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-- `e((Σ x)·α) = ∏ e(x·α)`。 -/
theorem e_sum_mul (ι : Type) [Fintype ι] (x : ι → ℝ) (α : ℝ) :
    e ((∑ i, x i) * α) = ∏ i, e (x i * α) := by
  rw [show (∑ i, x i) * α = ∑ i, x i * α from Finset.sum_mul ..]
  exact e_sum ι (fun i => x i * α)

/-- `α ↦ e(c·α)` 连续。 -/
theorem continuous_e_comp (c : ℝ) : Continuous fun α : ℝ => e (c * α) := by
  unfold e
  fun_prop

/-- 二次形式 `f(n) = a n² + b n`（整系数）。 -/
def qf (a b : ℤ) (n : ℤ) : ℤ := a * n ^ 2 + b * n

/-- 四元组的 `f`-和 `∑_{i<4} f(pᵢ)`。 -/
def qf4 (a b : ℤ) {N : ℕ} (p : Fin 4 → Fin (N + 1)) : ℤ :=
  ∑ i : Fin 4, qf a b ((p i : ℕ) : ℤ)

/-- 一般二次形式的指数和 `∑_{n≤N} e(α f(n))`。 -/
noncomputable def qSum (a b : ℤ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n : Fin (N + 1), e ((qf a b (n : ℤ) : ℝ) * α)

/-- `qSum⁴` 展开成四重和。 -/
theorem qSum_pow_four (a b : ℤ) (N : ℕ) (α : ℝ) :
    qSum a b N α ^ 4 = ∑ p : Fin 4 → Fin (N + 1),
      e (((qf4 a b p) : ℝ) * α) := by
  unfold qSum
  rw [Finset.sum_pow']
  rw [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl ?_
  intro p _
  simp only [qf4, qf]
  push_cast
  rw [e_sum_mul]

/-- `conj (qSum)⁴` 展开成四重和。 -/
theorem conj_qSum_pow_four (a b : ℤ) (N : ℕ) (α : ℝ) :
    (starRingEnd ℂ) (qSum a b N α) ^ 4 = ∑ p : Fin 4 → Fin (N + 1),
      e (-(((qf4 a b p) : ℝ) * α)) := by
  unfold qSum
  rw [map_sum, Finset.sum_pow']
  rw [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl ?_
  intro p _
  have step1 : (∏ i : Fin 4,
      (starRingEnd ℂ) (e ((qf a b ((p i : ℕ) : ℤ) : ℝ) * α)))
      = ∏ i : Fin 4, e (((-(qf a b ((p i : ℕ) : ℤ)) : ℤ) : ℝ) * α) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← e_neg]
    congr 1
    push_cast
    ring
  rw [step1, ← e_sum_mul]
  congr 1
  rw [qf4]
  push_cast
  rw [Finset.sum_neg_distrib]
  ring

/-- 八元组「`f`-和相等」的计数。 -/
noncomputable def qEqCount (a b : ℤ) (N : ℕ) : ℕ :=
  ((Finset.univ : Finset
      ((Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1)))).filter
    (fun pq => qf4 a b pq.1 = qf4 a b pq.2)).card

/-- **矩 = 计数**（一般二次形式的八次矩）。 -/
theorem integral_normSq_pow_four_q (a b : ℤ) (N : ℕ) :
    (∫ α in (0 : ℝ)..1, (Complex.normSq (qSum a b N α)) ^ 4)
      = (qEqCount a b N : ℝ) := by
  have hfun : ∀ α : ℝ, (((Complex.normSq (qSum a b N α)) ^ 4 : ℝ) : ℂ)
      = ((starRingEnd ℂ) (qSum a b N α)) ^ 4 * (qSum a b N α) ^ 4 := by
    intro α
    rw [Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self]
    ring
  have hcomb : ∀ (p q : Fin 4 → Fin (N + 1)) (α : ℝ),
      e (-(((qf4 a b p) : ℝ) * α)) * e (((qf4 a b q) : ℝ) * α)
      = e (((↑(qf4 a b q - qf4 a b p)) : ℝ) * α) := by
    intro p q α
    rw [← e_add]
    congr 1
    push_cast
    ring
  have hstep : ∀ pq : (Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1)),
      (∫ α in (0 : ℝ)..1, e (((↑(qf4 a b pq.2 - qf4 a b pq.1)) : ℝ) * α))
        = (if qf4 a b pq.1 = qf4 a b pq.2 then 1 else 0) := by
    intro pq
    set m : ℤ := qf4 a b pq.2 - qf4 a b pq.1 with hm
    rw [show (((↑(qf4 a b pq.2 - qf4 a b pq.1)) : ℝ)) = (m : ℝ) from by rw [hm]]
    rw [integral_e_mul_int]
    by_cases h : qf4 a b pq.1 = qf4 a b pq.2
    · have hz : m = 0 := by rw [hm, h]; ring
      simp [h, hz]
    · have hz : m ≠ 0 := by
        rw [hm]
        intro hz
        exact h (by linarith)
      simp [h, hz]
  have hcont : ∀ p : Fin 4 → Fin (N + 1),
      Continuous fun α : ℝ => ∑ q : Fin 4 → Fin (N + 1),
        e (((↑(qf4 a b q - qf4 a b p)) : ℝ) * α) := by
    intro p
    exact continuous_finsetSum _ (fun q _ => continuous_e_comp _)
  have hswap : (∫ α in (0 : ℝ)..1, ∑ p : (Fin 4 → Fin (N + 1)),
      ∑ q : (Fin 4 → Fin (N + 1)), e (((↑(qf4 a b q - qf4 a b p)) : ℝ) * α))
      = ∑ p : (Fin 4 → Fin (N + 1)), ∑ q : (Fin 4 → Fin (N + 1)),
          ∫ α in (0 : ℝ)..1, e (((↑(qf4 a b q - qf4 a b p)) : ℝ) * α) := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl ?_
      intro p _
      rw [intervalIntegral.integral_finsetSum]
      intro q _
      exact Continuous.intervalIntegrable (continuous_e_comp _) 0 1
    · intro p _
      exact Continuous.intervalIntegrable (hcont p) 0 1
  apply Complex.ofReal_inj.mp
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hfun, conj_qSum_pow_four, qSum_pow_four]
  simp only [Finset.sum_mul_sum]
  simp_rw [hcomb]
  rw [hswap]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hstep (p, q)))]
  rw [← Fintype.sum_prod_type
    (f := fun pq : (Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1)) =>
      if qf4 a b pq.1 = qf4 a b pq.2 then (1 : ℂ) else 0)]
  rw [Finset.sum_boole]
  norm_cast

/-! ## 第二部分：换变量 `hᵢ = pᵢ − qᵢ`、`mᵢ = pᵢ + qᵢ` -/

/-- `(h,m)` 形式的计数：`∑ᵢ hᵢ(a mᵢ + b) = 0`。 -/
noncomputable def qHMCount (a b : ℤ) (N : ℕ) : ℕ :=
  (((hBox N).product (mBox N)).filter
    (fun hm => (∑ i : Fin 4, hm.1 i * (a * hm.2 i + b)) = 0)).card

/-- `toHM` 的像落在 `hBox × mBox` 里。 -/
theorem toHM_mem_box (N : ℕ) (pq : (Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1))) :
    toHM N pq ∈ (hBox N).product (mBox N) := by
  have h1 : (fun i => (pq.1 i : ℤ) - (pq.2 i : ℤ)) ∈ hBox N := by
    rw [hBox, Fintype.mem_piFinset]
    intro i
    have h1' : (0 : ℤ) ≤ (pq.1 i : ℤ) := Int.natCast_nonneg _
    have h2' : (pq.2 i : ℤ) ≤ (N : ℤ) := by
      have := (pq.2 i).isLt
      exact_mod_cast (Nat.lt_succ_iff.mp this)
    have h3' : (0 : ℤ) ≤ (pq.2 i : ℤ) := Int.natCast_nonneg _
    have h4' : (pq.1 i : ℤ) ≤ (N : ℤ) := by
      have := (pq.1 i).isLt
      exact_mod_cast (Nat.lt_succ_iff.mp this)
    rw [Finset.mem_Icc]
    constructor <;> linarith
  have h2 : (fun i => (pq.1 i : ℤ) + (pq.2 i : ℤ)) ∈ mBox N := by
    rw [mBox, Fintype.mem_piFinset]
    intro i
    have h1' : (0 : ℤ) ≤ (pq.1 i : ℤ) := Int.natCast_nonneg _
    have h2' : (pq.1 i : ℤ) ≤ (N : ℤ) := by
      have := (pq.1 i).isLt
      exact_mod_cast (Nat.lt_succ_iff.mp this)
    have h3' : (0 : ℤ) ≤ (pq.2 i : ℤ) := Int.natCast_nonneg _
    have h4' : (pq.2 i : ℤ) ≤ (N : ℤ) := by
      have := (pq.2 i).isLt
      exact_mod_cast (Nat.lt_succ_iff.mp this)
    rw [Finset.mem_Icc]
    constructor <;> linarith
  exact Finset.mem_product.mpr ⟨h1, h2⟩

/-- `toHM` 单射。 -/
theorem toHM_inj (N : ℕ) :
    ∀ pq : (Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1)),
      ∀ pq' : (Fin 4 → Fin (N + 1)) × (Fin 4 → Fin (N + 1)),
      toHM N pq = toHM N pq' → pq = pq' := by
  intro pq pq' heq
  simp only [toHM, Prod.mk.injEq] at heq
  obtain ⟨h1, h2⟩ := heq
  have hp : pq.1 = pq'.1 := by
    funext i
    have h1i := congrFun h1 i
    have h2i := congrFun h2 i
    have h : (pq.1 i : ℤ) = (pq'.1 i : ℤ) := by linarith
    omega
  have hq : pq.2 = pq'.2 := by
    funext i
    have h1i := congrFun h1 i
    have h2i := congrFun h2 i
    have h : (pq.2 i : ℤ) = (pq'.2 i : ℤ) := by linarith
    omega
  exact Prod.ext hp hq

/-- **换变量**：`f`-和相等的计数不超过 `(h,m)` 计数。 -/
theorem qEqCount_le_qHMCount (a b : ℤ) (N : ℕ) : qEqCount a b N ≤ qHMCount a b N := by
  classical
  refine Finset.card_le_card_of_injOn (toHM N) ?_ ?_
  · intro pq hpq
    rw [Finset.mem_coe, Finset.mem_filter] at hpq
    obtain ⟨-, hpq⟩ := hpq
    simp only [qf4] at hpq
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨toHM_mem_box N pq, ?_⟩
    have hsq : ∀ i : Fin 4,
        ((pq.1 i : ℤ) - (pq.2 i : ℤ)) * (a * ((pq.1 i : ℤ) + (pq.2 i : ℤ)) + b)
          = qf a b ((pq.1 i : ℕ) : ℤ) - qf a b ((pq.2 i : ℕ) : ℤ) := by
      intro i
      unfold qf
      ring
    show (∑ i : Fin 4, ((pq.1 i : ℤ) - (pq.2 i : ℤ))
      * (a * ((pq.1 i : ℤ) + (pq.2 i : ℤ)) + b)) = 0
    rw [Finset.sum_congr rfl (fun i _ => hsq i), Finset.sum_sub_distrib, hpq]
    ring
  · exact fun x _ y _ hxy => toHM_inj N x y hxy

/-! ## 第三部分：Fubini 拆分（`Fin 4 → Fin 2 × Fin 2`） -/

/-- 二元部分和盒子 `[−H,H]² × [0,M]²`。 -/
noncomputable def qPbox2 (H M : ℕ) : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  (box2 (-(H : ℤ)) (H : ℤ)).product (box2 (0 : ℤ) (M : ℤ))

/-- 二元部分和 `h₀(a m₀ + b) + h₁(a m₁ + b)`。 -/
def qAval (a b : ℤ) (p : (Fin 2 → ℤ) × (Fin 2 → ℤ)) : ℤ :=
  a * (p.1 0 * p.2 0 + p.1 1 * p.2 1) + b * (p.1 0 + p.1 1)

/-- 二元部分和计数。 -/
noncomputable def qQ (a b : ℤ) (H M : ℕ) (n : ℤ) : ℕ :=
  ((qPbox2 H M).filter (fun p => qAval a b p = n)).card

/-- `box2 0 M` 的基数。 -/
theorem box2_zero_card (M : ℕ) : (box2 (0 : ℤ) (M : ℤ)).card = (M + 1) ^ 2 := by
  rw [box2, Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Int.card_Icc]
  have h : (M : ℤ) + 1 - 0 = (M : ℤ) + 1 := by ring
  rw [h]
  omega

/-- `qPbox2` 的基数。 -/
theorem qPbox2_card (H M : ℕ) : (qPbox2 H M).card = (2 * H + 1) ^ 2 * (M + 1) ^ 2 := by
  calc (qPbox2 H M).card
      = (box2 (-(H : ℤ)) (H : ℤ)).card * (box2 (0 : ℤ) (M : ℤ)).card :=
        Finset.card_product _ _
    _ = (2 * H + 1) ^ 2 * (box2 (0 : ℤ) (M : ℤ)).card := by rw [card_box2]
    _ = (2 * H + 1) ^ 2 * (M + 1) ^ 2 := by rw [box2_zero_card]

/-- **对接**：`qHMCount` 不超过 `(Pbox2 × Pbox2)` 中的 `A + A' = 0` 计数。 -/
theorem qHMCount_le_qHMCount2 (a b : ℤ) (N : ℕ) :
    qHMCount a b N ≤
      (((qPbox2 N (2 * N)).product (qPbox2 N (2 * N))).filter
        (fun pq => qAval a b pq.1 + qAval a b pq.2 = 0)).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun hm : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
      (((split4 hm.1).1, (split4 hm.2).1), ((split4 hm.1).2, (split4 hm.2).2))) ?_ ?_
  · intro hm hhm
    rw [Finset.mem_coe, Finset.mem_filter] at hhm
    obtain ⟨hhmS, hhm0⟩ := hhm
    have hh1 : hm.1 ∈ hBox N := ((Finset.mem_product).mp hhmS).1
    have hh2 : hm.2 ∈ mBox N := ((Finset.mem_product).mp hhmS).2
    rw [hBox, Fintype.mem_piFinset] at hh1
    rw [mBox, Fintype.mem_piFinset] at hh2
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · rw [box2, Fintype.mem_piFinset]
        intro i
        have := hh1 ⟨i.val, by omega⟩
        simpa [split4] using this
      · rw [box2, Fintype.mem_piFinset]
        intro i
        have := hh2 ⟨i.val, by omega⟩
        simpa [split4] using this
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · rw [box2, Fintype.mem_piFinset]
        intro i
        have := hh1 ⟨i.val + 2, by omega⟩
        simpa [split4] using this
      · rw [box2, Fintype.mem_piFinset]
        intro i
        have := hh2 ⟨i.val + 2, by omega⟩
        simpa [split4] using this
    · have hsum := hhm0
      rw [sum_fin4] at hsum
      have hgoal : qAval a b ((split4 hm.1).1, (split4 hm.2).1)
          + qAval a b ((split4 hm.1).2, (split4 hm.2).2)
          = hm.1 0 * (a * hm.2 0 + b) + hm.1 1 * (a * hm.2 1 + b)
            + hm.1 2 * (a * hm.2 2 + b) + hm.1 3 * (a * hm.2 3 + b) := by
        obtain ⟨e1, e2⟩ := split4_fst_val hm.1
        obtain ⟨e3, e4⟩ := split4_fst_val hm.2
        obtain ⟨e5, e6⟩ := split4_snd_val hm.1
        obtain ⟨e7, e8⟩ := split4_snd_val hm.2
        simp only [qAval, e1, e2, e3, e4, e5, e6, e7, e8]
        ring
      rw [hgoal, hsum]
  · intro x _ y _ hxy
    obtain ⟨h1, m1⟩ := x
    obtain ⟨h2, m2⟩ := y
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨⟨hh1, hm1⟩, hh2, hm2⟩ := hxy
    have hsp1 : split4 h1 = split4 h2 := Prod.ext hh1 hh2
    have hsp2 : split4 m1 = split4 m2 := Prod.ext hm1 hm2
    rw [split4_injective hsp1, split4_injective hsp2]

/-- **Fubini 展开**：`qHMCount` 不超过 `Σ_n qQ(n)·qQ(−n)`。 -/
theorem qHMCount_le_sum_qQ (a b : ℤ) (N : ℕ) (K : ℤ)
    (hK : ∀ p ∈ qPbox2 N (2 * N), |qAval a b p| ≤ K) :
    qHMCount a b N ≤
      ∑ n ∈ Finset.Icc (-K) K, qQ a b N (2 * N) n * qQ a b N (2 * N) (-n) := by
  classical
  set P : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) := qPbox2 N (2 * N) with hP
  -- 内层：每个 `p` 贡献 `qQ(−A p)`
  have hstep1 : (((P.product P).filter (fun pq => qAval a b pq.1 + qAval a b pq.2 = 0)).card)
      = ∑ p ∈ P, qQ a b N (2 * N) (-(qAval a b p)) := by
    rw [Finset.card_filter]
    rw [show (∑ i ∈ P.product P,
          (if qAval a b i.1 + qAval a b i.2 = 0 then (1 : ℕ) else 0))
        = ∑ p ∈ P, ∑ q ∈ P,
          (if qAval a b p + qAval a b q = 0 then (1 : ℕ) else 0) from
      Finset.sum_product P P (fun i => if qAval a b i.1 + qAval a b i.2 = 0 then (1 : ℕ) else 0)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have hc : (P.filter (fun q => qAval a b p + qAval a b q = 0))
        = (P.filter (fun q => qAval a b q = -(qAval a b p))) := by
      apply Finset.filter_congr
      intro q _
      constructor <;> intro h <;> linarith
    rw [← Finset.card_filter]
    rw [hc]
    rw [show (P.filter (fun q => qAval a b q = -(qAval a b p)))
        = ((qPbox2 N (2 * N)).filter (fun q => qAval a b q = -(qAval a b p))) from by rw [hP]]
    rw [← qQ]
  -- 外层：按 `n = A p` 展开
  refine le_trans (qHMCount_le_qHMCount2 a b N) ?_
  rw [show (((qPbox2 N (2 * N)).product (qPbox2 N (2 * N))).filter
        (fun pq => qAval a b pq.1 + qAval a b pq.2 = 0)).card
      = ∑ p ∈ P, qQ a b N (2 * N) (-(qAval a b p)) from hstep1]
  have hpoint : ∀ p ∈ P, qQ a b N (2 * N) (-(qAval a b p))
      = ∑ n ∈ Finset.Icc (-K) K,
          (if qAval a b p = n then qQ a b N (2 * N) (-n) else 0) := by
    intro p hp
    rw [Finset.sum_ite_eq]
    rw [if_pos (by
      rw [Finset.mem_Icc]
      have h := hK p hp
      rw [abs_le] at h
      exact h)]
  rw [Finset.sum_congr rfl (fun p hp => hpoint p hp)]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun n _ => ?_)
  rw [← Finset.sum_filter]
  have hcard : (P.filter (fun x => qAval a b x = n)).card = qQ a b N (2 * N) n := by
    rw [qQ, ← hP]
  rw [Finset.sum_const, hcard]
  simp

/-! ## 第四部分：`qQ` 的逐点界（Jameson Lemma 3 的一般形式）

对 `h ≠ 0`，方程 `a(h₀m₀+h₁m₁) + b(h₀+h₁) = n` 的 `m` 解数
由 `fiber_le_gcd` 控制为 `M/max|prim (a·h)| + 1`。关键事实：
`prim (a·h)` 与 `prim h` 的坐标绝对值相同，因此该界就是
`M/max|prim h| + 1`，与 `f(n) = n²` 的情形完全一致。

第二个关键事实：**纤维非空 ⟹ gcd(h₀,h₁) | n**。
（因为 `gcd | h₀+h₁`，所以 `a(h₀m₀+h₁m₁) + b(h₀+h₁) ≡ 0 (mod gcd)`。）
于是 Jameson 的 `gcd` 重索引 `sum_inv_prim_le` 原封不动可用。 -/

/-- `prim (a·h)` 与 `prim h` 的坐标绝对值相同。 -/
theorem prim_smul_natAbs (a : ℤ) (ha : a ≠ 0) {h : Fin 2 → ℤ} (hh : h ≠ 0) (i : Fin 2) :
    (prim (fun j => a * h j) i).natAbs = (prim h i).natAbs := by
  have hG : Nat.gcd ((a * h 0).natAbs) ((a * h 1).natAbs)
      = a.natAbs * Nat.gcd (h 0).natAbs (h 1).natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Nat.gcd_mul_left]
  have hdvd : ∀ j : Fin 2, ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ∣ h j := by
    intro j
    have h1 := Int.gcd_dvd_left (h 0) (h 1)
    have h2 := Int.gcd_dvd_right (h 0) (h 1)
    rw [Int.gcd_eq_natAbs] at h1 h2
    fin_cases j
    · exact h1
    · exact h2
  have hdvdA : ∀ j : Fin 2,
      ((Nat.gcd ((a * h 0).natAbs) ((a * h 1).natAbs) : ℕ) : ℤ) ∣ a * h j := by
    intro j
    have hgoal : Nat.gcd ((a * h 0).natAbs) ((a * h 1).natAbs) ∣ (a * h j).natAbs := by
      rw [hG, Int.natAbs_mul]
      fin_cases j
      · exact mul_dvd_mul (dvd_refl _) (Nat.gcd_dvd_left _ _)
      · exact mul_dvd_mul (dvd_refl _) (Nat.gcd_dvd_right _ _)
    rw [← Int.natAbs_dvd_natAbs]
    simpa using hgoal
  have hdvdA' : ((a.natAbs * Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ∣ a * h i := by
    rw [← hG]
    exact hdvdA i
  have hprimA : prim (fun j => a * h j) i
      = a * h i / ((a.natAbs * Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) := by
    unfold prim
    rw [hG]
  have hprimB : prim h i = h i / ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) := rfl
  rw [hprimA, hprimB]
  rw [Int.natAbs_ediv_of_dvd hdvdA', Int.natAbs_ediv_of_dvd (hdvd i)]
  rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
  exact Nat.mul_div_mul_left _ _ (Int.natAbs_pos.mpr ha)

/-- 纤维界：`h ≠ 0` 时，`a(h₀m₀+h₁m₁) + b(h₀+h₁) = n` 在 `[0,M]²` 中的
解数不超过 `M/max|prim h| + 1`。 -/
theorem qQ_fiber_le (a b : ℤ) (ha : a ≠ 0) (M : ℕ) (n : ℤ) {h : Fin 2 → ℤ}
    (hh : h ≠ 0) :
    ((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ =>
      a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = n)).card
      ≤ M / max (prim h 0).natAbs (prim h 1).natAbs + 1 := by
  classical
  have hAne : (fun j => a * h j) ≠ 0 := by
    intro hzero
    apply hh
    funext i
    have hi := congrFun hzero i
    simp only [Pi.zero_apply] at hi
    exact mul_left_cancel₀ ha (by simpa using hi)
  have hfilter : (box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ =>
      a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = n)
      = (box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ =>
        (a * h 0) * m 0 + (a * h 1) * m 1 = n - b * (h 0 + h 1)) := by
    refine Finset.filter_congr (fun m _ => ?_)
    constructor
    · intro hm
      have hring : (a * h 0) * m 0 + (a * h 1) * m 1
          = a * (h 0 * m 0 + h 1 * m 1) := by ring
      linarith
    · intro hm
      have hring : a * (h 0 * m 0 + h 1 * m 1)
          = (a * h 0) * m 0 + (a * h 1) * m 1 := by ring
      linarith
  rw [hfilter]
  refine le_trans (fiber_le_gcd hAne M (n - b * (h 0 + h 1))) ?_
  rw [prim_smul_natAbs a ha hh 0, prim_smul_natAbs a ha hh 1]

/-- **纤维非空 ⟹ `gcd | n`**。 -/
theorem gcond_of_fiber (a b : ℤ) (M : ℕ) (n : ℤ) {h : Fin 2 → ℤ}
    {m : Fin 2 → ℤ} (hm : a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = n) :
    gcond n h := by
  unfold gcond
  have hdvd : ∀ j : Fin 2, ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ∣ h j := by
    intro j
    have h1 := Int.gcd_dvd_left (h 0) (h 1)
    have h2 := Int.gcd_dvd_right (h 0) (h 1)
    rw [Int.gcd_eq_natAbs] at h1 h2
    fin_cases j
    · exact h1
    · exact h2
  have hdvdsum : ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ) ∣ h 0 + h 1 :=
    dvd_add (hdvd 0) (hdvd 1)
  have hdvdprod : ((Nat.gcd (h 0).natAbs (h 1).natAbs : ℕ) : ℤ)
      ∣ h 0 * m 0 + h 1 * m 1 :=
    dvd_add (dvd_mul_of_dvd_left (hdvd 0) (m 0)) (dvd_mul_of_dvd_left (hdvd 1) (m 1))
  rw [← hm]
  exact dvd_add (dvd_mul_of_dvd_right hdvdprod a) (dvd_mul_of_dvd_right hdvdsum b)

/-- `qQ` 按 `h` 拆成纤维的卡片和。 -/
theorem qQ_eq_sum_fiber (a b : ℤ) (H M : ℕ) (n : ℤ) :
    qQ a b H M n = ∑ h ∈ box2 (-(H : ℤ)) (H : ℤ),
      ((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ =>
        a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = n)).card := by
  classical
  rw [qQ, Finset.card_filter, qPbox2]
  rw [show (∑ i ∈ (box2 (-(H : ℤ)) (H : ℤ)).product (box2 (0 : ℤ) (M : ℤ)),
        (if qAval a b i = n then (1 : ℕ) else 0))
      = ∑ h ∈ box2 (-(H : ℤ)) (H : ℤ), ∑ m ∈ box2 (0 : ℤ) (M : ℤ),
        (if qAval a b (h, m) = n then (1 : ℕ) else 0) from
    Finset.sum_product _ _ _]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rfl

/-- **Lemma 3（一般二次形式版）**：`qQ(H,M;n) ≤ 4H(H+1) + 8HM·σ₋₁(|n|)`（`n ≠ 0`）。 -/
theorem qQ_le_sigma (a b : ℤ) (ha : a ≠ 0) (H M : ℕ) {n : ℤ} (hn : n ≠ 0) :
    (qQ a b H M n : ℚ) ≤ 4 * (H : ℚ) * ((H : ℚ) + 1)
      + 8 * (H : ℚ) * (M : ℚ) * sigmaMinusOne n.natAbs := by
  classical
  set B : Finset (Fin 2 → ℤ) := box2 (-(H : ℤ)) (H : ℤ) with hB
  set D : Finset (Fin 2 → ℤ) := box2 (0 : ℤ) (M : ℤ) with hD
  set F : (Fin 2 → ℤ) → ℕ := fun h => (D.filter (fun m : Fin 2 → ℤ =>
      a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = n)).card with hF
  set Sf : Finset (Fin 2 → ℤ) := B.filter (fun h : Fin 2 → ℤ => h ≠ 0 ∧ gcond n h) with hSf
  have hQ : qQ a b H M n = ∑ h ∈ B, F h := qQ_eq_sum_fiber a b H M n
  -- 去掉 h = 0
  have hzero : F 0 = 0 := by
    rw [hF]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _ hm
    apply hn
    have h' : a * (((0 : Fin 2 → ℤ) 0) * m 0 + ((0 : Fin 2 → ℤ) 1) * m 1)
        + b * ((0 : Fin 2 → ℤ) 0 + (0 : Fin 2 → ℤ) 1) = n := hm
    simpa using h'.symm
  have h1 : (∑ h ∈ B, F h) = ∑ h ∈ B.filter (fun h : Fin 2 → ℤ => h ≠ 0), F h := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro h hB hnotmem
    by_cases h0 : h = 0
    · rw [h0]
      exact hzero
    · exact absurd (by rw [Finset.mem_filter]; exact ⟨hB, h0⟩) hnotmem
  -- 去掉 gcd ∤ n 的 h
  have h2 : (∑ h ∈ B.filter (fun h : Fin 2 → ℤ => h ≠ 0), F h) = ∑ h ∈ Sf, F h := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro h hh
      rw [hSf, Finset.mem_filter] at hh
      rw [Finset.mem_filter]
      exact ⟨hh.1, hh.2.1⟩
    · intro h hh hnotmem
      rw [Finset.mem_filter] at hh
      obtain ⟨hB, hne⟩ := hh
      have hc : ¬ gcond n h := by
        intro hc'
        exact hnotmem (by rw [hSf, Finset.mem_filter]; exact ⟨hB, hne, hc'⟩)
      rw [hF]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro m _ hm
      exact hc (gcond_of_fiber a b M n hm)
  -- 逐项界
  have h3 : ((∑ h ∈ Sf, F h : ℕ) : ℚ) ≤ ∑ h ∈ Sf,
      ((M : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)) + 1) := by
    push_cast
    refine Finset.sum_le_sum (fun h hh => ?_)
    rw [hSf, Finset.mem_filter] at hh
    obtain ⟨-, hne, -⟩ := hh
    have hb := qQ_fiber_le a b ha M n hne
    have hFF : F h = ((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ =>
        a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = n)).card := by
      rw [hF, hD]
    rw [hFF]
    have hcast : (((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ =>
        a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = n)).card : ℚ) ≤
        ((M / max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ) + 1 := by
      exact_mod_cast hb
    have hdiv : ((M / max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ) ≤
        (M : ℚ) / ((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ) := Nat.cast_div_le
    have hdiv' : ((M / max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ) ≤
        (M : ℚ) / max ((prim h 0).natAbs : ℚ) ((prim h 1).natAbs : ℚ) := by
      rw [← Nat.cast_max]
      exact hdiv
    linarith [hcast, hdiv']
  -- 拆分求和
  have h4 : (∑ h ∈ Sf, ((M : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)) + 1))
      = (M : ℚ) * (∑ h ∈ Sf,
          (1 : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)))
        + (∑ h ∈ Sf, (1 : ℚ)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [mul_one_div]
  have h5 : (∑ h ∈ Sf, (1 : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)))
      ≤ 8 * (H : ℚ) * sigmaMinusOne n.natAbs := by
    rw [hSf, hB]
    exact sum_inv_prim_le hn H
  have h6 : (∑ h ∈ Sf, (1 : ℚ)) ≤ 4 * (H : ℚ) * ((H : ℚ) + 1) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : Sf.card ≤ 4 * H * (H + 1) := by
      have hsub : Sf ⊆ B.filter (fun h : Fin 2 → ℤ => h ≠ 0) := by
        intro h hh
        rw [hSf, Finset.mem_filter] at hh
        exact Finset.mem_filter.mpr ⟨hh.1, hh.2.1⟩
      have hc1 : Sf.card ≤ (B.filter (fun h : Fin 2 → ℤ => h ≠ 0)).card :=
        Finset.card_le_card hsub
      rw [hB, card_box2_ne_zero H] at hc1
      refine le_trans hc1 ?_
      have hsq : (2 * H + 1) ^ 2 = 4 * H * (H + 1) + 1 := by ring
      rw [hsq, Nat.add_sub_cancel]
    exact_mod_cast hcard
  calc (qQ a b H M n : ℚ) = ((∑ h ∈ Sf, F h : ℕ) : ℚ) := by rw [hQ, h1, h2]
    _ ≤ ∑ h ∈ Sf, ((M : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)) + 1) := h3
    _ = (M : ℚ) * (∑ h ∈ Sf,
          (1 : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)))
        + (∑ h ∈ Sf, (1 : ℚ)) := h4
    _ ≤ (M : ℚ) * (8 * (H : ℚ) * sigmaMinusOne n.natAbs)
        + 4 * (H : ℚ) * ((H : ℚ) + 1) := by
        have hM : (0 : ℚ) ≤ (M : ℚ) := by positivity
        have hMA : (M : ℚ) * (∑ h ∈ Sf,
            (1 : ℚ) / (((max (prim h 0).natAbs (prim h 1).natAbs : ℕ) : ℚ)))
            ≤ (M : ℚ) * (8 * (H : ℚ) * sigmaMinusOne n.natAbs) :=
          mul_le_mul_of_nonneg_left h5 hM
        linarith [hMA, h6]
    _ = 4 * (H : ℚ) * ((H : ℚ) + 1)
        + 8 * (H : ℚ) * (M : ℚ) * sigmaMinusOne n.natAbs := by ring

/-! ## 第五部分：`qQ` 的对称性与零点界 -/

/-- 部分和的界常数 `K = 4N²|a| + 2N|b|`。 -/
def qK (a b : ℤ) (N : ℕ) : ℤ :=
  4 * (N : ℤ) ^ 2 * (a.natAbs : ℤ) + 2 * (N : ℤ) * (b.natAbs : ℤ)

/-- `qK` 非负。 -/
theorem qK_nonneg (a b : ℤ) (N : ℕ) : 0 ≤ qK a b N := by
  unfold qK
  positivity

/-- **部分和的范围**：`|qAval p| ≤ qK a b N`。 -/
theorem qAval_bound (a b : ℤ) (N : ℕ) {p : (Fin 2 → ℤ) × (Fin 2 → ℤ)}
    (hp : p ∈ qPbox2 N (2 * N)) : |qAval a b p| ≤ qK a b N := by
  have hp1 : p.1 ∈ box2 (-(N : ℤ)) (N : ℤ) := ((Finset.mem_product).mp hp).1
  have hp2 : p.2 ∈ box2 (0 : ℤ) ((2 * N : ℕ) : ℤ) := ((Finset.mem_product).mp hp).2
  rw [box2, Fintype.mem_piFinset] at hp1 hp2
  have hb1 : |p.1 0| ≤ (N : ℤ) := by
    have := Finset.mem_Icc.mp (hp1 0); rw [abs_le]; exact this
  have hb2 : |p.1 1| ≤ (N : ℤ) := by
    have := Finset.mem_Icc.mp (hp1 1); rw [abs_le]; exact this
  have hb3 : |p.2 0| ≤ (2 * N : ℕ) := by
    have := Finset.mem_Icc.mp (hp2 0)
    rw [abs_of_nonneg this.1]; exact_mod_cast this.2
  have hb4 : |p.2 1| ≤ (2 * N : ℕ) := by
    have := Finset.mem_Icc.mp (hp2 1)
    rw [abs_of_nonneg this.1]; exact_mod_cast this.2
  have hb3' : |p.2 0| ≤ 2 * (N : ℤ) := by push_cast at hb3 ⊢; linarith
  have hb4' : |p.2 1| ≤ 2 * (N : ℤ) := by push_cast at hb4 ⊢; linarith
  have haa : |a| = (a.natAbs : ℤ) := Int.abs_eq_natAbs a
  have hbb : |b| = (b.natAbs : ℤ) := Int.abs_eq_natAbs b
  unfold qAval qK
  calc |a * (p.1 0 * p.2 0 + p.1 1 * p.2 1) + b * (p.1 0 + p.1 1)|
      ≤ |a * (p.1 0 * p.2 0 + p.1 1 * p.2 1)| + |b * (p.1 0 + p.1 1)| := abs_add_le _ _
    _ = |a| * |p.1 0 * p.2 0 + p.1 1 * p.2 1| + |b| * |p.1 0 + p.1 1| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * (|p.1 0| * |p.2 0| + |p.1 1| * |p.2 1|) + |b| * (|p.1 0| + |p.1 1|) := by
        have e1 : |p.1 0 * p.2 0 + p.1 1 * p.2 1| ≤ |p.1 0| * |p.2 0| + |p.1 1| * |p.2 1| := by
          refine le_trans (abs_add_le _ _) ?_
          rw [abs_mul, abs_mul]
        have e2 : |p.1 0 + p.1 1| ≤ |p.1 0| + |p.1 1| := abs_add_le _ _
        have h1 := mul_le_mul_of_nonneg_left e1 (abs_nonneg a)
        have h2 := mul_le_mul_of_nonneg_left e2 (abs_nonneg b)
        linarith
    _ ≤ |a| * ((N : ℤ) * (2 * (N : ℤ)) + (N : ℤ) * (2 * (N : ℤ)))
          + |b| * ((N : ℤ) + (N : ℤ)) := by
        have h1 : |p.1 0| * |p.2 0| + |p.1 1| * |p.2 1|
            ≤ (N : ℤ) * (2 * (N : ℤ)) + (N : ℤ) * (2 * (N : ℤ)) := by
          have e1 := mul_le_mul hb1 hb3' (abs_nonneg _) (by positivity : (0:ℤ) ≤ N)
          have e2 := mul_le_mul hb2 hb4' (abs_nonneg _) (by positivity : (0:ℤ) ≤ N)
          linarith
        have h2 : |p.1 0| + |p.1 1| ≤ (N : ℤ) + (N : ℤ) := by linarith
        have e1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
        have e2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg b)
        linarith
    _ = 4 * (N : ℤ) ^ 2 * (a.natAbs : ℤ) + 2 * (N : ℤ) * (b.natAbs : ℤ) := by
        rw [haa, hbb]
        ring

/-- **`qQ` 的对称性**：`qQ(−n) = qQ(n)`。 -/
theorem qQ_neg (a b : ℤ) (H M : ℕ) (n : ℤ) : qQ a b H M (-n) = qQ a b H M n := by
  classical
  unfold qQ
  have hboxmem : ∀ p ∈ qPbox2 H M, (-p.1, p.2) ∈ qPbox2 H M := by
    intro p hp
    refine Finset.mem_product.mpr ⟨?_, (Finset.mem_product.mp hp).2⟩
    have hp1 : ∀ i, p.1 i ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
      have h := (Finset.mem_product.mp hp).1
      rw [box2, Fintype.mem_piFinset] at h
      exact h
    rw [box2, Fintype.mem_piFinset]
    intro i
    have hi := hp1 i
    rw [Finset.mem_Icc] at hi ⊢
    simp only [Pi.neg_apply]
    constructor <;> linarith [hi.1, hi.2]
  have hneg : ∀ p : (Fin 2 → ℤ) × (Fin 2 → ℤ), qAval a b (-p.1, p.2) = -qAval a b p := by
    intro p
    unfold qAval
    simp only [Pi.neg_apply]
    ring
  refine Finset.card_bij (fun p _ => (-p.1, p.2)) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hboxmem p hp.1, by rw [hneg, hp.2]; ring⟩
  · intro p _ q _ hpq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    exact Prod.ext (neg_inj.mp h1) h2
  · intro q hq
    rw [Finset.mem_filter] at hq
    refine ⟨(-q.1, q.2), ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hboxmem q hq.1, by rw [hneg, hq.2]⟩
    · simp
/-- **零点的一致界**：`qQ(0) ≤ (M+1)² + 4H(H+1)(M+1)`。 -/
theorem qQ_zero_le (a b : ℤ) (ha : a ≠ 0) (H M : ℕ) :
    qQ a b H M 0 ≤ (M + 1) ^ 2 + 4 * H * (H + 1) * (M + 1) := by
  classical
  rw [qQ_eq_sum_fiber]
  set B : Finset (Fin 2 → ℤ) := box2 (-(H : ℤ)) (H : ℤ) with hB
  set F : (Fin 2 → ℤ) → ℕ := fun h => ((box2 (0 : ℤ) (M : ℤ)).filter
    (fun m : Fin 2 → ℤ => a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = 0)).card with hF
  have h0mem : (0 : Fin 2 → ℤ) ∈ B := by
    rw [hB]
    exact mem_box2_of_abs_le (fun i => by simp)
  have hF0 : F 0 ≤ (M + 1) ^ 2 := by
    have hsub : (box2 (0 : ℤ) (M : ℤ)).filter
        (fun m : Fin 2 → ℤ => a * ((0 : Fin 2 → ℤ) 0 * m 0 + (0 : Fin 2 → ℤ) 1 * m 1)
          + b * ((0 : Fin 2 → ℤ) 0 + (0 : Fin 2 → ℤ) 1) = 0)
        ⊆ box2 (0 : ℤ) (M : ℤ) := Finset.filter_subset _ _
    have h1 : F 0 ≤ (box2 (0 : ℤ) (M : ℤ)).card := by
      rw [hF]
      exact Finset.card_le_card hsub
    rw [box2_zero_card] at h1
    exact h1
  have hpos : ∀ h : Fin 2 → ℤ, h ≠ 0 →
      1 ≤ max (prim h 0).natAbs (prim h 1).natAbs := by
    intro h hh
    have hpne : prim h ≠ 0 := by
      intro hp0
      apply hh
      funext i
      rw [h_eq_gcd_mul_prim h i, congrFun hp0 i]
      simp
    obtain ⟨i, hi⟩ : ∃ i, prim h i ≠ 0 := by
      by_contra hall
      apply hpne
      funext i
      by_contra hc
      exact hall ⟨i, hc⟩
    have h1 : 1 ≤ (prim h i).natAbs := Int.natAbs_pos.mpr hi
    fin_cases i
    · exact le_trans h1 (le_max_left _ _)
    · exact le_trans h1 (le_max_right _ _)
  have hFne : ∀ h ∈ B.erase (0 : Fin 2 → ℤ), F h ≤ M + 1 := by
    intro h hh
    rw [Finset.mem_erase] at hh
    obtain ⟨hne, hB⟩ := hh
    have hb := qQ_fiber_le a b ha M 0 hne
    have hFF : F h = ((box2 (0 : ℤ) (M : ℤ)).filter (fun m : Fin 2 → ℤ =>
        a * (h 0 * m 0 + h 1 * m 1) + b * (h 0 + h 1) = 0)).card := by
      rw [hF]
    rw [hFF]
    refine le_trans hb ?_
    have hp := hpos h hne
    have hd : M / max (prim h 0).natAbs (prim h 1).natAbs ≤ M := Nat.div_le_self M _
    omega
  have hsplit : (∑ h ∈ B, F h) = F 0 + ∑ h ∈ B.erase (0 : Fin 2 → ℤ), F h := by
    rw [add_comm]
    exact (Finset.sum_erase_add B F h0mem).symm
  rw [hsplit]
  have hcard : (B.erase (0 : Fin 2 → ℤ)).card = 4 * H * (H + 1) := by
    rw [Finset.card_erase_of_mem h0mem, hB, card_box2]
    have hsq : (2 * H + 1) ^ 2 = 4 * H * (H + 1) + 1 := by ring
    rw [hsq, Nat.add_sub_cancel]
  have hsum : (∑ h ∈ B.erase (0 : Fin 2 → ℤ), F h) ≤ (B.erase (0 : Fin 2 → ℤ)).card * (M + 1) := by
    calc (∑ h ∈ B.erase (0 : Fin 2 → ℤ), F h) ≤ (B.erase (0 : Fin 2 → ℤ)).card • (M + 1) :=
          Finset.sum_le_card_nsmul _ _ _ hFne
      _ = (B.erase (0 : Fin 2 → ℤ)).card * (M + 1) := by simp
  rw [hcard] at hsum
  linarith

/-! ## 第六部分：汇总 —— 八次矩的 `N⁶` 界 -/

/-- 对称区间的求和公式（`ℚ` 值）。 -/
theorem sum_Icc_symm_rat (K : ℤ) (hK : 0 ≤ K) (f : ℤ → ℚ) (hf : ∀ n, f (-n) = f n) :
    (∑ n ∈ Finset.Icc (-K) K, f n) = f 0 + 2 * ∑ n ∈ Finset.Icc (1 : ℤ) K, f n := by
  have hU1 : Finset.Icc (-K) (-1 : ℤ) ∪ Finset.Icc (0 : ℤ) K = Finset.Icc (-K) K := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hd1 : Disjoint (Finset.Icc (-K) (-1 : ℤ)) (Finset.Icc (0 : ℤ) K) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx hy
    omega
  have hU2 : ({0} : Finset ℤ) ∪ Finset.Icc (1 : ℤ) K = Finset.Icc (0 : ℤ) K := by
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hd2 : Disjoint ({0} : Finset ℤ) (Finset.Icc (1 : ℤ) K) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc] at hy
    omega
  have hneg : (∑ n ∈ Finset.Icc (-K) (-1 : ℤ), f n) = ∑ n ∈ Finset.Icc (1 : ℤ) K, f n := by
    have h1 : (∑ n ∈ Finset.Icc (-K) (-1 : ℤ), f n)
        = ∑ n ∈ Finset.Icc (1 : ℤ) K, f (-n) := by
      refine Finset.sum_bij (fun n _ => -n) ?_ ?_ ?_ ?_
      · intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro n1 hn1 n2 hn2 heq
        simp only [Finset.mem_Icc] at hn1 hn2
        omega
      · intro m hm
        simp only [Finset.mem_Icc] at hm
        exact ⟨-m, by simp only [Finset.mem_Icc]; omega, by simp⟩
      · intro n _
        simp
    rw [h1]
    exact Finset.sum_congr rfl (fun n _ => hf n)
  rw [← hU1, Finset.sum_union hd1, ← hU2, Finset.sum_union hd2,
    Finset.sum_singleton, hneg]
  ring

/-- `σ₋₁(0) = 0`。 -/
theorem sigmaMinusOne_zero : sigmaMinusOne 0 = 0 := by
  unfold sigmaMinusOne
  simp

/-- `Σ_{|n|≤K} σ₋₁(|n|) ≤ 4K`。 -/
theorem sum_sigmaMinusOne_Icc (K : ℤ) (hK : 0 ≤ K) :
    (∑ n ∈ Finset.Icc (-K) K, sigmaMinusOne n.natAbs) ≤ 4 * (K : ℚ) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, K = (k : ℤ) := ⟨K.toNat, (Int.toNat_of_nonneg hK).symm⟩
  rw [sum_Icc_symm_rat (k : ℤ) (by positivity)
    (fun n => sigmaMinusOne n.natAbs) (fun n => by rw [Int.natAbs_neg])]
  rw [Int.natAbs_zero, sigmaMinusOne_zero]
  rw [sum_int_Icc_eq_sum_nat_Icc k (fun m => sigmaMinusOne m)]
  have h := sum_sigmaMinusOne_le k
  push_cast
  linarith

/-- `Σ_{|n|≤K} σ₋₁(|n|)² ≤ 12K`。 -/
theorem sum_sigmaMinusOne_sq_Icc (K : ℤ) (hK : 0 ≤ K) :
    (∑ n ∈ Finset.Icc (-K) K, sigmaMinusOne n.natAbs ^ 2) ≤ 12 * (K : ℚ) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, K = (k : ℤ) := ⟨K.toNat, (Int.toNat_of_nonneg hK).symm⟩
  rw [sum_Icc_symm_rat (k : ℤ) (by positivity)
    (fun n => sigmaMinusOne n.natAbs ^ 2) (fun n => by rw [Int.natAbs_neg])]
  rw [Int.natAbs_zero, sigmaMinusOne_zero]
  rw [sum_int_Icc_eq_sum_nat_Icc k (fun m => sigmaMinusOne m ^ 2)]
  have h := sum_sigmaMinusOne_sq_le k
  push_cast
  linarith

/-- **主计数界**：`qHMCount ≤ Σ_n qQ(n)²`。 -/
theorem qHMCount_le_sum_sq (a b : ℤ) (N : ℕ) :
    qHMCount a b N ≤ ∑ n ∈ Finset.Icc (-(qK a b N)) (qK a b N),
      qQ a b N (2 * N) n ^ 2 := by
  refine le_trans (qHMCount_le_sum_qQ a b N (qK a b N) (fun p hp => qAval_bound a b N hp)) ?_
  refine Finset.sum_le_sum (fun n _ => ?_)
  rw [qQ_neg, sq]

/-- `Σ_n qQ(n)²` 的 `N⁶` 界。 -/
theorem sum_qQ_sq_le (a b : ℤ) (ha : a ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ((∑ n ∈ Finset.Icc (-(qK a b N)) (qK a b N), qQ a b N (2 * N) n ^ 2 : ℕ) : ℚ)
      ≤ 1000000 * ((2 * a.natAbs + b.natAbs + 1 : ℕ) : ℚ) * (N : ℚ) ^ 6 := by
  classical
  have hNq : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  set c : ℚ := ((2 * a.natAbs + b.natAbs + 1 : ℕ) : ℚ) with hc
  have hc1 : (1 : ℚ) ≤ c := by
    rw [hc]
    have : (1 : ℕ) ≤ 2 * a.natAbs + b.natAbs + 1 := by omega
    exact_mod_cast this
  have hcnn : (0 : ℚ) ≤ c := le_trans zero_le_one hc1
  set A : ℚ := 4 * (N : ℚ) * ((N : ℚ) + 1) with hA
  set B : ℚ := 16 * (N : ℚ) ^ 2 with hB
  set Kz : ℤ := qK a b N with hKz
  have hKz0 : 0 ≤ Kz := by rw [hKz]; exact qK_nonneg a b N
  have hAnn : (0 : ℚ) ≤ A := by rw [hA]; positivity
  have hBnn : (0 : ℚ) ≤ B := by rw [hB]; positivity
  -- 1) cast 与分拆
  have hcast : ((∑ n ∈ Finset.Icc (-Kz) Kz, qQ a b N (2 * N) n ^ 2 : ℕ) : ℚ)
      = ∑ n ∈ Finset.Icc (-Kz) Kz, (qQ a b N (2 * N) n : ℚ) ^ 2 := by
    push_cast
    ring
  have h0mem : (0 : ℤ) ∈ Finset.Icc (-Kz) Kz := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hsplit : (∑ n ∈ Finset.Icc (-Kz) Kz, (qQ a b N (2 * N) n : ℚ) ^ 2)
      = (qQ a b N (2 * N) 0 : ℚ) ^ 2
        + ∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (qQ a b N (2 * N) n : ℚ) ^ 2 := by
    rw [add_comm]
    exact (Finset.sum_erase_add _ _ h0mem).symm
  -- 2) n = 0 项
  have hQ0 : (qQ a b N (2 * N) 0 : ℚ) ^ 2 ≤ 1089 * (N : ℚ) ^ 6 := by
    have h1 : qQ a b N (2 * N) 0 ≤ (2 * N + 1) ^ 2 + 4 * N * (N + 1) * (2 * N + 1) :=
      qQ_zero_le a b ha N (2 * N)
    have h2 : (2 * N + 1) ^ 2 + 4 * N * (N + 1) * (2 * N + 1) ≤ 33 * N ^ 3 := by
      have h3 : (2 * (N : ℚ) + 1) ^ 2 + 4 * (N : ℚ) * ((N : ℚ) + 1) * (2 * (N : ℚ) + 1)
          ≤ 33 * (N : ℚ) ^ 3 := by
        nlinarith [hNq]
      exact_mod_cast h3
    have h4 : (qQ a b N (2 * N) 0 : ℚ) ≤ 33 * (N : ℚ) ^ 3 := by
      have h5 : qQ a b N (2 * N) 0 ≤ 33 * N ^ 3 := le_trans h1 h2
      exact_mod_cast h5
    calc (qQ a b N (2 * N) 0 : ℚ) ^ 2 ≤ (33 * (N : ℚ) ^ 3) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h4 2
      _ = 1089 * (N : ℚ) ^ 6 := by ring
  -- 3) 其余项 ≤ Σ (A + Bσ)²
  have hrest : (∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (qQ a b N (2 * N) n : ℚ) ^ 2)
      ≤ ∑ n ∈ Finset.Icc (-Kz) Kz, (A + B * sigmaMinusOne n.natAbs) ^ 2 := by
    have h1 : (∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (qQ a b N (2 * N) n : ℚ) ^ 2)
        ≤ ∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (A + B * sigmaMinusOne n.natAbs) ^ 2 := by
      refine Finset.sum_le_sum (fun n hn => ?_)
      rw [Finset.mem_erase] at hn
      obtain ⟨hn0, -⟩ := hn
      have hq := qQ_le_sigma a b ha N (2 * N) hn0
      have hAs : 4 * (N : ℚ) * ((N : ℚ) + 1) = A := by rw [hA]
      have hBs : 8 * (N : ℚ) * ((2 * N : ℕ) : ℚ) = B := by
        rw [hB]
        push_cast
        ring
      rw [hAs, hBs] at hq
      exact pow_le_pow_left₀ (by positivity) hq 2
    have h2 : (∑ n ∈ (Finset.Icc (-Kz) Kz).erase 0, (A + B * sigmaMinusOne n.natAbs) ^ 2)
        ≤ ∑ n ∈ Finset.Icc (-Kz) Kz, (A + B * sigmaMinusOne n.natAbs) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset (0 : ℤ) (Finset.Icc (-Kz) Kz)) (fun n _ _ => by positivity)
    linarith [h1, h2]
  -- 4) 展开 Σ (A + Bσ)²
  have hexp : (∑ n ∈ Finset.Icc (-Kz) Kz, (A + B * sigmaMinusOne n.natAbs) ^ 2)
      = ((2 * Kz + 1 : ℤ) : ℚ) * A ^ 2
        + 2 * A * B * (∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs)
        + B ^ 2 * (∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs ^ 2) := by
    have hpt : ∀ n : ℤ, (A + B * sigmaMinusOne n.natAbs) ^ 2
        = A ^ 2 + 2 * A * B * sigmaMinusOne n.natAbs
          + B ^ 2 * sigmaMinusOne n.natAbs ^ 2 := fun n => by ring
    rw [Finset.sum_congr rfl (fun n _ => hpt n)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hcK : ((Finset.Icc (-Kz) Kz).card : ℚ) = ((2 * Kz + 1 : ℤ) : ℚ) := by
      rw [Int.card_Icc]
      have h1 : Kz + 1 - (-Kz) = 2 * Kz + 1 := by ring
      rw [h1]
      have h2 : ((2 * Kz + 1).toNat : ℤ) = 2 * Kz + 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast h2
    have e1 : (∑ n ∈ Finset.Icc (-Kz) Kz, A ^ 2) = ((2 * Kz + 1 : ℤ) : ℚ) * A ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, hcK]
    have e2 : (∑ n ∈ Finset.Icc (-Kz) Kz, 2 * A * B * sigmaMinusOne n.natAbs)
        = 2 * A * B * ∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs := by
      rw [Finset.mul_sum]
    have e3 : (∑ n ∈ Finset.Icc (-Kz) Kz, B ^ 2 * sigmaMinusOne n.natAbs ^ 2)
        = B ^ 2 * ∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs ^ 2 := by
      rw [Finset.mul_sum]
    rw [e1, e2, e3]
  -- 5) 关键放缩
  have hcabs : c = 2 * |(a : ℚ)| + |(b : ℚ)| + 1 := by
    rw [hc]
    push_cast
    simp
  have hKz_ub : (Kz : ℚ) ≤ 2 * (N : ℚ) ^ 2 * c := by
    have hN1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    have ha0 : (0 : ℤ) ≤ (a.natAbs : ℤ) := Int.natCast_nonneg _
    have hb0 : (0 : ℤ) ≤ (b.natAbs : ℤ) := Int.natCast_nonneg _
    have hNle : (N : ℤ) ≤ (N : ℤ) ^ 2 := by nlinarith [hN1]
    have hKz_int : Kz ≤ 2 * (N : ℤ) ^ 2 * (2 * (a.natAbs : ℤ) + (b.natAbs : ℤ)) := by
      rw [hKz]
      unfold qK
      have hstep : 2 * (N : ℤ) * (b.natAbs : ℤ) ≤ 2 * (N : ℤ) ^ 2 * (b.natAbs : ℤ) := by
        nlinarith [mul_le_mul_of_nonneg_left hNle hb0]
      linarith
    have h1 : (Kz : ℚ) ≤ ((2 * (N : ℤ) ^ 2 * (2 * (a.natAbs : ℤ) + (b.natAbs : ℤ)) : ℤ) : ℚ) := by
      exact_mod_cast hKz_int
    have h2 : ((2 * (N : ℤ) ^ 2 * (2 * (a.natAbs : ℤ) + (b.natAbs : ℤ)) : ℤ) : ℚ)
        ≤ 2 * (N : ℚ) ^ 2 * c := by
      have hcast1 : ((2 * (N : ℤ) ^ 2 * (2 * (a.natAbs : ℤ) + (b.natAbs : ℤ)) : ℤ) : ℚ)
          = 2 * (N : ℚ) ^ 2 * (2 * |(a : ℚ)| + |(b : ℚ)|) := by
        push_cast
        simp
      rw [hcast1, hcabs]
      have hN2 : (0 : ℚ) ≤ (N : ℚ) ^ 2 := by positivity
      have hle : (2 * |(a : ℚ)| + |(b : ℚ)|)
          ≤ 2 * |(a : ℚ)| + |(b : ℚ)| + 1 := by linarith
      nlinarith [hle, hN2]
    linarith [h1, h2]
  have hK1 : ((2 * Kz + 1 : ℤ) : ℚ) ≤ 5 * (N : ℚ) ^ 2 * c := by
    have h1 : ((2 * Kz + 1 : ℤ) : ℚ) = 2 * (Kz : ℚ) + 1 := by push_cast; ring
    rw [h1]
    have hN2 : (1 : ℚ) ≤ (N : ℚ) ^ 2 := by nlinarith [hNq]
    nlinarith [hKz_ub, hN2, hcnn]
  have hA_ub : A ≤ 8 * (N : ℚ) ^ 2 := by
    rw [hA]
    nlinarith [hNq]
  have hA2 : A ^ 2 ≤ 64 * (N : ℚ) ^ 4 := by
    calc A ^ 2 ≤ (8 * (N : ℚ) ^ 2) ^ 2 := pow_le_pow_left₀ hAnn hA_ub 2
      _ = 64 * (N : ℚ) ^ 4 := by ring
  have hAB : A * B ≤ 128 * (N : ℚ) ^ 4 := by
    rw [hB]
    have h2 : A ≤ 8 * (N : ℚ) ^ 2 := hA_ub
    nlinarith [hAnn, hNq]
  have hB2 : B ^ 2 = 256 * (N : ℚ) ^ 4 := by
    rw [hB]
    ring
  -- 6) 主放缩
  have hmain : (∑ n ∈ Finset.Icc (-Kz) Kz, (A + B * sigmaMinusOne n.natAbs) ^ 2)
      ≤ 25000 * c * (N : ℚ) ^ 6 := by
    rw [hexp]
    have hs1 := sum_sigmaMinusOne_Icc Kz hKz0
    have hs2 := sum_sigmaMinusOne_sq_Icc Kz hKz0
    have e1 : 2 * A * B * (∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs)
        ≤ 2 * A * B * (4 * (Kz : ℚ)) := by
      apply mul_le_mul_of_nonneg_left hs1
      positivity
    have e2 : B ^ 2 * (∑ n ∈ Finset.Icc (-Kz) Kz, sigmaMinusOne n.natAbs ^ 2)
        ≤ B ^ 2 * (12 * (Kz : ℚ)) := by
      apply mul_le_mul_of_nonneg_left hs2
      positivity
    have hkey : ((2 * Kz + 1 : ℤ) : ℚ) * A ^ 2 + 2 * A * B * (4 * (Kz : ℚ))
        + B ^ 2 * (12 * (Kz : ℚ)) ≤ 25000 * c * (N : ℚ) ^ 6 := by
      have hAB2 : A * B ≤ 128 * (N : ℚ) ^ 4 := hAB
      have hKzq : (Kz : ℚ) ≤ 2 * (N : ℚ) ^ 2 * c := hKz_ub
      have h1 : ((2 * Kz + 1 : ℤ) : ℚ) * A ^ 2 ≤ (5 * (N : ℚ) ^ 2 * c) * (64 * (N : ℚ) ^ 4) := by
        apply mul_le_mul hK1 hA2 (by positivity) (by positivity)
      have h2 : 2 * A * B * (4 * (Kz : ℚ)) ≤ 8 * (128 * (N : ℚ) ^ 4) * (2 * (N : ℚ) ^ 2 * c) := by
        have hAB' : 2 * A * B * 4 ≤ 8 * (128 * (N : ℚ) ^ 4) := by
          nlinarith [hAB2]
        have h := mul_le_mul hAB' hKzq (by positivity) (by positivity)
        nlinarith [h]
      have h3 : B ^ 2 * (12 * (Kz : ℚ)) ≤ (256 * (N : ℚ) ^ 4) * (12 * (2 * (N : ℚ) ^ 2 * c)) := by
        rw [hB2]
        apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
        nlinarith [hKzq]
      have hN6 : (0 : ℚ) ≤ (N : ℚ) ^ 6 := by positivity
      nlinarith [h1, h2, h3, hcnn, hNq, hN6]
    nlinarith [e1, e2, hkey]
  -- 7) 汇总
  rw [hcast, hsplit]
  nlinarith [hQ0, hrest, hmain, hc1, hcnn, hNq]

/-- **Theorem 1（`k = 2`，一般二次形式）**：`qEqCount ≤ C·N⁶`。 -/
theorem qEqCount_le (a b : ℤ) (ha : a ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    qEqCount a b N ≤ 1000000 * (2 * a.natAbs + b.natAbs + 1) * N ^ 6 := by
  refine le_trans (le_trans (qEqCount_le_qHMCount a b N) (qHMCount_le_sum_sq a b N)) ?_
  have h := sum_qQ_sq_le a b ha N hN
  have h2 : ((1000000 * (2 * a.natAbs + b.natAbs + 1) * N ^ 6 : ℕ) : ℚ)
      = 1000000 * ((2 * a.natAbs + b.natAbs + 1 : ℕ) : ℚ) * (N : ℚ) ^ 6 := by
    push_cast
    ring
  rw [← h2] at h
  exact_mod_cast h

/-- **Theorem 1（`k = 2`，一般二次形式）的积分形式**：
`∫₀¹ |∑_{n≤N} e(α(a n² + b n))|⁸ dα ≤ 10⁶·(2|a|+|b|+1)·N⁶`。 -/
theorem integral_normSq_pow_four_le_q (a b : ℤ) (ha : a ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    (∫ α in (0 : ℝ)..1, (Complex.normSq (qSum a b N α)) ^ 4)
      ≤ 1000000 * ((2 * a.natAbs + b.natAbs + 1 : ℕ) : ℝ) * (N : ℝ) ^ 6 := by
  rw [integral_normSq_pow_four_q]
  have h := qEqCount_le a b ha N hN
  have h' : (qEqCount a b N : ℝ) ≤ ((1000000 * (2 * a.natAbs + b.natAbs + 1) * N ^ 6 : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h' ⊢
  exact h'

end Waring