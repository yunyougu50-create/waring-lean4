import WaringQuadSum

open Finset

namespace Waring

#print axioms integral_sum_pow_four
#print axioms pointwise_expand
#print axioms integral_compute
#print axioms TN_pack
#print axioms mul_four_finset
#print axioms dshift_polyEval
#print axioms Qsum_polyEval

-- 主定理的精确陈述
#check @integral_sum_pow_four

-- 条件形式是 `Σ Qᵢ = 0`（无 h 加权）
example (f : ℤ → ℤ) (N : ℕ) (s : ℕ) (hs : 1 ≤ s) :
    (∫ α in (0:ℝ)..1,
      (∑ h ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0, ‖T f N α h‖ ^ (2*s)) ^ 4)
      = ∑ h1 ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0,
        ∑ h2 ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0,
        ∑ h3 ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0,
        ∑ h4 ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0,
        ∑ Q1 ∈ QSet f N h1 s, ∑ Q2 ∈ QSet f N h2 s,
        ∑ Q3 ∈ QSet f N h3 s, ∑ Q4 ∈ QSet f N h4 s,
          (if Q1 + Q2 + Q3 + Q4 = 0 then
            (BCount f N h1 s Q1 * BCount f N h2 s Q2 * BCount f N h3 s Q3
              * BCount f N h4 s Q4 : ℝ)
          else 0) :=
  integral_sum_pow_four f N s hs

-- 桥接：多项式情形频率是 `h·φ`
example (a : ℕ → ℤ) (d : ℕ) (h : ℤ) (n : ℕ) :
    dshift (polyEval a d) h n = h * polyEval (diffCoeff a d h) d (n : ℤ) :=
  dshift_polyEval a d h n

end Waring
