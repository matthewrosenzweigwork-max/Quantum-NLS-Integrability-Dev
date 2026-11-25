import Mathlib
import NlsGge.ThirdConsultation.M.M031Host
import NlsGge.ThirdConsultation.M.M022Host

   
                                                                                                     

                                                                                                                  
                                                                                                           
                                                                               
                                                                           
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

/-- The submultiplicative factor of `sourceH1Weight`. -/
def sourceH1Factor (k : ℤ) : ℝ := (1 + Real.pi * |(k : ℝ)|) / (1 + |(k : ℝ)|)

theorem one_le_sourceH1Factor (k : ℤ) : 1 ≤ sourceH1Factor k := by
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have ha := abs_nonneg (k : ℝ)
  unfold sourceH1Factor
  rw [one_le_div (by positivity)]
  nlinarith

theorem sourceH1Factor_neg (k : ℤ) : sourceH1Factor (-k) = sourceH1Factor k := by
  unfold sourceH1Factor
  rw [Int.cast_neg, abs_neg]

/-- Monotonicity in the modulus and the product inequality. -/
theorem sourceH1Factor_le_mul (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcab : c ≤ a + b) :
    (1 + Real.pi * c) / (1 + c) ≤
      ((1 + Real.pi * a) / (1 + a)) * ((1 + Real.pi * b) / (1 + b)) := by
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (1 + Real.pi * c) * (1 + (a + b)) ≤ (1 + Real.pi * (a + b)) * (1 + c) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hpi) (sub_nonneg.2 hcab)]
  have h2 : (1 + Real.pi * (a + b)) * ((1 + a) * (1 + b)) ≤
      ((1 + Real.pi * a) * (1 + Real.pi * b)) * (1 + (a + b)) := by
    have hab : 0 ≤ a * b := mul_nonneg ha hb
    have hp2 : 0 ≤ Real.pi ^ 2 - 1 := by nlinarith
    have hp3 : 0 ≤ Real.pi ^ 2 - Real.pi := by nlinarith
    nlinarith [mul_nonneg hab hp2, mul_nonneg (mul_nonneg hab hp3) (add_nonneg ha hb)]
  have hpos : 0 ≤ (1 + a) * (1 + b) := by positivity
  have hposc : 0 ≤ 1 + c := by positivity
  calc (1 + Real.pi * c) * ((1 + a) * (1 + b))
      ≤ (1 + Real.pi * c) * ((1 + a) * (1 + b)) * 1 := le_of_eq (mul_one _).symm
    _ = ((1 + Real.pi * c) * (1 + (a + b))) * ((1 + a) * (1 + b)) / (1 + (a + b)) := by
        field_simp
    _ ≤ ((1 + Real.pi * (a + b)) * (1 + c)) * ((1 + a) * (1 + b)) / (1 + (a + b)) := by
        gcongr
    _ = ((1 + Real.pi * (a + b)) * ((1 + a) * (1 + b))) * (1 + c) / (1 + (a + b)) := by ring
    _ ≤ (((1 + Real.pi * a) * (1 + Real.pi * b)) * (1 + (a + b))) * (1 + c) / (1 + (a + b)) := by
        gcongr
    _ = (1 + Real.pi * a) * (1 + Real.pi * b) * (1 + c) := by
        field_simp

theorem sourceH1Factor_submultiplicative :
    NlsGge.Atomic.DM046.SubmultiplicativeWeight sourceH1Factor := by
  intro k l
  unfold sourceH1Factor
  have hcab : |((k + l : ℤ) : ℝ)| ≤ |(k : ℝ)| + |(l : ℝ)| := by
    rw [Int.cast_add]; exact abs_add_le _ _
  exact sourceH1Factor_le_mul _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hcab

theorem sourceH1Weight_eq (k : ℤ) :
    sourceH1Weight k = NlsGge.Atomic.M.M054.indexWeight k * sourceH1Factor k := by
  unfold sourceH1Weight sourceH1Factor NlsGge.Atomic.M.M054.indexWeight
  have hpos : (0 : ℝ) < 1 + |(k : ℝ)| := by positivity
  rw [abs_mul, abs_of_pos Real.pi_pos]
  field_simp

/-- Pro round 14 (M-031) producer obligation: the source H1 weight is a one-derivative weight. -/
theorem oneDerivativeWeight_sourceH1Weight : OneDerivativeWeight sourceH1Weight :=
  ⟨sourceH1Factor, one_le_sourceH1Factor, sourceH1Factor_neg,
    sourceH1Factor_submultiplicative, sourceH1Weight_eq⟩

end NlsGge.ThirdConsultation.M

end
