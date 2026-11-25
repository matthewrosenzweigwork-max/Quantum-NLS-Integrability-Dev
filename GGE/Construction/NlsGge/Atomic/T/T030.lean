                                                                                                                           
                                                                                                                                
                                                                                                                                       
                                                                             
import Mathlib
import NlsGge.Birkhoff.W12Tilt38

set_option autoImplicit false

namespace NlsGge.ThirdConsultation.T
noncomputable section

def lowerWeightTiltProduct {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (δ : ℝ) : ℝ :=
  NlsGge.Birkhoff.Dtilt38 c.val δ

theorem lowerWeightTilt_product_positive
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ : δ * upper < lower) :
    Summable (fun n : ℤ =>
      δ * NlsGge.Birkhoff.bRate38 c.val n /
        NlsGge.Measure.fullWeightRate c.val n) ∧
    (∀ n : ℤ,
      0 ≤ δ * NlsGge.Birkhoff.bRate38 c.val n /
        NlsGge.Measure.fullWeightRate c.val n ∧
      δ * NlsGge.Birkhoff.bRate38 c.val n /
        NlsGge.Measure.fullWeightRate c.val n < 1) ∧
    0 < lowerWeightTiltProduct c δ ∧
    HasProd (fun n : ℤ =>
      1 - δ * NlsGge.Birkhoff.bRate38 c.val n /
        NlsGge.Measure.fullWeightRate c.val n)
      (lowerWeightTiltProduct c δ) := by
  have hpr := NlsGge.Birkhoff.hasProd_tilt38 c hδ0 hδ
  exact ⟨NlsGge.Birkhoff.summable_tiltRatio38 c δ,
    fun n => ⟨NlsGge.Birkhoff.tiltRatio38_nonneg c hδ0 n,
      NlsGge.Birkhoff.tiltRatio38_lt_one c hδ0 hδ n⟩,
    hpr.1, hpr.2⟩

theorem lowerWeightTilt_deficits_quarter
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ : δ * upper < lower / 4) :
    ∀ n : ℤ,
      δ * NlsGge.Birkhoff.bRate38 c.val n /
        NlsGge.Measure.fullWeightRate c.val n ∈ Set.Icc 0 (1 / 4 : ℝ) := by
  intro n
  have hlpos : 0 < lower := c.2.1
  have h1 := NlsGge.Birkhoff.tiltRatio38_le38 c hδ0 n
  have h2 : δ * (upper / lower) ≤ 1 / 4 := by
    rw [← mul_div_assoc, div_le_iff₀ hlpos]
    linarith
  exact Set.mem_Icc.2 ⟨NlsGge.Birkhoff.tiltRatio38_nonneg c hδ0 n, h1.trans h2⟩

theorem lowerWeightTilt_zero_mode
    (lower upper : ℝ)
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ : δ * upper < lower) :
    NlsGge.Birkhoff.bRate38 c.val 0 = NlsGge.coefficient c.val 1 ∧
    NlsGge.Measure.fullWeightRate c.val 0 = NlsGge.coefficient c.val 0 ∧
    0 < 1 - δ * NlsGge.coefficient c.val 1 /
      NlsGge.coefficient c.val 0 := by
  have hfw : ∀ d : ℕ → ℝ, NlsGge.Measure.fullWeightRate d 0 = d 0 := by
    intro d
    unfold NlsGge.Measure.fullWeightRate
    simp only [Int.cast_zero, mul_zero]
    exact NlsGge.Weights.weight_at_zero d
  have hb0 : NlsGge.Birkhoff.bRate38 c.val 0 = c.val 1 := by
    unfold NlsGge.Birkhoff.bRate38
    rw [hfw]
    simp [NlsGge.Birkhoff.bCoef38]
  have hc1 : NlsGge.coefficient c.val 1 = c.val 1 := by
    simp [NlsGge.coefficient]
  have hc0 : NlsGge.coefficient c.val 0 = c.val 0 := by
    simp [NlsGge.coefficient]
  have hlow0 : lower ≤ c.val 0 := (c.2.2.2 0).1
  have hup1 : c.val 1 ≤ upper := (c.2.2.2 1).2
  have hlpos : 0 < lower := c.2.1
  have hc0pos : 0 < c.val 0 := lt_of_lt_of_le hlpos hlow0
  refine ⟨by rw [hb0, hc1], ?_, ?_⟩
  · rw [hfw, hc0]
  · rw [hc1, hc0]
    have hprod : δ * c.val 1 < c.val 0 := by
      have : δ * c.val 1 ≤ δ * upper := mul_le_mul_of_nonneg_left hup1 hδ0.le
      linarith
    have hq : δ * c.val 1 / c.val 0 < 1 := (div_lt_one hc0pos).2 hprod
    linarith

end
end NlsGge.ThirdConsultation.T
#print axioms NlsGge.ThirdConsultation.T.lowerWeightTilt_product_positive
#print axioms NlsGge.ThirdConsultation.T.lowerWeightTilt_deficits_quarter
#print axioms NlsGge.ThirdConsultation.T.lowerWeightTilt_zero_mode
