import NlsGge.Weights.Size
import NlsGge.Definitions.PilotInterfaces

namespace NlsGge.ThirdConsultation.R

/-- Model size of the global signed symbol: `(1+|r|)^(-3/4) e^{4√|r|}`. -/
noncomputable def modelWeight (r : ℝ) : ℝ :=
  (1 + |r|) ^ (-3 / 4 : ℝ) * Real.exp (4 * Real.sqrt |r|)

/-- R-080: global signed symbol size including zero (wrapper over
`NlsGge.Weights.weight_two_sided_size`). Binding repair: `AdmittedCoefficients lower upper`
with the interval parameters before the coefficient sequence; constants before `coeff`. -/
theorem weight_two_sided_size (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) :
    ∃ c C : ℝ, 0 < C ∧ ∀ coeff : ℕ → ℝ,
      NlsGge.Pilot.AdmittedCoefficients lower upper coeff → ∀ r : ℝ,
        c * modelWeight r ≤ NlsGge.Weights.weight coeff r ∧
          NlsGge.Weights.weight coeff r ≤ C * modelWeight r := by
  obtain ⟨A, B, _hA, hB, h⟩ :=
    NlsGge.Weights.weight_two_sided_size lower upper hlower hlower_upper
  refine ⟨A, B, hB, fun coeff hc r => ?_⟩
  obtain ⟨-, -, hb⟩ := hc
  have hb' := h coeff (fun j => (hb j).1) (fun j => (hb j).2) r
  unfold modelWeight
  exact ⟨by rw [← mul_assoc]; exact hb'.1, by rw [← mul_assoc]; exact hb'.2⟩

end NlsGge.ThirdConsultation.R
