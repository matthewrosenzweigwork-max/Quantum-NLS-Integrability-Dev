import NlsGge.Weights.LowerGrowth
import NlsGge.Sobolev.SourceWeighted

                                                                                                                
                                                                                               
                                                                                                       
                                                       

set_option autoImplicit false

open NlsGge NlsGge.Pilot NlsGge.Weights

namespace NlsGge.ThirdConsultation.I
noncomputable section

theorem i006 (lower upper : ℝ) (hlower : 0 < lower) (hle : lower ≤ upper) :
    ∃ growth : ℝ, 0 < growth ∧
      ∀ c : BoundedCoefficients lower upper, ∀ r : ℝ, 16 ≤ r →
        let j : ℕ := lowerGrowthIndex r
        Real.sqrt r / 4 ≤ (j : ℝ) ∧ (j : ℝ) ≤ Real.sqrt r / 2 ∧
        (j.factorial : ℝ) ≤ (j : ℝ) ^ j ∧
        lower * (16 : ℝ) ^ j ≤ weightTerm c.val r j ∧
        growth * Real.exp (growth * Real.sqrt r) ≤ weight c.val r := by
  obtain ⟨g, hg, hgb⟩ := weight_uniform_lower_growth lower upper hlower hle
  refine ⟨g, hg, fun c r hr => ?_⟩
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  obtain ⟨h1, h2⟩ := lowerGrowthIndex_bounds r hr
  intro j
  have hr0 : 0 ≤ r := by linarith
  have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0
  have hsn : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hj4 : 4 * (j : ℝ) ^ 2 ≤ r := by
    have hsq : (j : ℝ) * (j : ℝ) ≤ (Real.sqrt r / 2) * (Real.sqrt r / 2) :=
      mul_le_mul h2 h2 hj0 (by positivity)
    nlinarith [hsq, hs]
  exact ⟨h1, h2, by exact_mod_cast Nat.factorial_le_pow j,
    weightTerm_lower_geometric lower c.val hl hb' r hr0 j hj4,
    hgb c.val hb' hu' r hr⟩

end
end NlsGge.ThirdConsultation.I
