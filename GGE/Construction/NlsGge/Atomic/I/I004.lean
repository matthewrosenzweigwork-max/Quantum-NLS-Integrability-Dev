import NlsGge.Weights.Regularity
import NlsGge.Weights.Entire
import NlsGge.Sobolev.SourceWeighted

                                                                                                    
                                                                                                                  
                                                                                             
                                                            

set_option autoImplicit false

open NlsGge.Pilot NlsGge.Weights

namespace NlsGge.ThirdConsultation.I
noncomputable section

theorem i004 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (r : ℝ) (hr : 0 < r) :
    (∀ j : ℕ, 0 ≤ probabilityTerm c.val r j) ∧
    HasSum (probabilityTerm c.val r) 1 ∧
    Summable (fun j : ℕ => (j : ℝ) ^ 4 * probabilityTerm c.val r j) ∧
    (∑' j : ℕ, (j : ℝ) ^ 4 * probabilityTerm c.val r j) ≤
      (upper / lower) * r ^ 2 ∧
    (∀ m : ℕ,
      (∑ j ∈ Finset.range (m + 1), partialProbabilityTerm c.val m r j) = 1 ∧
      (∑ j ∈ Finset.range (m + 1),
        (j : ℝ) ^ 4 * partialProbabilityTerm c.val m r j) ≤
        (upper / lower) * r ^ 2) ∧
    (∑ j ∈ Finset.range 1,
      (j : ℝ) ^ 4 * partialProbabilityTerm c.val 0 r j) = 0 := by
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  refine ⟨fun j => probabilityTerm_nonneg lower upper c.val hl hb' hu' r j,
    probabilityTerm_hasSum lower upper c.val hl hb' hu' r,
    probabilityTerm_fourthMoment_summable lower upper c.val hl hb' hu' r,
    probabilityTerm_fourthMoment_le lower upper c.val hl hb' hu' r,
    fun m => ⟨partialProbabilityTerm_sum lower c.val hl hb' m r,
      partialProbabilityTerm_fourthMoment lower upper c.val hl hb' hu' m r⟩, ?_⟩
  simp

end
end NlsGge.ThirdConsultation.I
