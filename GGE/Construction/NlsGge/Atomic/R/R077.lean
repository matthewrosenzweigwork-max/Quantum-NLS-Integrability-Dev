import NlsGge.Atomic.R.R076

                                                                                                                
                                                                                                                  
                                                                                                     
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.R
noncomputable section

theorem probabilityTerm_uniform_centeredSecondMoment (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℕ → ℝ, NlsGge.Pilot.AdmittedCoefficients lower upper c →
      ∀ t : ℝ, 4 ≤ t →
        Summable (fun j : ℕ => ((j : ℝ) - t) ^ 2 * tiltedPoissonFourth c t j) ∧
        (∑' j : ℕ, ((j : ℝ) - t) ^ 2 * tiltedPoissonFourth c t j) ≤ C * t := by
  obtain ⟨C, hC, h⟩ :=
    NlsGge.Weights.probabilityTerm_uniform_centeredSecondMoment lower upper hlower hlower_upper
  refine ⟨C, hC, fun c hc t ht => ?_⟩
  have hc' := hc
  obtain ⟨hlo, -, hbd⟩ := hc
  have hb1 : ∀ j : ℕ, lower ≤ c j := fun j => (hbd j).1
  have hb2 : ∀ j : ℕ, c j ≤ upper := fun j => (hbd j).2
  have ht0 : 0 ≤ t := by linarith
  have hfun : (fun j : ℕ => ((j : ℝ) - t) ^ 2 * tiltedPoissonFourth c t j) =
      fun j : ℕ => ((j : ℝ) - t) ^ 2 * NlsGge.Weights.probabilityTerm c (t ^ 2) j :=
    funext fun j => by
      rw [(tiltedPoissonFourth_probabilityTerm lower upper c hc' t ht0).2.2.1 j]
  have hsum : (∑' j : ℕ, ((j : ℝ) - t) ^ 2 * tiltedPoissonFourth c t j) =
      ∑' j : ℕ, ((j : ℝ) - t) ^ 2 * NlsGge.Weights.probabilityTerm c (t ^ 2) j := by
    rw [hfun]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact NlsGge.Weights.probabilityTerm_centeredSecondMoment_summable lower upper c hlo hb1 hb2 t ht0
  · rw [hsum]
    exact h c hb1 hb2 t ht

end
end NlsGge.ThirdConsultation.R
