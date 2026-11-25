import NlsGge.Atomic.R.R076

                                                                                                                
                                                                                                                  
                                                                                                     
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.R
noncomputable section

theorem probabilityTerm_uniform_firstSecondMoments (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℕ → ℝ, NlsGge.Pilot.AdmittedCoefficients lower upper c →
      ∀ t : ℝ, 4 ≤ t →
        Summable (fun j : ℕ => (j : ℝ) * tiltedPoissonFourth c t j) ∧
        Summable (fun j : ℕ => (j : ℝ) ^ 2 * tiltedPoissonFourth c t j) ∧
        |meanJ c t - t| ≤ C * Real.sqrt t ∧
        |meanJ2 c t - t ^ 2| ≤ C * Real.rpow t (3 / 2 : ℝ) := by
  obtain ⟨C, hC, h⟩ :=
    NlsGge.Weights.probabilityTerm_uniform_firstSecondMoments lower upper hlower hlower_upper
  refine ⟨C, hC, fun c hc t ht => ?_⟩
  have hc' := hc
  obtain ⟨hlo, -, hbd⟩ := hc
  have hb1 : ∀ j : ℕ, lower ≤ c j := fun j => (hbd j).1
  have hb2 : ∀ j : ℕ, c j ≤ upper := fun j => (hbd j).2
  have ht0 : 0 ≤ t := by linarith
  have hid := (tiltedPoissonFourth_probabilityTerm lower upper c hc' t ht0).2.2.1
  have h1 : (fun j : ℕ => (j : ℝ) * tiltedPoissonFourth c t j) =
      fun j : ℕ => (j : ℝ) * NlsGge.Weights.probabilityTerm c (t ^ 2) j :=
    funext fun j => by rw [hid j]
  have h2 : (fun j : ℕ => (j : ℝ) ^ 2 * tiltedPoissonFourth c t j) =
      fun j : ℕ => (j : ℝ) ^ 2 * NlsGge.Weights.probabilityTerm c (t ^ 2) j :=
    funext fun j => by rw [hid j]
  have hm1 : meanJ c t = ∑' j : ℕ, (j : ℝ) * NlsGge.Weights.probabilityTerm c (t ^ 2) j := by
    unfold meanJ; rw [h1]
  have hm2 : meanJ2 c t = ∑' j : ℕ, (j : ℝ) ^ 2 * NlsGge.Weights.probabilityTerm c (t ^ 2) j := by
    unfold meanJ2; rw [h2]
  obtain ⟨k1, k2⟩ := (h c hb1 hb2 t ht)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]
    refine ((NlsGge.Weights.firstMoment_summable lower upper c hlo hb1 hb2 (t ^ 2)).div_const
      (NlsGge.Weights.weight c (t ^ 2))).congr fun j => ?_
    unfold NlsGge.Weights.probabilityTerm; ring
  · rw [h2]; exact NlsGge.Weights.probabilityTerm_secondMoment_summable lower upper c hlo hb1 hb2 (t ^ 2)
  · rw [hm1]; exact k1
  · rw [hm2]; exact k2

end
end NlsGge.ThirdConsultation.R
