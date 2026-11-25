import NlsGge.Ramer.LocalBump

                                                                                                                      
                                                                                               
                                                                                                          
                                                                                                             
                                                                                          
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.R
noncomputable section

def BoundedFieldAndDerivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) : Prop :=
  ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C ∧ ‖fderiv ℝ f x‖ ≤ C

theorem r022_exists_bumped_field {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (K : E → H) (hK : ContDiff ℝ 2 K) (x₀ : E) :
    ∃ r > 0, ∃ G : E → H, ContDiff ℝ 2 G ∧ Set.EqOn G K (Metric.ball x₀ r) ∧
      BoundedFieldAndDerivative G := by
  obtain ⟨r, hr, G, B, hG, hGb, hfd, hEq⟩ := NlsGge.Ramer.exists_bumped_field_generic K hK x₀
  exact ⟨r, hr, G, hG, hEq, B, fun x => ⟨hGb x, hfd x⟩⟩

end
end NlsGge.ThirdConsultation.R
