import Mathlib
import NlsGge.Composition.LocalBounds

                                                                       
                                                                                                        
                                                                                                      
                                                                                                
                                                                                                         
                                                                        
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.R

def UniformSeriesBounds
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y) (K : Set X) (δ ρ M : ℝ) : Prop :=
  ∀ y ∈ Metric.thickening δ K,
    ∃ p : FormalMultilinearSeries ℝ X Y,
      HasFPowerSeriesOnBall F p y (ENNReal.ofReal ρ) ∧
      ∀ k : ℕ, ‖p k‖ ≤ M * (ρ⁻¹) ^ k

theorem exists_uniform_series_bounds
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (F : X → Y) (O K : Set X)
    (hO : IsOpen O) (hF : AnalyticOnNhd ℝ F O)
    (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ δ ρ M : ℝ, 0 < δ ∧ 0 < ρ ∧ 0 ≤ M ∧
      Metric.thickening δ K ⊆ O ∧
      UniformSeriesBounds F K δ ρ M := by
  obtain ⟨δ, ρ, M, hδ, hρ, hM, hsub, hser⟩ :=
    NlsGge.Composition.exists_uniform_series_bounds hO hF hK hKO
  exact ⟨δ, ρ, M, hδ, hρ, hM, hsub, hser⟩

end NlsGge.ThirdConsultation.R
