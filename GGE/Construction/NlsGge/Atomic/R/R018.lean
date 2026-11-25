import Mathlib
import NlsGge.Ramer.FiniteDivergenceL2
import NlsGge.Ramer.FiniteDivergenceGrowth
import NlsGge.ThirdConsultation.R.ExpGrowth018C

                                                                                                         
                                                                                                         
                                                                                            
                                                                                                             
                                                                                                       
set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace NlsGge.ThirdConsultation.R
noncomputable section

def GaussianC2AdmissibleField
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : V → V) : Prop :=
  ContDiff ℝ 2 F ∧
    ∃ C : ℝ, 0 < C ∧ ∀ x : V,
      ‖F x‖ + ‖fderiv ℝ F x‖ +
          ‖fderiv ℝ (fun y : V => fderiv ℝ F y) x‖ ≤
        C * Real.exp (C * ‖x‖)

abbrev GaussianFiniteCarrier (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem integral_sq_finiteGaussianDivergence
    (d : ℕ) (F : GaussianFiniteCarrier d → GaussianFiniteCarrier d)
    (hF : GaussianC2AdmissibleField F) :
    (∫ x : GaussianFiniteCarrier d,
        (NlsGge.Ramer.finiteGaussianDivergence F x) ^ 2
        ∂NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) =
      (∫ x : GaussianFiniteCarrier d, ‖F x‖ ^ 2
        ∂NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) +
      (∫ x : GaussianFiniteCarrier d,
        NlsGge.Ramer.traceCLM (GaussianFiniteCarrier d)
          ((fderiv ℝ F x).comp (fderiv ℝ F x))
        ∂NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)) := by
  obtain ⟨hF2, C, hC, hbd⟩ := hF
  have hFg : ∀ x, ‖F x‖ ≤ C * Real.exp (C * ‖x‖) := fun x => by
    have h1 := hbd x
    have h2 := norm_nonneg (fderiv ℝ F x)
    have h3 := norm_nonneg (fderiv ℝ (fun y : GaussianFiniteCarrier d => fderiv ℝ F y) x)
    linarith
  have hDg : ∀ x, ‖fderiv ℝ F x‖ ≤ C * Real.exp (C * ‖x‖) := fun x => by
    have h1 := hbd x
    have h2 := norm_nonneg (F x)
    have h3 := norm_nonneg (fderiv ℝ (fun y : GaussianFiniteCarrier d => fderiv ℝ F y) x)
    linarith
  exact (NlsGge.ThirdConsultation.R.integral_sq_finiteGaussianDivergence_expGrowth hF2 hC hFg hDg).2.2.2

end
end NlsGge.ThirdConsultation.R
