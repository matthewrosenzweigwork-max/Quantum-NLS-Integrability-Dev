import Mathlib
import NlsGge.Atomic.R.R023

                                                                                                                                                
                                                                                                                                                           
                                                                                                                                                                                                                                                                                                                                   
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators RealInnerProductSpace
namespace NlsGge.ThirdConsultation.R
noncomputable section

theorem projField_nullPres_eventually
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (K : RamerE c s → RamerH c) (hK : ContDiff ℝ 2 K)
    (x₀ : RamerE c s)
    (hInv : IsUnit (1 + (hsDerivH c s hs K x₀).toCLM)) :
    ∃ r : ℝ, 0 < r ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ A : Set (RamerE c s),
          ramerGaussian c s A = 0 →
          ramerGaussian c s
            (Metric.ball x₀ r ∩
              (TM c s hs (projField c s N K)) ⁻¹' A) = 0 :=
  NlsGge.Ramer.projField_nullPres_eventually c s hs K hK x₀ hInv

end
end NlsGge.ThirdConsultation.R
