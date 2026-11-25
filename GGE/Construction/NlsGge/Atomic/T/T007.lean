import NlsGge.Hierarchy.ExponentialH2Moment38
import NlsGge.Birkhoff.F09Limit38d
import NlsGge.ThirdConsultation.T.ECarrier98
import NlsGge.Atomic.T.T005

                                                                                             
                                                                                                                     
                                                                                                     
                                                                                                        
                                                                                                   
                                                                                                           
                                                                                                           
                                                                                                         

set_option autoImplicit false
open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.T

theorem localizedTest_removal_error
    (lower upper : ℝ) (hlower : 0 < lower) (hupper : lower ≤ upper) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (c : BoundedCoefficients lower upper) (s : ℝ),
        (1 : ℝ) / 2 < s →
        ∀ (N : ℕ) (R : ℝ), 0 ≤ R →
          ∀ (F : BoundedContinuousFunction (ECarrier38 c s) ℝ)
            (χ : ECarrier38 c s → ℝ),
            Measurable χ →
            (∀ y : ECarrier38 c s, 0 ≤ χ y ∧ χ y ≤ 1) →
            (∀ y : ECarrier38 c s,
              ‖eToSob38 c s 2 y‖ ≤ R → χ y = 1) →
            Integrable
              (fun x : ECarrier38 c s =>
                F (projE38 c s N x) * fN38 c s N x)
              (fullWeightedSequenceGaussian c s) ∧
            Integrable
              (fun x : ECarrier38 c s =>
                F (projE38 c s N x) * χ (projE38 c s N x) *
                  fN38 c s N x)
              (fullWeightedSequenceGaussian c s) ∧
            |unnormalizedTest c s (fun y => F y) N -
              unnormalizedTest c s (fun y => F y * χ y) N| ≤
                C * ‖F‖ * Real.exp (-(η * R ^ 2)) := by
  obtain ⟨η, C, hη, hC, H⟩ := fullFourier_common_producer98 lower upper hlower hupper
  exact ⟨η, C, hη, hC, fun c s hs N R hR F χ hχm hχb hχ1 =>
    (H c s hs N).2.2 R hR F χ hχm hχb hχ1⟩

end NlsGge.ThirdConsultation.T
