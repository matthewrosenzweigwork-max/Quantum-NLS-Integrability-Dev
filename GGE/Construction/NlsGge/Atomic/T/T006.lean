import NlsGge.Hierarchy.ExponentialH2Moment38
import NlsGge.Birkhoff.F09Limit38d
import NlsGge.ThirdConsultation.T.ECarrier98
import NlsGge.Atomic.T.T005

                                                                                             
                                                                                                                     
                                                                                                          
                                                                                            

set_option autoImplicit false
open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.T

theorem fullFourier_unnormalized_H2_tail
    (lower upper : ℝ) (hlower : 0 < lower) (hupper : lower ≤ upper) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (c : BoundedCoefficients lower upper) (s : ℝ),
        (1 : ℝ) / 2 < s → ∀ N : ℕ,
          (Integrable
            (fun x : ECarrier38 c s =>
              fN38 c s N x * Real.exp
                (η * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2))
            (fullWeightedSequenceGaussian c s) ∧
           (∫ x : ECarrier38 c s,
             fN38 c s N x * Real.exp
               (η * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2)
               ∂fullWeightedSequenceGaussian c s) ≤ C) ∧
          ∀ R : ℝ, 0 ≤ R →
            Integrable
              ((tailSet38 c s N R).indicator (fN38 c s N))
              (fullWeightedSequenceGaussian c s) ∧
            (∫ x : ECarrier38 c s,
              (tailSet38 c s N R).indicator (fN38 c s N) x
                ∂fullWeightedSequenceGaussian c s) ≤
                  C * Real.exp (-(η * R ^ 2)) := by
  obtain ⟨η, C, hη, hC, H⟩ := fullFourier_common_producer98 lower upper hlower hupper
  exact ⟨η, C, hη, hC, fun c s hs N => ⟨(H c s hs N).1, (H c s hs N).2.1⟩⟩

end NlsGge.ThirdConsultation.T
