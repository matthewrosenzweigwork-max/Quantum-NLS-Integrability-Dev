import Mathlib
import NlsGge.Atomic.I.I041Core
import NlsGge.ThirdConsultation.I.ActualInverseBridge

                                                                                                     
                                                                          
                                                                                                      
                                                                                                             
                         
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

theorem i041 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    (∀ (g : ℤ → ℂ) (n : ℤ),
      fullWeightRate c.val n * ‖zFull38 c.val g n‖ ^ 2 = ‖g n‖ ^ 2 ∧
      ∀ m : ℕ, hierRate38 c.val m n * ‖zHier38 c.val m g n‖ ^ 2 = ‖g n‖ ^ 2) ∧
    (∫⁻ g : ℤ → ℂ, ∑' n : ℤ, ENNReal.ofReal
      (‖g n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ)) ∂stdGauss38) =
      ∑' n : ℤ, ENNReal.ofReal (japaneseBracket n ^ (-3 / 2 : ℝ)) ∧
    (∫⁻ g : ℤ → ℂ, ∑' n : ℤ, ENNReal.ofReal
      (‖g n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ)) ∂stdGauss38) < ⊤ ∧
    ∀ g ∈ Omega1_38 c.val,
      Summable (fun n : ℤ => ‖g n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ,
        |gapRemainderTermE02_38 (weight c.val) (physicalOfSequence (zFull38 c.val g)) n| ≤
          C * ‖g n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ) ∧
        ∀ m : ℕ, 2 ≤ m →
          |gapRemainderTermE02_38 (partialWeight c.val m)
            (physicalOfSequence (zHier38 c.val m g)) n| ≤
              C * ‖g n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ) :=
  NlsGge.ThirdConsultation.I041C.i041_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence lower upper c

end NlsGge.ThirdConsultation.I
