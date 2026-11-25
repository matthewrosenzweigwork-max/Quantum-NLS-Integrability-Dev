import Mathlib
import NlsGge.Atomic.I.I040Core
import NlsGge.ThirdConsultation.I.ActualInverseBridge

                                                                                                     
                                                                          
                                                                                                                       
                                                                                                                   
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

theorem i040 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    ∀ g ∈ Omega1_38 c.val,
      (∀ (r m₀ : ℕ), max 2 (r + 1) ≤ m₀ →
        SobolevSquareSummable (r : ℝ) (physicalFourier (physicalOfSequence (zFull38 c.val g))) ∧
        (∀ m : ℕ, m₀ ≤ m → SobolevSquareSummable (r : ℝ)
          (physicalFourier (physicalOfSequence (zHier38 c.val m g)))) ∧
        Tendsto (fun k : ℕ => physFS38 r (physicalOfSequence (zHier38 c.val (m₀ + k) g)))
          atTop (𝓝 (physFS38 r (physicalOfSequence (zFull38 c.val g))))) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ‖physFS38 1 (physicalOfSequence (zFull38 c.val g))‖ ≤ B ∧
        ∀ m : ℕ, 2 ≤ m → ‖physFS38 1 (physicalOfSequence (zHier38 c.val m g))‖ ≤ B :=
  NlsGge.ThirdConsultation.I040C.i040_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence lower upper c

end NlsGge.ThirdConsultation.I
