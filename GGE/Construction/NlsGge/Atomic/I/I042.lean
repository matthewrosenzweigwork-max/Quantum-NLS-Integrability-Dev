import Mathlib
import NlsGge.Atomic.I.I042CoreF
import NlsGge.ThirdConsultation.I.ActualInverseBridge
import NlsGge.Atomic.F.F010Sup1
import NlsGge.Atomic.G6.G6013

                                                                                                                                                                                                                                           
                                                                          
                                                                                                      
                                                                                                              
                                                                                                                   
                                                                                            
                                                                                                                      
                                                                         
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

theorem i042 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    (∀ A : ℝ, 0 ≤ A →
      TendstoUniformlyOn (fun m : ℕ => partialWeight c.val m) (weight c.val) atTop (Set.Icc (-A) A)) ∧
    (∀ g ∈ Omega1_38 c.val,
      Summable (fun n : ℤ =>
        |gapRemainderTermE02_38 (weight c.val) (physicalOfSequence (zFull38 c.val g)) n|) ∧
      0 ≤ remainder38 c.val (physicalOfSequence (zFull38 c.val g)) ∧
      sequenceRemainder (weight c.val) (zFull38 c.val g) =
        remainder38 c.val (physicalOfSequence (zFull38 c.val g)) ∧
      (∀ n : ℤ, Tendsto (fun m : ℕ => gapRemainderTermE02_38 (partialWeight c.val (m + 2))
        (physicalOfSequence (zHier38 c.val (m + 2) g)) n) atTop
        (𝓝 (gapRemainderTermE02_38 (weight c.val) (physicalOfSequence (zFull38 c.val g)) n))) ∧
      (∀ m : ℕ, 2 ≤ m →
        Summable (fun n : ℤ => |gapRemainderTermE02_38 (partialWeight c.val m)
          (physicalOfSequence (zHier38 c.val m g)) n|) ∧
        0 ≤ hierRemainder38 c.val m (physicalOfSequence (zHier38 c.val m g)) ∧
        sequenceRemainder (partialWeight c.val m) (zHier38 c.val m g) =
          hierRemainder38 c.val m (physicalOfSequence (zHier38 c.val m g))) ∧
      Tendsto (fun m : ℕ => hierRemainder38 c.val (m + 2)
        (physicalOfSequence (zHier38 c.val (m + 2) g))) atTop
        (𝓝 (remainder38 c.val (physicalOfSequence (zFull38 c.val g))))) ∧
    (∀ m : ℕ, 2 ≤ m →
      limitNormalizer (partialWeight c.val m) =
        NlsGge.ThirdConsultation.F.finiteNormalizer m (coefficient c.val) ∧
      ∀ r : ℕ, r < m →
        (physicalLaw (partialWeight c.val m)).map (physFS38 r) = finiteOrderLaw c.val r m) ∧
    Tendsto (fun m : ℕ => NlsGge.ThirdConsultation.F.finiteNormalizer m (coefficient c.val))
      atTop (𝓝 (limitNormalizer (weight c.val))) ∧
    ∀ r : ℕ, ∀ F : SobolevHilbert (r : ℝ) →ᵇ ℝ,
      Tendsto (fun k : ℕ => ∫ u : SobolevHilbert (r : ℝ), F u
        ∂finiteOrderLaw c.val r (max 2 (r + 1) + k)) atTop
        (𝓝 (∫ u : PhysicalL2, F (physFS38 r u) ∂physicalLaw (weight c.val))) :=
  NlsGge.ThirdConsultation.I042FC.i042_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence
    NlsGge.ThirdConsultation.F010Aux.physicalBirkhoff_inverseOnSobolev
    NlsGge.ThirdConsultation.F010Aux.continuous_inverseOnSobolev G6013.2.2.2.2.1 lower upper c

end NlsGge.ThirdConsultation.I
