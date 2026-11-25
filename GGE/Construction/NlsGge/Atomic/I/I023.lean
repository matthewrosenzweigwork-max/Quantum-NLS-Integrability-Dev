import Mathlib
import NlsGge.Atomic.I.I023Core
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

theorem i023 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (z : ℤ → ℂ) (hz : z ∈ goodGaussianSet c.val)
    (Λ : ℕ → Finset ℤ) (hΛ : IsExhaustion38 Λ) :
    let u := physicalOfSequence z
    let uN := fun N : ℕ => physicalOfSequence (projFin38 (Λ N) z)
    (∀ n : ℤ, actualGapActionAllE02_38 u n = ‖z n‖ ^ 2 ∧
      (∀ N : ℕ, actualGapActionAllE02_38 (uN N) n =
        if n ∈ Λ N then ‖z n‖ ^ 2 else 0) ∧
      Tendsto (fun N : ℕ => gapRemainderTermE02_38 (weight c.val) (uN N) n)
        atTop (𝓝 (gapRemainderTermE02_38 (weight c.val) u n))) ∧
    ∃ C : ℝ, 0 ≤ C ∧
      Summable (fun n : ℤ => C * fullWeightRate c.val n * ‖z n‖ ^ 2 *
        japaneseBracket n ^ (-3 / 2 : ℝ)) ∧
      ∀ n : ℤ,
        |gapRemainderTermE02_38 (weight c.val) u n| ≤
          C * fullWeightRate c.val n * ‖z n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ) ∧
        ∀ N : ℕ, |gapRemainderTermE02_38 (weight c.val) (uN N) n| ≤
          C * fullWeightRate c.val n * ‖z n‖ ^ 2 * japaneseBracket n ^ (-3 / 2 : ℝ) :=
  NlsGge.ThirdConsultation.I023C.i023_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence lower upper c z hz Λ hΛ

end NlsGge.ThirdConsultation.I
