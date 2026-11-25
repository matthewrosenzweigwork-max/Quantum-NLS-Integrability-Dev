import Mathlib
import NlsGge.Atomic.I.I038Core
import NlsGge.ThirdConsultation.I.ActualInverseBridge

                                                                                                     
                                                                          
                                                                                             
                                                                                                           
                                                                                                                 
                                                                                                                
                                                                               
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.I010 (spectralEnergy)
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

theorem i038 (p : ℝ) (hp : 2 < p) (c : BoundedCoefficients 1 2) :
    let W := NlsGge.Atomic.I037.factorialPowerWeight p c.val
    let a := fun n : ℤ => W (2 * Real.pi * (n : ℝ))
    let γ := countableComplexGaussian a
    let Ω := {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => a n * ‖z n‖ ^ 2 * japaneseBracket n ^ (2 / p - 2))}
    Summable (fun n : ℤ => japaneseBracket n ^ (2 / p - 2)) ∧
    MeasurableSet Ω ∧ γ Ω = 1 ∧
    (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : PhysicalL2, SobolevSquareSummable 1 (physicalFourier u) →
        ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
          |gapRemainderTermE02_38 W u n| ≤
            C * a n * actualGapActionAllE02_38 u n * japaneseBracket n ^ (2 / p - 2)) ∧
    (∀ z ∈ Ω,
      Summable (fun n : ℤ => |gapRemainderTermE02_38 W (physicalOfSequence z) n|) ∧
      sequenceRemainder W z = remainderForWeight W (physicalOfSequence z) ∧
      0 ≤ remainderForWeight W (physicalOfSequence z)) ∧
    (∀ S : Finset ℤ,
      0 < finiteAbsolutePartition W S ∧
      finiteAbsolutePartition W S ≤ ∏ n : S, Real.pi / a n ∧
      0 < finiteRelativeNormalizer W S ∧ finiteRelativeNormalizer W S ≤ 1 ∧
      finiteRelativeNormalizer W S = finiteAbsolutePartition W S / (∏ n : S, Real.pi / a n) ∧
      finiteGapCoordinateLaw W S = (finiteComplexVolume S).withDensity
        (fun w => ENNReal.ofReal (Real.exp (-spectralEnergy W (finiteGapField S w)) /
          finiteAbsolutePartition W S)) ∧
      IsProbabilityMeasure (finiteGapLaw W S) ∧
      ∀ w : S → ℂ,
        Integrable (fun t : ℝ => W (2 * t) * actualGapHeightE02_38 (finiteGapField S w) t) ∧
        HasSum (fun j : ℕ => c.val j / ((j.factorial : ℝ) ^ p) *
          chargeFn38 (j + 2) j (finiteGapField S w)) (spectralEnergy W (finiteGapField S w))) ∧
    0 < limitNormalizer W ∧ limitNormalizer W ≤ 1 ∧
    IsProbabilityMeasure (weightedSequenceLaw W) ∧ IsProbabilityMeasure (physicalLaw W) ∧
    weightedSequenceLaw W ≪ γ ∧ γ ≪ weightedSequenceLaw W ∧
    (∀ A : Set (ℤ → ℂ), MeasurableSet A →
      weightedSequenceLaw W A ≤ ENNReal.ofReal ((limitNormalizer W)⁻¹) * γ A) ∧
    (∀ᵐ (u : PhysicalL2) ∂physicalLaw W, ∀ r : ℕ, SobolevSquareSummable (r : ℝ) (physicalFourier u)) ∧
    ∀ Λ : ℕ → Finset ℤ, IsExhaustion38 Λ →
      Tendsto (fun N : ℕ => finiteRelativeNormalizer W (Λ N)) atTop (𝓝 (limitNormalizer W)) ∧
      ∀ (r : ℕ) (F : SobolevHilbert (r : ℝ) →ᵇ ℝ),
        Tendsto (fun N : ℕ => ∫ u : PhysicalL2, F (physFS38 r u) ∂finiteGapLaw W (Λ N))
          atTop (𝓝 (∫ u : PhysicalL2, F (physFS38 r u) ∂physicalLaw W)) :=
  NlsGge.ThirdConsultation.I038A.i038_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence p hp c

end NlsGge.ThirdConsultation.I
