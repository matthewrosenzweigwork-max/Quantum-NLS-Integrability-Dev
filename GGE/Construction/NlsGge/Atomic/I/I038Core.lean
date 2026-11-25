import Mathlib
import NlsGge.Atomic.I.I038Weight
import NlsGge.Atomic.I.I038Measure
import NlsGge.Atomic.I.I038Omega
import NlsGge.Atomic.I.I038FiniteBlock
import NlsGge.Atomic.I.I038Charge
import NlsGge.Atomic.I.I038Limit
import NlsGge.Atomic.I.I038Weak

                                                                                                              
                                                                                              
                                                                                                      
                                                                                                                     
                                                                                                                    
                                                                                                                     
                                                                    
                                                                                                  
                                                                                                         
                                                                                 
                                                                                                       
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.Measure
open NlsGge.ThirdConsultation.I
open NlsGge.Atomic.I010 (spectralEnergy)

namespace NlsGge.ThirdConsultation.I038A

theorem i038_of (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (p : ℝ) (hp : 2 < p) (c : BoundedCoefficients 1 2) :
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
          atTop (𝓝 (∫ u : PhysicalL2, F (physFS38 r u) ∂physicalLaw W)) := by
  intro W a γ Ω
  have hc : ∀ j, 1 ≤ c.val j ∧ c.val j ≤ 2 := c.property.2.2
  have hp1 : 1 ≤ p := by linarith
  have hW2 := NlsGge.ThirdConsultation.I038S.contDiff_weight hp1 hc
  have hconv := NlsGge.ThirdConsultation.I038S.convexOn_weight hp1 hc
  have hWc : Continuous W := hW2.continuous
  have hpos : ∀ n : ℤ, 0 < W (2 * Real.pi * (n : ℝ)) := fun n => by
    have := NlsGge.Atomic.I037.weight_ge_one hp1 hc (2 * Real.pi * (n : ℝ)); linarith
  set w : ℤ → ℝ := fun n => a n * japaneseBracket n ^ (2 / p - 2) with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n =>
    mul_nonneg (hpos n).le (Real.rpow_nonneg (by unfold japaneseBracket; positivity) _)
  have hgap : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalL2,
      SobolevSquareSummable 1 (physicalFourier u) → ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
        |gapRemainderTermE02_38 W u n| ≤ C * w n * actualGapActionAllE02_38 u n := by
    intro B hB0
    obtain ⟨C, hC, h⟩ := NlsGge.ThirdConsultation.I038W.gap_conjunct p hp c B hB0
    refine ⟨C, hC, fun u hu hBu n => (h u hu hBu n).trans (le_of_eq ?_)⟩
    simp only [hw]; ring
  obtain ⟨hΩm, hΩ1⟩ := NlsGge.ThirdConsultation.I038M.omega_conjuncts p hp c
  have hΩae : ∀ᵐ z ∂γ, (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => w n * ‖z n‖ ^ 2) := by
    have h := ae_iff.2 ((prob_compl_eq_zero_iff hΩm).2 hΩ1)
    filter_upwards [h] with z hz
    exact ⟨hz.1, hz.2.congr fun n => by simp only [hw]; ring⟩
  obtain ⟨hZ1, hZ2, hP1, hP2, hac1, hac2, hdens⟩ :=
    NlsGge.ThirdConsultation.I038L.limit_gen Bk hB W hWc
  refine ⟨NlsGge.ThirdConsultation.I038W.summable_bracket hp, hΩm, hΩ1,
    NlsGge.ThirdConsultation.I038W.gap_conjunct p hp c,
    NlsGge.ThirdConsultation.I038O.omega_remainder_of Bk hB p hp c, fun S => ?_,
    hZ1, hZ2, hP1, hP2, hac1, hac2, hdens,
    NlsGge.ThirdConsultation.I038L.ae_allSobolev Bk hB p hp c,
    fun Λ hΛ => NlsGge.ThirdConsultation.I038K.weak_gen Bk hB W hW2 hconv w hw0 hgap hΩae Λ hΛ⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ :=
    NlsGge.ThirdConsultation.I038B.block Bk hB W hW2 hconv hpos S
  exact ⟨b1, b2, b3, b4, b5, b6, b7, fun v => ⟨b8 v,
    NlsGge.ThirdConsultation.I038C.finiteGap_charge Bk hB p hp1 c.val hc S v⟩⟩

end NlsGge.ThirdConsultation.I038A
