import Mathlib
import NlsGge.Atomic.I.I033Core
import NlsGge.Atomic.I.I038Measure
import NlsGge.Atomic.I.I038Weight
import NlsGge.Birkhoff.S04Moments38d

                                                                                                             
                                                                                               
                                                                                                                      
                                  
                                                                                                                 
                                                                                                                      
                                                                                                      
                                                                                                            
                                                               
                                                                                                                  
                                                                                                                 
                                                                       
                                                                                                                    
                                                                                                                
                                                                                           
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
open NlsGge.Pilot NlsGge.Measure NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.I038L

theorem limit_gen (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (W : ℝ → ℝ) (hWc : Continuous W) :
    0 < limitNormalizer W ∧ limitNormalizer W ≤ 1 ∧
    IsProbabilityMeasure (weightedSequenceLaw W) ∧ IsProbabilityMeasure (physicalLaw W) ∧
    weightedSequenceLaw W ≪ countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ))) ∧
    countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ))) ≪ weightedSequenceLaw W ∧
    (∀ A : Set (ℤ → ℂ), MeasurableSet A →
      weightedSequenceLaw W A ≤ ENNReal.ofReal ((limitNormalizer W)⁻¹) *
        countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ))) A) := by
  set γ := countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ))) with hγ
  have hRm := NlsGge.ThirdConsultation.I033C.measurable_sequenceRemainder Bk hB W hWc
  have h0 := NlsGge.ThirdConsultation.I033C.sequenceRemainder_nonneg W
  have hPm : Measurable physicalOfSequence := by
    rw [show physicalOfSequence = Bk.cleanΦinv from (funext hB).symm]
    exact Bk.measurable_cleanΦinv
  have hlaw : weightedSequenceLaw W = gibbsLaw38 γ (sequenceRemainder W) := rfl
  have hZ : limitNormalizer W = gibbsPartition38 γ (sequenceRemainder W) := rfl
  have hZ1 := gibbsPartition38_pos γ _ hRm h0
  have hprob : IsProbabilityMeasure (weightedSequenceLaw W) := by
    rw [hlaw]; exact gibbsLaw38_prob γ _ hRm h0
  refine ⟨hZ ▸ hZ1, hZ ▸ gibbsPartition38_le_one γ _ hRm h0, hprob, ?_, ?_, ?_, fun A hA => ?_⟩
  · unfold physicalLaw
    exact (Measure.isProbabilityMeasure_map_iff hPm.aemeasurable).2 hprob
  · rw [hlaw]; exact gibbsLaw38_ac γ _ hRm h0
  · rw [hlaw]; exact ac_gibbsLaw38 γ _ hRm h0
  · rw [hlaw, gibbsLaw38_eq_withDensity γ _ hRm h0, withDensity_apply _ hA, hZ]
    calc ∫⁻ x in A, ENNReal.ofReal ((gibbsPartition38 γ (sequenceRemainder W))⁻¹ *
          Real.exp (-sequenceRemainder W x)) ∂γ
        ≤ ∫⁻ _x in A, ENNReal.ofReal ((gibbsPartition38 γ (sequenceRemainder W))⁻¹) ∂γ := by
          refine lintegral_mono (fun x => ENNReal.ofReal_le_ofReal ?_)
          have he : Real.exp (-sequenceRemainder W x) ≤ 1 :=
            Real.exp_le_one_iff.2 (neg_nonpos.2 (h0 x))
          have hi : 0 ≤ (gibbsPartition38 γ (sequenceRemainder W))⁻¹ := inv_nonneg.2 hZ1.le
          nlinarith
      _ = ENNReal.ofReal ((gibbsPartition38 γ (sequenceRemainder W))⁻¹) * γ A := by
          rw [setLIntegral_const]

theorem measurableSet_allSobolev_phys :
    MeasurableSet {u : PhysicalL2 | ∀ r : ℕ, SobolevSquareSummable (r : ℝ) (physicalFourier u)} := by
  have h := (NlsGge.ThirdConsultation.I038M.measurableSet_good (fun _ => (0 : ℝ)) (fun _ => le_rfl))
  have e : {u : PhysicalL2 | ∀ r : ℕ, SobolevSquareSummable (r : ℝ) (physicalFourier u)} =
      (fun u : PhysicalL2 => fun n : ℤ => physicalFourier u n) ⁻¹'
        {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
          Summable (fun n : ℤ => (fun _ => (0 : ℝ)) n * ‖z n‖ ^ 2)} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_preimage, zero_mul, summable_zero, and_true]
  rw [e]
  exact measurable_physicalFourierSeq38 h

theorem ae_allSobolev (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (p : ℝ) (hp : 2 < p) (c : BoundedCoefficients 1 2) :
    ∀ᵐ (u : PhysicalL2) ∂physicalLaw (NlsGge.Atomic.I037.factorialPowerWeight p c.val),
      ∀ r : ℕ, SobolevSquareSummable (r : ℝ) (physicalFourier u) := by
  set W := NlsGge.Atomic.I037.factorialPowerWeight p c.val with hW
  have hc : ∀ j, 1 ≤ c.val j ∧ c.val j ≤ 2 := c.property.2.2
  have hWc : Continuous W := NlsGge.ThirdConsultation.I038W.continuous_weight hp hc
  have hPm : Measurable physicalOfSequence := by
    rw [show physicalOfSequence = Bk.cleanΦinv from (funext hB).symm]
    exact Bk.measurable_cleanΦinv
  obtain ⟨-, -, -, -, hac, -, -⟩ := limit_gen Bk hB W hWc
  obtain ⟨hΩm, hΩ1⟩ := NlsGge.ThirdConsultation.I038M.omega_conjuncts p hp c
  have hΩae := (prob_compl_eq_zero_iff hΩm).2 hΩ1
  unfold physicalLaw
  rw [ae_map_iff hPm.aemeasurable measurableSet_allSobolev_phys]
  refine hac.ae_le ?_
  filter_upwards [ae_iff.2 hΩae] with z hz r
  rw [← hB z]
  exact Bk.sobolev_cleanΦinv38 r z ((mem_seqSobolev38_iff _ _).2 (hz.1 r))

end NlsGge.ThirdConsultation.I038L
