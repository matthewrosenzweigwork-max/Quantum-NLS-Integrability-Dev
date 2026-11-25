import Mathlib
import NlsGge.ThirdConsultation.I.LimitLaws
import NlsGge.Atomic.I.I039
import NlsGge.Birkhoff.S04Moments38b
import NlsGge.Birkhoff.S04Moments38c
import NlsGge.Birkhoff.H03Diagonal38b
import NlsGge.Birkhoff.BirkhoffInput38
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38

                                                                                                                       
                                                                                                                       
                                                                                                              
                                                                                                                      
                                                                                                
                                                                              
                                                                                                                      
                                                                                                                  
                                                                                                              
                                                                                                  
                                                                                                               
                                                                                                                
                                                                                                                           
                                                  set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.I010 (spectralEnergy)
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I
namespace I029Aux

theorem norm_physFS (m : ℕ) (v : PhysicalL2) : ‖physFS38 m v‖ = ‖physH38 m v‖ := by
  unfold physFS38
  show ‖reflC38 (m : ℝ) (physH38 m v)‖ = _
  exact (reflIso38 (m : ℝ)).norm_map _

theorem hnorm_zero (x : ℤ → ℂ) (hs : Summable (fun n : ℤ => ‖x n‖ ^ 2)) :
    hnorm38 0 x = Real.sqrt (∑' n : ℤ, ‖x n‖ ^ 2) := by
  have hw : ∀ n : ℤ, sobolevWeight38 0 n = 1 := fun n => by
    simp [sobolevWeight38]
  have hs' : Summable (fun n : ℤ => sobolevWeight38 0 n * ‖x n‖ ^ 2) := by
    simpa [hw] using hs
  unfold hnorm38
  rw [sobEnergy38_eq_tsum 0 hs']
  simp [hw]

theorem norm_physH_zero (v : PhysicalL2) : ‖physH38 0 v‖ = ‖v‖ := by
  have hmem : fourierSeq38 v ∈ seqSobolev38 ((0 : ℕ) : ℝ) := by
    simpa using fourierSeq38_mem_zero v
  have hlp := lp.hasSum_norm (p := 2) (by norm_num) (reflectedFourierL2 v)
  have hs : Summable (fun n : ℤ => ‖fourierSeq38 v n‖ ^ 2) := by
    have h2 : Summable (fun n : ℤ => ‖(reflectedFourierL2 v) n‖ ^ 2) := by simpa using hlp.summable
    exact h2
  rw [physH38_of_mem 0 v hmem, norm_carrierMk_eq_hnorm38 0 _ hmem, hnorm_zero _ hs,
    ← norm_sq_eq_tsum_fourierSeq38, Real.sqrt_sq (norm_nonneg _)]

theorem i029_of (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (B : BirkhoffTop38) (hM : BirkhoffMolnar38 B)
    (hΦ : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (hP : B.muW38 c.val = physicalLaw (weight c.val))
    (hZ : B.ZW38 c.val = limitNormalizer (weight c.val))
    (hact : ∀ (u : PhysicalL2) (n : ℤ), actualGapActionAllE02_38 u n = ‖physicalBirkhoff u n‖ ^ 2)
    (hsum : ∀ u : PhysicalL2, HasSum (fun n : ℤ => actualGapActionAllE02_38 u n) (‖u‖ ^ 2))
    (hR : Function.RightInverse physicalInverseBirkhoff physicalBirkhoff) :
    (∀ m : ℕ, ∃ A : ℝ, 0 < A ∧ ∃ d : ℕ,
      ∀ z : ℤ → ℂ, SobolevSquareSummable (m : ℝ) z →
        ‖physFS38 m (physicalOfSequence z)‖ ≤ A * (1 + sobolevSeqNorm m z) ^ d) ∧
    (∀ z : ℤ → ℂ, SobolevSquareSummable 0 z →
      ‖physicalOfSequence z‖ = sobolevSeqNorm 0 z) ∧
    (∀ᵐ (u : PhysicalL2) ∂physicalLaw (weight c.val),
      ∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier u)) ∧
    ∀ (m : ℕ) (q : ℝ), 0 ≤ q →
      Integrable (fun z : ℤ → ℂ => ‖physFS38 m (physicalOfSequence z)‖ ^ q)
        (fullWeightSequenceGaussian c.val) ∧
      Integrable (fun u : PhysicalL2 => ‖physFS38 m u‖ ^ q) (physicalLaw (weight c.val)) ∧
      (∫ u : PhysicalL2, ‖physFS38 m u‖ ^ q ∂physicalLaw (weight c.val)) ≤
        (limitNormalizer (weight c.val))⁻¹ *
          (∫ z : ℤ → ℂ, ‖physFS38 m (physicalOfSequence z)‖ ^ q
            ∂fullWeightSequenceGaussian c.val) := by
  obtain ⟨hlower, -, hc⟩ := c.property
  have hbound : ∀ j : ℕ, lower ≤ c.val j := fun j => (hc j).1
  have hupper : ∀ j : ℕ, c.val j ≤ upper := fun j => (hc j).2
  -- mass identity
  have hmass : ∀ z : ℤ → ℂ, SobolevSquareSummable 0 z →
      ‖physicalOfSequence z‖ = sobolevSeqNorm 0 z := by
    intro z hz
    have hz0 : z ∈ seqSobolev38 0 := (mem_seqSobolev38_iff _ _).2 hz
    have hl : Memℓp z 2 := (mem_seqSobolev38_zero_iff z).1 hz0
    have hu : physicalOfSequence z = physicalInverseBirkhoff ⟨z, hl⟩ := by
      unfold physicalOfSequence
      rw [dif_pos hl]
    have hΦu : physicalBirkhoff (physicalOfSequence z) = ⟨z, hl⟩ := by
      rw [hu]; exact hR _
    have hs := hsum (physicalOfSequence z)
    have hcoef : ∀ n : ℤ, actualGapActionAllE02_38 (physicalOfSequence z) n = ‖z n‖ ^ 2 := fun n => by
      rw [hact, hΦu]
    simp only [hcoef] at hs
    show ‖physicalOfSequence z‖ = hnorm38 0 z
    rw [hnorm_zero z hs.summable, hs.tsum_eq, Real.sqrt_sq (norm_nonneg _)]
  -- conj 1
  have hpoly : ∀ m : ℕ, ∃ A : ℝ, 0 < A ∧ ∃ d : ℕ,
      ∀ z : ℤ → ℂ, SobolevSquareSummable (m : ℝ) z →
        ‖physFS38 m (physicalOfSequence z)‖ ≤ A * (1 + sobolevSeqNorm m z) ^ d := by
    intro m
    by_cases hm : 1 ≤ m
    · obtain ⟨C, d, hC, hCd⟩ := B.exists_cleanTinvC_bound38 hM m hm
      refine ⟨C + 1, by linarith, d, fun z hz => ?_⟩
      have hzm : z ∈ seqSobolev38 (m : ℝ) := (mem_seqSobolev38_iff _ _).2 hz
      rw [norm_physFS, ← hΦ, B.physH38_cleanΦinv]
      have h0 : 0 ≤ (1 + hnorm38 m z) ^ d := pow_nonneg (by linarith [hnorm38_nonneg m z]) d
      calc ‖B.cleanTinvC m z‖ ≤ C * (1 + hnorm38 m z) ^ d := hCd z hzm
        _ ≤ (C + 1) * (1 + sobolevSeqNorm m z) ^ d := mul_le_mul_of_nonneg_right (by linarith) h0
    · have hm0 : m = 0 := by omega
      subst hm0
      refine ⟨1, one_pos, 1, fun z hz => ?_⟩
      have hz' : SobolevSquareSummable 0 z := by simpa using hz
      rw [norm_physFS, norm_physH_zero, hmass z hz', one_mul, pow_one]
      linarith [hnorm38_nonneg 0 z]
  -- measurability
  have hΦfun : physicalOfSequence = B.cleanΦinv := funext fun z => (hΦ z).symm
  have hmeasΦ : Measurable physicalOfSequence := by rw [hΦfun]; exact B.measurable_cleanΦinv
  refine ⟨hpoly, hmass, ?_, fun m q hq => ?_⟩
  · rw [← hP]
    exact B.ae_muW38_allSobolev lower upper c.val hlower hbound hupper
  obtain ⟨A, hA, d, hb⟩ := hpoly m
  have hmeasF : Measurable (fun z : ℤ → ℂ => ‖physFS38 m (physicalOfSequence z)‖ ^ q) :=
    (((measurable_physFS38 m).comp hmeasΦ).norm).pow_const q
  have hintγ : Integrable (fun z : ℤ → ℂ => ‖physFS38 m (physicalOfSequence z)‖ ^ q)
      (fullWeightSequenceGaussian c.val) := by
    have hg := (integrable_hnorm_pow38 lower upper c.val hlower hbound hupper m (d * ⌈q⌉₊)).const_mul (A ^ q)
    refine hg.mono' hmeasF.aestronglyMeasurable ?_
    filter_upwards [ae_mem_Omega038 lower upper c.val hlower hbound hupper] with z hz
    have hzm : SobolevSquareSummable (m : ℝ) z :=
      (mem_seqSobolev38_iff _ _).1 (BirkhoffTop38.mem_seqSobolev38_of_Omega038 c.val hz m)
    have hN := hb z hzm
    have h1 : (1 : ℝ) ≤ 1 + hnorm38 m z := by linarith [hnorm38_nonneg m z]
    have hn0 : 0 ≤ ‖physFS38 m (physicalOfSequence z)‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn0 q)]
    calc ‖physFS38 m (physicalOfSequence z)‖ ^ q ≤ (A * (1 + hnorm38 m z) ^ d) ^ q :=
          Real.rpow_le_rpow hn0 hN hq
      _ = A ^ q * (1 + hnorm38 m z) ^ ((d : ℝ) * q) := by
          rw [Real.mul_rpow hA.le (pow_nonneg (by linarith) d), ← Real.rpow_natCast,
            ← Real.rpow_mul (by linarith)]
      _ ≤ A ^ q * (1 + hnorm38 m z) ^ ((d * ⌈q⌉₊ : ℕ) : ℝ) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 ?_) (Real.rpow_nonneg hA.le q)
          push_cast
          exact mul_le_mul_of_nonneg_left (Nat.le_ceil q) (Nat.cast_nonneg d)
      _ = A ^ q * (1 + hnorm38 m z) ^ (d * ⌈q⌉₊) := by rw [Real.rpow_natCast]
  obtain ⟨hZpos, -⟩ := B.ZW38_pos_le_one lower upper c.val hlower hbound hupper
  have hle := B.muHatW38_le lower upper c.val hlower hbound hupper
  have hne : ENNReal.ofReal (1 / B.ZW38 c.val) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hintS : Integrable (fun z : ℤ → ℂ => ‖physFS38 m (physicalOfSequence z)‖ ^ q)
      (ENNReal.ofReal (1 / B.ZW38 c.val) • fullWeightSequenceGaussian c.val) := hintγ.smul_measure hne
  have hintH : Integrable (fun z : ℤ → ℂ => ‖physFS38 m (physicalOfSequence z)‖ ^ q) (B.muHatW38 c.val) :=
    hintS.mono_measure hle
  have hgm : Measurable (fun u : PhysicalL2 => ‖physFS38 m u‖ ^ q) :=
    ((measurable_physFS38 m).norm).pow_const q
  have hmap : physicalLaw (weight c.val) = (B.muHatW38 c.val).map physicalOfSequence := by
    rw [← hP, hΦfun]; rfl
  have hintP : Integrable (fun u : PhysicalL2 => ‖physFS38 m u‖ ^ q) (physicalLaw (weight c.val)) := by
    rw [hmap, integrable_map_measure hgm.aestronglyMeasurable hmeasΦ.aemeasurable]
    exact hintH
  refine ⟨hintγ, hintP, ?_⟩
  rw [hmap, integral_map hmeasΦ.aemeasurable hgm.aestronglyMeasurable]
  calc (∫ z : ℤ → ℂ, ‖physFS38 m (physicalOfSequence z)‖ ^ q ∂(B.muHatW38 c.val))
      ≤ ∫ z : ℤ → ℂ, ‖physFS38 m (physicalOfSequence z)‖ ^ q
          ∂(ENNReal.ofReal (1 / B.ZW38 c.val) • fullWeightSequenceGaussian c.val) :=
        integral_mono_measure hle (Eventually.of_forall fun z => Real.rpow_nonneg (norm_nonneg _) q) hintS
    _ = (limitNormalizer (weight c.val))⁻¹ *
          ∫ z : ℤ → ℂ, ‖physFS38 m (physicalOfSequence z)‖ ^ q ∂fullWeightSequenceGaussian c.val := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul, hZ, one_div]

end I029Aux
end NlsGge.ThirdConsultation.I
