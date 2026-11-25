import Mathlib
import NlsGge.Atomic.I.I023Core
import NlsGge.Birkhoff.H02Hierarchy38d
import NlsGge.Birkhoff.H03Diagonal38b

                                                                                                                   
                                                                                   
                                                                                                                    
                                                                       
                                                                                                                
                                                                                                                      
                                                                                                                             
                                                                                                              
                                                                                                                  
                                                                                                                            
                                                                                            
                                                                                                                       
                                                               
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.I042C

theorem uniform_partial (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (A : ℝ) (hA : 0 ≤ A) :
    TendstoUniformlyOn (fun m : ℕ => partialWeight c m) (weight c) atTop (Set.Icc (-A) A) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h := tendsto_weightTail38 lower upper c hlower hbound hupper A
  filter_upwards [h (Iio_mem_nhds hε)] with m hm x hx
  have hx' : |x| ≤ A := abs_le.2 hx
  rw [Real.dist_eq, weight_sub_partialWeight38 lower upper c hlower hbound hupper m x,
    abs_of_nonneg (weightTail38_nonneg lower upper c hlower hbound hupper m x)]
  exact lt_of_le_of_lt (weightTail38_mono lower upper c hlower hbound hupper m hx') hm

theorem gamma_eq (c : ℕ → ℝ) (m : ℕ) :
    NlsGge.HierarchyRiccati.Core.gammaM38 m (coefficient c) =
      countableComplexGaussian (fun n : ℤ => partialWeight c m (2 * Real.pi * (n : ℝ))) := rfl

theorem hier_rem_ae (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m) :
    Bk.hierRbar38 c m =ᵐ[NlsGge.HierarchyRiccati.Core.gammaM38 m (coefficient c)]
      sequenceRemainder (partialWeight c m) := by
  filter_upwards [BirkhoffInput38.ae_mem_seqSobolev38_gammaM38 lower c hlower hbound hm] with z hz
  rw [Bk.hierRbar38_of_mem c m hz]
  have h4 := hierRemainder38_F04 lower c hlower hbound hm _ (Bk.sobolev_cleanΦinv_hier38 m hz)
  unfold sequenceRemainder
  rw [← hB z]
  exact (max_eq_right h4.2).symm

theorem hierZ_eq (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m) :
    Bk.hierZ38 c m = limitNormalizer (partialWeight c m) := by
  unfold BirkhoffTop38.hierZ38 limitNormalizer gibbsPartition38
  rw [← gamma_eq]
  exact integral_congr_ae ((hier_rem_ae Bk hB lower c hlower hbound hm).mono fun z hz => by simp only [hz])

theorem hierMuHat_eq (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m) :
    Bk.hierMuHat38 c m = weightedSequenceLaw (partialWeight c m) := by
  have hZ := hierZ_eq Bk hB lower c hlower hbound hm
  unfold BirkhoffTop38.hierMuHat38 weightedSequenceLaw gibbsLaw38 Measure.tilted
  rw [← gamma_eq]
  have hZ' : ∫ x, Real.exp (-sequenceRemainder (partialWeight c m) x)
      ∂(NlsGge.HierarchyRiccati.Core.gammaM38 m (coefficient c)) = Bk.hierZ38 c m := by
    rw [hZ]; rfl
  simp only [neg_neg]
  rw [hZ']
  exact withDensity_congr_ae ((hier_rem_ae Bk hB lower c hlower hbound hm).mono fun z hz => by simp only [hz])

theorem hierMu_eq (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m) :
    Bk.hierMu38 c m = physicalLaw (partialWeight c m) := by
  unfold BirkhoffTop38.hierMu38 physicalLaw
  rw [hierMuHat_eq Bk hB lower c hlower hbound hm, show Bk.cleanΦinv = physicalOfSequence from funext hB]

/-- The Ω₁ path block of I-042. -/
theorem path_block (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    ∀ g ∈ Omega1_38 c.val,
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
        (𝓝 (remainder38 c.val (physicalOfSequence (zFull38 c.val g)))) := by
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  have hW := weight_continuous38 hl hb' hu'
  intro g hg
  have hzF := zFull38_mem_Omega038 lower upper c.val hl hb' hu' hg
  obtain ⟨h1, h2, h3, -⟩ := NlsGge.ThirdConsultation.I023C.i024_of Bk hB lower upper c _ hzF
  have hRW := NlsGge.ThirdConsultation.I017C.remainderForWeight_eq c.val hW
  refine ⟨h1, by rw [← hRW]; exact h2, by rw [h3, hRW], fun n => ?_, fun m hm => ?_, ?_⟩
  · have h := (Bk.tendsto_summand_scale38 lower upper c.val hl hb' hu' hg n).comp (tendsto_add_atTop_nat 2)
    rw [remainderSummand38_eq_gapRemainderTerm c.val hW] at h
    simp only [Function.comp_def, hB] at h
    exact h
  · have hz := zHier38_mem_seqSobolev38 lower upper c.val hl hb' hu' hg hm
    have h4 := hierRemainder38_F04 lower c.val hl hb' hm _ (Bk.sobolev_cleanΦinv_hier38 m hz)
    rw [hB] at h4
    refine ⟨h4.1, h4.2, ?_⟩
    unfold sequenceRemainder
    exact max_eq_right h4.2
  · have h := (Bk.tendsto_remainder_scale38 lower upper c.val hl hb' hu' hg).comp (tendsto_add_atTop_nat 2)
    simp only [Function.comp_def, hB] at h
    exact h

end NlsGge.ThirdConsultation.I042C
