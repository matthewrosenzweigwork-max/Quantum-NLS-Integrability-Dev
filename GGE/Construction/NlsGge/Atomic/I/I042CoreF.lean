import Mathlib
import NlsGge.Atomic.I.I042CoreA
import NlsGge.Atomic.I.I026Core
import NlsGge.Atomic.I.I033Core
import NlsGge.ThirdConsultation.I.FiniteOrderLaw

                                                                                                                   
                                                                                    
                                                                                                                
                                                                                                                    
                                                                                                               
                                                 
                                
                                                                                                   
                                                                                         
                                                                                                               
                                                                                                                 
                                                                                                       
                                                                                                              
                                                   
                                                                                                  
                                                                                                        
                                                                                                 
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.I042FC

theorem ae_inv
    (hfid : ∀ m : ℕ, 2 ≤ m → ∀ (w : Hm1 m) (n : ℤ),
      physicalBirkhoff (sobolevToL2_38 (m - 1) (NlsGge.ThirdConsultation.F.inverseOnSobolev m w)) n =
        (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from w) n)
    (hLI : Function.LeftInverse physicalInverseBirkhoff physicalBirkhoff)
    (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ z ∂NlsGge.HierarchyRiccati.Core.gammaM38 m (coefficient c),
      sobolevToL2_38 (m - 1) (NlsGge.ThirdConsultation.F.inverseOnSequence m z) = physicalOfSequence z := by
  have hβ : ∀ i ≤ m, 0 ≤ coefficient c i := fun i _ => (coefficient_pos lower c hlower hbound i).le
  filter_upwards [NlsGge.HierarchyRiccati.Core.ae_summable38 hm hβ (coefficient_pos lower c hlower hbound 0)
      (coefficient_pos lower c hlower hbound m),
    NlsGge.HierarchyRiccati.Core.ae_gaussianRealization_apply38 hm hβ (coefficient_pos lower c hlower hbound 0)
      (coefficient_pos lower c hlower hbound m)] with z hz hz'
  have hzm : z ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ) := (mem_seqSobolev38_iff _ _).2 hz
  have hz0 : Memℓp z 2 := (mem_seqSobolev38_zero_iff z).1 (seqSobolev38_natCast_mono hzm)
  have hΦ : physicalBirkhoff (sobolevToL2_38 (m - 1) (NlsGge.ThirdConsultation.F.inverseOnSequence m z)) =
      ⟨z, hz0⟩ := Subtype.ext (funext fun n => (hfid m hm _ n).trans (hz' n))
  unfold physicalOfSequence
  rw [dif_pos hz0, ← hΦ, hLI]

theorem seqRem_ae (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (hfid : ∀ m : ℕ, 2 ≤ m → ∀ (w : Hm1 m) (n : ℤ),
      physicalBirkhoff (sobolevToL2_38 (m - 1) (NlsGge.ThirdConsultation.F.inverseOnSobolev m w)) n =
        (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from w) n)
    (hLI : Function.LeftInverse physicalInverseBirkhoff physicalBirkhoff)
    (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ z ∂NlsGge.HierarchyRiccati.Core.gammaM38 m (coefficient c),
      sequenceRemainder (partialWeight c m) z =
        Rm38 m (coefficient c) (NlsGge.ThirdConsultation.F.inverseOnSequence m z) := by
  filter_upwards [NlsGge.ThirdConsultation.I042C.hier_rem_ae Bk hB lower c hlower hbound hm,
    ae_inv hfid hLI lower c hlower hbound hm,
    BirkhoffInput38.ae_mem_seqSobolev38_gammaM38 lower c hlower hbound hm] with z h1 h2 h3
  rw [← h1, Bk.hierRbar38_of_mem c m h3]
  unfold Rm38 hierRemainder38
  rw [h2, ← hB z]
  rfl

theorem normalizer_eq (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (hfid : ∀ m : ℕ, 2 ≤ m → ∀ (w : Hm1 m) (n : ℤ),
      physicalBirkhoff (sobolevToL2_38 (m - 1) (NlsGge.ThirdConsultation.F.inverseOnSobolev m w)) n =
        (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from w) n)
    (hLI : Function.LeftInverse physicalInverseBirkhoff physicalBirkhoff)
    (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m) :
    limitNormalizer (partialWeight c m) = NlsGge.ThirdConsultation.F.finiteNormalizer m (coefficient c) := by
  unfold limitNormalizer gibbsPartition38 NlsGge.ThirdConsultation.F.finiteNormalizer
    NlsGge.ThirdConsultation.F.finiteDensity
  rw [← NlsGge.ThirdConsultation.I042C.gamma_eq]
  exact integral_congr_ae ((seqRem_ae Bk hB hfid hLI lower c hlower hbound hm).mono fun z hz => by
    simp only [hz])

theorem law_eq (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (hfid : ∀ m : ℕ, 2 ≤ m → ∀ (w : Hm1 m) (n : ℤ),
      physicalBirkhoff (sobolevToL2_38 (m - 1) (NlsGge.ThirdConsultation.F.inverseOnSobolev m w)) n =
        (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from w) n)
    (hcont : ∀ m : ℕ, 2 ≤ m → Continuous (NlsGge.ThirdConsultation.F.inverseOnSobolev m))
    (hLI : Function.LeftInverse physicalInverseBirkhoff physicalBirkhoff)
    (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m)
    (r : ℕ) :
    (physicalLaw (partialWeight c m)).map (physFS38 r) = finiteOrderLaw c r m := by
  haveI : BorelSpace (SobolevHilbert ((m - 1 : ℕ) : ℝ)) := ⟨rfl⟩
  have hW : Continuous (partialWeight c m) := continuous_partialWeight38 c m
  have hRm := NlsGge.ThirdConsultation.I033C.measurable_sequenceRemainder Bk hB _ hW
  have h0 := NlsGge.ThirdConsultation.I033C.sequenceRemainder_nonneg (partialWeight c m)
  have hPm : Measurable physicalOfSequence := by
    rw [show physicalOfSequence = Bk.cleanΦinv from (funext hB).symm]
    exact Bk.measurable_cleanΦinv
  have hInv : Measurable (NlsGge.ThirdConsultation.F.inverseOnSequence m) :=
    (hcont m hm).measurable.comp (NlsGge.HierarchyRiccati.Core.measurable_gaussianRealization38 (m := m))
  have hS : Measurable (fun u : Hm1 m => physFS38 r (sobolevToL2_38 (m - 1) u)) :=
    (measurable_physFS38 r).comp (sobolevToL2_38 (m - 1)).continuous.measurable
  set γ := NlsGge.HierarchyRiccati.Core.gammaM38 m (coefficient c) with hγ
  have hlaw : weightedSequenceLaw (partialWeight c m) = gibbsLaw38 γ (sequenceRemainder (partialWeight c m)) := rfl
  have hac : weightedSequenceLaw (partialWeight c m) ≪ γ := by
    rw [hlaw]; exact gibbsLaw38_ac _ _ hRm h0
  have hZint : ∫ x, Real.exp (-sequenceRemainder (partialWeight c m) x) ∂γ =
      NlsGge.ThirdConsultation.F.finiteNormalizer m (coefficient c) :=
    normalizer_eq Bk hB hfid hLI lower c hlower hbound hm
  have hZpos : 0 < NlsGge.ThirdConsultation.F.finiteNormalizer m (coefficient c) := by
    rw [← hZint]; exact (exp_neg_integral_pos_le_one38 γ _ hRm h0).1
  have hmeas : weightedSequenceLaw (partialWeight c m) =
      (ENNReal.ofReal (NlsGge.ThirdConsultation.F.finiteNormalizer m (coefficient c)))⁻¹ •
        γ.withDensity (fun z => ENNReal.ofReal (NlsGge.ThirdConsultation.F.finiteDensity m (coefficient c) z)) := by
    rw [hlaw]
    unfold gibbsLaw38 Measure.tilted
    simp only [neg_neg]
    rw [hZint, ← withDensity_smul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZpos).ne')]
    refine withDensity_congr_ae ?_
    filter_upwards [seqRem_ae Bk hB hfid hLI lower c hlower hbound hm] with z hz
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hz, ENNReal.ofReal_div_of_pos hZpos, div_eq_mul_inv, mul_comm]
    rfl
  unfold physicalLaw finiteOrderLaw NlsGge.ThirdConsultation.F.finiteGapLaw
  rw [Measure.map_map (measurable_physFS38 r) hPm, Measure.map_map hS hInv]
  have hmap : (physFS38 r ∘ physicalOfSequence) =ᵐ[weightedSequenceLaw (partialWeight c m)]
      ((fun u : Hm1 m => physFS38 r (sobolevToL2_38 (m - 1) u)) ∘
        NlsGge.ThirdConsultation.F.inverseOnSequence m) := by
    refine hac.ae_le ?_
    filter_upwards [ae_inv hfid hLI lower c hlower hbound hm] with z hz
    simp only [Function.comp_apply, hz]
  rw [Measure.map_congr hmap, hmeas]

theorem i042_of (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (hfid : ∀ m : ℕ, 2 ≤ m → ∀ (w : Hm1 m) (n : ℤ),
      physicalBirkhoff (sobolevToL2_38 (m - 1) (NlsGge.ThirdConsultation.F.inverseOnSobolev m w)) n =
        (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from w) n)
    (hcont : ∀ m : ℕ, 2 ≤ m → Continuous (NlsGge.ThirdConsultation.F.inverseOnSobolev m))
    (hLI : Function.LeftInverse physicalInverseBirkhoff physicalBirkhoff)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
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
        (𝓝 (∫ u : PhysicalL2, F (physFS38 r u) ∂physicalLaw (weight c.val))) := by
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  have hH := Bk.H02_hierarchy_limit_38 lower upper c.val hl hb' hu'
  have hZW := NlsGge.ThirdConsultation.IEnsC.ZW_eq_of Bk hB lower upper c
  have hmuW := NlsGge.ThirdConsultation.IEnsC.muW_eq_of Bk hB lower upper c
  refine ⟨fun A hA => NlsGge.ThirdConsultation.I042C.uniform_partial lower upper c.val hl hb' hu' A hA,
    NlsGge.ThirdConsultation.I042C.path_block Bk hB lower upper c,
    fun m hm => ⟨normalizer_eq Bk hB hfid hLI lower c.val hl hb' hm,
      fun r _ => law_eq Bk hB hfid hcont hLI lower c.val hl hb' hm r⟩, ?_, fun r F => ?_⟩
  · have h := hH.1.1
    rw [hZW] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with m hm
    rw [NlsGge.ThirdConsultation.I042C.hierZ_eq Bk hB lower c.val hl hb' hm,
      normalizer_eq Bk hB hfid hLI lower c.val hl hb' hm]
  · have h := (hH.2.2 r).2 (NlsGge.ThirdConsultation.I026C.houseTest r F)
    simp only [NlsGge.ThirdConsultation.I026C.houseTest_apply] at h
    rw [hmuW] at h
    have h2 := h.comp (tendsto_add_atTop_nat (max 2 (r + 1)))
    refine h2.congr (fun k => ?_)
    have hm : 2 ≤ k + max 2 (r + 1) := le_trans (le_max_left _ _) (Nat.le_add_left _ _)
    simp only [Function.comp_apply]
    rw [NlsGge.ThirdConsultation.I042C.hierMu_eq Bk hB lower c.val hl hb' hm,
      ← integral_map (measurable_physFS38 r).aemeasurable F.continuous.aestronglyMeasurable,
      law_eq Bk hB hfid hcont hLI lower c.val hl hb' hm r, add_comm]

end NlsGge.ThirdConsultation.I042FC
