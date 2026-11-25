import Mathlib
import NlsGge.Atomic.I.I038Pathwise
import NlsGge.Atomic.I.I022Core
import NlsGge.Atomic.I.I025Core
import NlsGge.Atomic.I.I017Core
import NlsGge.Atomic.I.I033Core

                                                                                                                        
                                                                                              
                                                                                                                  
                                                                                                                 
                                                                                                         
                                                                                                                     
                                                    
                                                                                                                 
                                                                                                        
                                                                                                             
                                                                                                                     
                                                                                                       
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.Measure
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.I038K

theorem restrict_map (q : ℤ → ℝ) (Λ : Finset ℤ) :
    (countableComplexGaussian q).map Λ.restrict = finiteComplexGaussian (fun n : Λ => q n) := by
  unfold countableComplexGaussian finiteComplexGaussian
  rw [Measure.infinitePi_map_restrict]

theorem field_restrict (Λ : Finset ℤ) (z : ℤ → ℂ) :
    finiteGapField Λ (Λ.restrict z) = physicalOfSequence (projFin38 Λ z) :=
  (congrArg physicalOfSequence (projFin38_eq_extZero38 Λ z)).symm

theorem gauss_restrict (W : ℝ → ℝ) (Λ : Finset ℤ) :
    finiteComplexGaussian (fun n : Λ => W (2 * Real.pi * ((n : ℤ) : ℝ))) =
      (countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ)))).map Λ.restrict :=
  (restrict_map (fun n : ℤ => W (2 * Real.pi * (n : ℝ))) Λ).symm

/-- The finite-gap normalizer and Gibbs integrals, written on the full product. -/
theorem finite_on_product (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (W : ℝ → ℝ) (hWc : Continuous W) (Λ : Finset ℤ) (G : PhysicalL2 → ℝ) (hG : Measurable G) :
    finiteRelativeNormalizer W Λ =
      ∫ z, Real.exp (-remainderForWeight W (physicalOfSequence (projFin38 Λ z)))
        ∂countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ))) ∧
    (0 < finiteRelativeNormalizer W Λ →
      ∫ u, G u ∂finiteGapLaw W Λ =
        (∫ z, Real.exp (-remainderForWeight W (physicalOfSequence (projFin38 Λ z))) *
          G (physicalOfSequence (projFin38 Λ z))
          ∂countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ)))) /
          finiteRelativeNormalizer W Λ) := by
  have hPm : Measurable physicalOfSequence := by
    rw [show physicalOfSequence = Bk.cleanΦinv from (funext hB).symm]
    exact Bk.measurable_cleanΦinv
  have hFm : Measurable (finiteGapField Λ) := hPm.comp (measurable_extZero38 Λ)
  have hRm := NlsGge.ThirdConsultation.I025C.measurable_remainderForWeight W hWc
  have hRΛ : Measurable (fun w => remainderForWeight W (finiteGapField Λ w)) := hRm.comp hFm
  have hres : AEMeasurable (Λ.restrict : (ℤ → ℂ) → (Λ → ℂ))
      (countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ)))) :=
    (Finset.measurable_restrict Λ).aemeasurable
  constructor
  · unfold finiteRelativeNormalizer gibbsPartition38
    rw [gauss_restrict, integral_map hres]
    · simp only [field_restrict]
    · exact (Real.measurable_exp.comp hRΛ.neg).aestronglyMeasurable
  · intro hZ
    unfold finiteGapLaw
    rw [integral_map hFm.aemeasurable hG.aestronglyMeasurable,
      NlsGge.ThirdConsultation.I017C.law_rel,
      BirkhoffTop38.integral_withDensity_exp_neg38 _ _ hRΛ _ hZ]
    congr 1
    rw [gauss_restrict, integral_map hres]
    · simp only [field_restrict]
    · exact ((Real.measurable_exp.comp hRΛ.neg).mul (hG.comp hFm)).aestronglyMeasurable

theorem weak_gen (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ Set.univ W)
    (w : ℤ → ℝ) (hw0 : ∀ n, 0 ≤ w n)
    (hgap : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalL2,
      SobolevSquareSummable 1 (physicalFourier u) → ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
        |gapRemainderTermE02_38 W u n| ≤ C * w n * actualGapActionAllE02_38 u n)
    (hΩ : ∀ᵐ z ∂countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ))),
      (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧ Summable (fun n : ℤ => w n * ‖z n‖ ^ 2))
    (Λ : ℕ → Finset ℤ) (hΛ : IsExhaustion38 Λ) :
    Tendsto (fun N : ℕ => finiteRelativeNormalizer W (Λ N)) atTop (𝓝 (limitNormalizer W)) ∧
      ∀ (r : ℕ) (F : SobolevHilbert (r : ℝ) →ᵇ ℝ),
        Tendsto (fun N : ℕ => ∫ u : PhysicalL2, F (physFS38 r u) ∂finiteGapLaw W (Λ N))
          atTop (𝓝 (∫ u : PhysicalL2, F (physFS38 r u) ∂physicalLaw W)) := by
  have hWc : Continuous W := hW2.continuous
  set γ := countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ))) with hγ
  have hPm : Measurable physicalOfSequence := by
    rw [show physicalOfSequence = Bk.cleanΦinv from (funext hB).symm]
    exact Bk.measurable_cleanΦinv
  have hRm := NlsGge.ThirdConsultation.I025C.measurable_remainderForWeight W hWc
  have hSm := NlsGge.ThirdConsultation.I033C.measurable_sequenceRemainder Bk hB W hWc
  have hS0 := NlsGge.ThirdConsultation.I033C.sequenceRemainder_nonneg W
  -- finite-gap remainders are nonnegative for every z
  have hRN0 : ∀ (S : Finset ℤ) (z : ℤ → ℂ),
      0 ≤ remainderForWeight W (physicalOfSequence (projFin38 S z)) := by
    intro S z
    rw [← hB]
    obtain ⟨hs, hfin, -⟩ := Bk.finiteGap_structure38 S z
    exact (NlsGge.ThirdConsultation.I038F.finiteGap_remainder W hW2 hconv _ hs hfin).2.2
  -- a.s. pointwise limits
  have hlimR : ∀ᵐ z ∂γ, Tendsto (fun N : ℕ => remainderForWeight W (physicalOfSequence (projFin38 (Λ N) z)))
      atTop (𝓝 (sequenceRemainder W z)) := by
    filter_upwards [hΩ] with z hz
    have hz1 : z ∈ seqSobolev38 ((1 : ℕ) : ℝ) := (mem_seqSobolev38_iff _ _).2 (hz.1 1)
    obtain ⟨-, -, hlim, h0⟩ := NlsGge.ThirdConsultation.I038P.pathwise Bk hB W hW2 hconv w hw0 hgap z hz1 hz.2 Λ hΛ
    unfold sequenceRemainder
    rw [max_eq_right h0]
    exact hlim
  have hlimP : ∀ r : ℕ, ∀ᵐ z ∂γ, Tendsto (fun N : ℕ => physFS38 r (physicalOfSequence (projFin38 (Λ N) z)))
      atTop (𝓝 (physFS38 r (physicalOfSequence z))) := by
    intro r
    filter_upwards [hΩ] with z hz
    have hzr : z ∈ seqSobolev38 (r : ℝ) := (mem_seqSobolev38_iff _ _).2 (hz.1 r)
    have hP : ∀ N : ℕ, projFin38 (Λ N) z ∈ seqSobolev38 (r : ℝ) := fun N =>
      finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 (Λ N) z)
    have hT : Tendsto (fun N : ℕ => Bk.cleanTinvC r (projFin38 (Λ N) z)) atTop (𝓝 (Bk.cleanTinvC r z)) := by
      rw [Bk.cleanTinvC_of_mem r z hzr]
      refine (((Bk.continuous_TinvC r).tendsto _).comp
        (tendsto_carrier_proj38 (r : ℝ) z hzr hΛ)).congr (fun N => ?_)
      rw [Bk.cleanTinvC_of_mem r _ (hP N)]
      rfl
    have h := ((continuous_physFS_comp38 r).tendsto _).comp hT
    rw [← hB z, NlsGge.ThirdConsultation.I022C.physFS_eq Bk r z]
    refine h.congr (fun N => ?_)
    simp only [Function.comp_apply]
    rw [← hB (projFin38 (Λ N) z), NlsGge.ThirdConsultation.I022C.physFS_eq Bk r]
  -- dominated convergence for a bounded measurable observable
  have hdct : ∀ (G : PhysicalL2 → ℝ) (M : ℝ), Measurable G → (∀ u, |G u| ≤ M) →
      (∀ᵐ z ∂γ, Tendsto (fun N : ℕ => G (physicalOfSequence (projFin38 (Λ N) z))) atTop
        (𝓝 (G (physicalOfSequence z)))) →
      Tendsto (fun N : ℕ => ∫ z, Real.exp (-remainderForWeight W (physicalOfSequence (projFin38 (Λ N) z))) *
          G (physicalOfSequence (projFin38 (Λ N) z)) ∂γ) atTop
        (𝓝 (∫ z, Real.exp (-sequenceRemainder W z) * G (physicalOfSequence z) ∂γ)) := by
    intro G M hG hM hGl
    refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun N => ?_) (integrable_const _)
      (fun N => Filter.Eventually.of_forall (fun z => ?_)) ?_
    · exact ((Real.measurable_exp.comp ((hRm.comp hPm).comp (measurable_projFin38 (Λ N))).neg).mul
        ((hG.comp hPm).comp (measurable_projFin38 (Λ N)))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-remainderForWeight W (physicalOfSequence (projFin38 (Λ N) z))) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (hRN0 _ z))
      have := hM (physicalOfSequence (projFin38 (Λ N) z))
      have h0 : 0 ≤ |G (physicalOfSequence (projFin38 (Λ N) z))| := abs_nonneg _
      nlinarith [Real.exp_pos (-remainderForWeight W (physicalOfSequence (projFin38 (Λ N) z)))]
    · filter_upwards [hlimR, hGl] with z hz1 hz2
      exact ((Real.continuous_exp.tendsto _).comp hz1.neg).mul hz2
  -- normalizers
  have hZ : 0 < limitNormalizer W := gibbsPartition38_pos γ _ hSm hS0
  have hZN : ∀ N, 0 < finiteRelativeNormalizer W (Λ N) := by
    intro N
    have hFm : Measurable (finiteGapField (Λ N)) := hPm.comp (measurable_extZero38 (Λ N))
    exact gibbsPartition38_pos _ _ (hRm.comp hFm) (fun v => by
      show 0 ≤ remainderForWeight W (physicalOfSequence (extZero38 (Λ N) v))
      have := hRN0 (Λ N) (extZero38 (Λ N) v)
      rwa [projFin38_extZero38] at this)
  have hden : Tendsto (fun N : ℕ => finiteRelativeNormalizer W (Λ N)) atTop (𝓝 (limitNormalizer W)) := by
    have h := hdct (fun _ => 1) 1 measurable_const (fun _ => by norm_num)
      (Filter.Eventually.of_forall fun _ => tendsto_const_nhds)
    simp only [mul_one] at h
    refine h.congr (fun N => ?_)
    exact ((finite_on_product Bk hB W hWc (Λ N) (fun _ => 1) measurable_const).1).symm
  refine ⟨hden, fun r F => ?_⟩
  have hG : Measurable (fun u : PhysicalL2 => F (physFS38 r u)) :=
    F.continuous.measurable.comp (measurable_physFS38 r)
  have hnum := hdct (fun u => F (physFS38 r u)) ‖F‖ hG (fun u => by
      rw [← Real.norm_eq_abs]; exact F.norm_coe_le_norm _)
    ((hlimP r).mono fun z hz => ((F.continuous.tendsto _).comp hz))
  have hlimit : ∫ u : PhysicalL2, F (physFS38 r u) ∂physicalLaw W =
      (∫ z, Real.exp (-sequenceRemainder W z) * F (physFS38 r (physicalOfSequence z)) ∂γ) /
        limitNormalizer W := by
    unfold physicalLaw
    rw [integral_map hPm.aemeasurable hG.aestronglyMeasurable]
    have hw : weightedSequenceLaw W = γ.withDensity
        (fun z => ENNReal.ofReal (Real.exp (-sequenceRemainder W z) / limitNormalizer W)) := rfl
    rw [hw, BirkhoffTop38.integral_withDensity_exp_neg38 _ _ hSm _ hZ]
  rw [hlimit]
  refine (hnum.div hden hZ.ne').congr (fun N => ?_)
  exact ((finite_on_product Bk hB W hWc (Λ N) _ hG).2 (hZN N)).symm

end NlsGge.ThirdConsultation.I038K
