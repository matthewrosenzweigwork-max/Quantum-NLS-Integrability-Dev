import Mathlib
import NlsGge.Atomic.I.I038FiniteGap
import NlsGge.Atomic.I.I017Core
import NlsGge.Atomic.I.I025Core

                                                                                                             
                                                                                                                      
                                  
                                                                                                                      
                                                                                                                     
                                                         
                                                                                                                         
                                                                                                                    
                                                                                                                   
                                                                                                               
                                                                                                     
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.ThirdConsultation.I
open NlsGge.Atomic.I010 (spectralEnergy)

namespace NlsGge.ThirdConsultation.I038B

theorem energy_split (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ Set.univ W) (S : Finset ℤ) (w : S → ℂ) :
    spectralEnergy W (finiteGapField S w) = remainderForWeight W (finiteGapField S w) +
      ∑ i : S, W (2 * Real.pi * ((i : ℤ) : ℝ)) * ‖w i‖ ^ 2 ∧
    0 ≤ remainderForWeight W (finiteGapField S w) ∧
    Integrable (fun t : ℝ => W (2 * t) * actualGapHeightE02_38 (finiteGapField S w) t) := by
  rw [NlsGge.ThirdConsultation.I017C.field_eq_proj Bk hB S w]
  obtain ⟨hs, hfin, hact⟩ := Bk.finiteGap_structure38 S (extZero38 S w)
  obtain ⟨-, hR, hnn⟩ := NlsGge.ThirdConsultation.I038F.finiteGap_remainder W hW2 hconv _ hs hfin
  have hsum : ∑' n : ℤ, W (2 * Real.pi * (n : ℝ)) *
      actualGapActionAllE02_38 (Bk.cleanΦinv (projFin38 S (extZero38 S w))) n =
      ∑ i : S, W (2 * Real.pi * ((i : ℤ) : ℝ)) * ‖w i‖ ^ 2 := by
    simp_rw [hact]
    rw [tsum_eq_sum (s := S) (fun n hn => by simp [hn]), ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [i.2, ↓reduceIte, extZero38_apply_of_mem w i.2]
  refine ⟨by linarith, hnn,
    (NlsGge.Atomic.I009.finiteGap_convex_difference _ hs hfin W hW2 hconv).1⟩

theorem block (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ Set.univ W)
    (hpos : ∀ n : ℤ, 0 < W (2 * Real.pi * (n : ℝ))) (S : Finset ℤ) :
    0 < finiteAbsolutePartition W S ∧
    finiteAbsolutePartition W S ≤ ∏ n : S, Real.pi / W (2 * Real.pi * ((n : ℤ) : ℝ)) ∧
    0 < finiteRelativeNormalizer W S ∧ finiteRelativeNormalizer W S ≤ 1 ∧
    finiteRelativeNormalizer W S =
      finiteAbsolutePartition W S / (∏ n : S, Real.pi / W (2 * Real.pi * ((n : ℤ) : ℝ))) ∧
    finiteGapCoordinateLaw W S = (finiteComplexVolume S).withDensity
      (fun w => ENNReal.ofReal (Real.exp (-spectralEnergy W (finiteGapField S w)) /
        finiteAbsolutePartition W S)) ∧
    IsProbabilityMeasure (finiteGapLaw W S) ∧
    ∀ w : S → ℂ, Integrable (fun t : ℝ => W (2 * t) * actualGapHeightE02_38 (finiteGapField S w) t) := by
  have hWc : Continuous W := hW2.continuous
  set a : S → ℝ := fun n => W (2 * Real.pi * ((n : ℤ) : ℝ)) with ha_def
  have ha : ∀ i, 0 < a i := fun i => hpos i
  set R : (S → ℂ) → ℝ := fun w => remainderForWeight W (finiteGapField S w) with hR_def
  have hPm : Measurable physicalOfSequence := by
    rw [show physicalOfSequence = Bk.cleanΦinv from (funext hB).symm]
    exact Bk.measurable_cleanΦinv
  have hFm : Measurable (finiteGapField S) := hPm.comp (measurable_extZero38 S)
  have hRm : Measurable R :=
    (NlsGge.ThirdConsultation.I025C.measurable_remainderForWeight W hWc).comp hFm
  have hsplit := fun w => energy_split Bk hB W hW2 hconv S w
  have hR0 : ∀ w, 0 ≤ R w := fun w => (hsplit w).2.1
  set γ := finiteComplexGaussian a with hγ
  obtain ⟨hZ1, hZ2⟩ := exp_neg_integral_pos_le_one38 γ R hRm hR0
  have hZrel : finiteRelativeNormalizer W S = ∫ w, Real.exp (-R w) ∂γ := rfl
  set gd : (S → ℂ) → ℝ := fun w => ∏ i, (a i / Real.pi) * Real.exp (-a i * ‖w i‖ ^ 2) with hgd
  have hgd0 : ∀ w, 0 ≤ gd w := fun w =>
    Finset.prod_nonneg (fun i _ => normalizedGaussianKernel_nonneg _ (ha i) (w i))
  have hK : 0 < ∏ i : S, Real.pi / a i := Finset.prod_pos (fun i _ => div_pos Real.pi_pos (ha i))
  have hden : ∀ w, Real.exp (-spectralEnergy W (finiteGapField S w)) =
      (∏ i : S, Real.pi / a i) * (gd w * Real.exp (-R w)) := by
    intro w
    rw [(hsplit w).1, neg_add, Real.exp_add]
    have e2 : Real.exp (-∑ i : S, a i * ‖w i‖ ^ 2) = ∏ i : S, Real.exp (-(a i) * ‖w i‖ ^ 2) := by
      rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have e3 : (∏ i : S, Real.pi / a i) * gd w = ∏ i : S, Real.exp (-(a i) * ‖w i‖ ^ 2) := by
      rw [hgd, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have := (ha i).ne'
      field_simp
    have e1 : (∑ i : S, W (2 * Real.pi * ((i : ℤ) : ℝ)) * ‖w i‖ ^ 2) = ∑ i : S, a i * ‖w i‖ ^ 2 := rfl
    rw [e1, e2, ← e3]
    ring
  have hm1 : Measurable (fun w : S → ℂ => ENNReal.ofReal (gd w)) :=
    (measurable_finiteGaussianPDF a).ennreal_ofReal
  have hγd : γ = (finiteComplexVolume S).withDensity (fun w => ENNReal.ofReal (gd w)) :=
    finiteComplexGaussian_density a ha
  have hintγ : ∀ f : (S → ℂ) → ℝ, ∫ w, f w ∂γ = ∫ w, gd w * f w ∂(finiteComplexVolume S) := by
    intro f
    rw [hγd, integral_withDensity_eq_integral_toReal_smul hm1
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (hgd0 w)]
  have hZabs : finiteAbsolutePartition W S = (∏ i : S, Real.pi / a i) * ∫ w, Real.exp (-R w) ∂γ := by
    unfold finiteAbsolutePartition
    rw [hintγ, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => hden w)
  have hprob : IsProbabilityMeasure (finiteGapCoordinateLaw W S) := by
    rw [NlsGge.ThirdConsultation.I017C.law_rel]
    exact isProbabilityMeasure_withDensity_exp_neg38 γ R hRm hR0
  refine ⟨?_, ?_, hZ1, hZ2, ?_, ?_, ?_, fun w => (hsplit w).2.2⟩
  · rw [hZabs]; exact mul_pos hK hZ1
  · rw [hZabs]; nlinarith
  · rw [hZrel, hZabs]; exact (mul_div_cancel_left₀ _ hK.ne').symm
  · rw [NlsGge.ThirdConsultation.I017C.law_rel]
    change γ.withDensity _ = _
    have hm2 : Measurable (fun w : S → ℂ =>
        ENNReal.ofReal (Real.exp (-R w) / finiteRelativeNormalizer W S)) :=
      ((Real.measurable_exp.comp hRm.neg).div_const _).ennreal_ofReal
    rw [hγd, ← withDensity_mul _ hm1 hm2]
    congr 1
    funext w
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hgd0 w), hden w, hZabs, ← hZrel]
    congr 1
    have := hK.ne'
    field_simp
  · unfold finiteGapLaw
    exact (Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).2 hprob

end NlsGge.ThirdConsultation.I038B
