import Mathlib
import NlsGge.ThirdConsultation.I.FiniteGapLaws
import NlsGge.Birkhoff.S04Moments38

/- I-017 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORT (no packet increment).
   Target NlsGge/Atomic/I/I017Core.lean, namespace NlsGge.ThirdConsultation.I017C.
   Pro's I-017 route ("specializes the fixed G6 physical map"; source A:eq:finitecanonical, A:eq:relativefinite,
   Birkhoff/S04Moments38 ZcalΛ38_eq, nuHat38_eq_relative): for ANY house record B : BirkhoffTop38 whose cleaned inverse
   is the I inverse on all sequences (hB, the round-14 bridge `actual_inverse_eq_physicalOfSequence` for
   B = PDE.actualBirkhoffTop38), the literal I-017 conclusion holds.  hB is a hypothesis of this SUPPORT lemma only;
   the glue I017.lean discharges it with the concrete record and the proved bridge, so i017 itself has no extra binder.
   Reuse (house, B-generic, all landed): finiteGap_structure38, remainder38_finiteGap_proj, integrable_energyIntegrand38,
   densΛ38_eq, ZcalΛ38_pos_le, ZΛ38_eq_integral, ZΛ38_pos_le_one, nuHat38_eq_relative, isProbabilityMeasure_nuHat38,
   isProbabilityMeasure_nu38, gammaΛ38_density, Rbar38_of_mem, projFin38_mem_Omega038, projFin38_extZero38,
   remainderSummand38_eq_gapRemainderTerm, weight_continuous38.  Normalizations are the house ones: rate W(2πn), complex
   Gaussian (a/π)e^{-a|z|²} (real-component variance 1/(2a)), product complex Lebesgue measure, factor 2/π; empty Λ and
   zero coordinates are not excluded anywhere. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.I010 (spectralEnergy)
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.I017C

/-- `Φ(0) = 0` for the selected physical map (X-006 `Phi_mass` at `u = 0`). -/
theorem physicalBirkhoff_zero : physicalBirkhoff 0 = 0 := by
  have h := (sourceFamily.Phi_mass 0).2
  rw [norm_zero] at h
  have h' : ‖physicalBirkhoff 0‖ ^ 2 = 0 := by
    change ‖sourceFamily.Phi 0‖ ^ 2 = 0
    rw [h]; norm_num
  exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h')

/-- Support for the round-14 bridge `actual_inverse_eq_physicalOfSequence`: a house record whose cleaned inverse is
    `physicalInverseBirkhoff` on `h⁰`, with `physicalInverseBirkhoff 0 = 0`, has cleaned inverse equal to the I inverse on
    ALL sequences (the off-`h⁰` branch of both is the field `0`). -/
theorem cleanΦinv_eq_of (B : BirkhoffTop38)
    (hmem : ∀ (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0), B.cleanΦinv z = physicalInverseBirkhoff (seqToLp38 z hz))
    (h0 : physicalInverseBirkhoff 0 = 0) (z : ℤ → ℂ) :
    B.cleanΦinv z = physicalOfSequence z := by
  by_cases h : Memℓp z 2
  · have hz : z ∈ seqSobolev38 0 := (mem_seqSobolev38_zero_iff z).2 h
    rw [hmem z hz]
    unfold physicalOfSequence
    rw [dif_pos h]
    rfl
  · have hz : z ∉ seqSobolev38 0 := fun hz => h ((mem_seqSobolev38_zero_iff z).1 hz)
    unfold BirkhoffTop38.cleanΦinv physicalOfSequence
    rw [dif_neg hz, dif_neg h, h0]

theorem field_eq38 (B : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (Λ : Finset ℤ) : finiteGapField Λ = B.finiteGapField38 Λ :=
  funext fun w => (hB (extZero38 Λ w)).symm

theorem field_eq_proj (B : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (Λ : Finset ℤ) (w : Λ → ℂ) :
    finiteGapField Λ w = B.cleanΦinv (projFin38 Λ (extZero38 Λ w)) := by
  rw [projFin38_extZero38]; exact (hB (extZero38 Λ w)).symm

theorem remainderForWeight_eq (c : ℕ → ℝ) (hW : Continuous (weight c)) (u : PhysicalL2) :
    remainderForWeight (weight c) u = remainder38 c u := by
  unfold remainderForWeight remainder38
  exact tsum_congr fun n => (remainderSummand38_eq_gapRemainderTerm c hW u n).symm

theorem spectralEnergy_eq (c : ℕ → ℝ) (u : PhysicalL2) : spectralEnergy (weight c) u = energyW38 c u := rfl

theorem sum_extZero (c : ℕ → ℝ) (Λ : Finset ℤ) (w : Λ → ℂ) :
    ∑ n ∈ Λ, fullWeightRate c n * ‖extZero38 Λ w n‖ ^ 2 = ∑ n : Λ, fullWeightRate c n * ‖w n‖ ^ 2 := by
  rw [← Finset.sum_coe_sort Λ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [extZero38_apply_of_mem w i.2]

theorem rem_eq (B : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (c : ℕ → ℝ) (hW : Continuous (weight c)) (Λ : Finset ℤ) (w : Λ → ℂ) :
    remainderForWeight (weight c) (finiteGapField Λ w) = B.Rbar38 c (extZero38 Λ w) := by
  have hmem : extZero38 Λ w ∈ Omega038 c := by
    have := projFin38_mem_Omega038 c Λ (extZero38 Λ w)
    rwa [projFin38_extZero38] at this
  rw [remainderForWeight_eq c hW, B.Rbar38_of_mem c hmem, field_eq38 B hB]
  rfl

theorem dens_eq (B : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (c : ℕ → ℝ) (Λ : Finset ℤ) (w : Λ → ℂ) :
    Real.exp (-spectralEnergy (weight c) (finiteGapField Λ w)) = B.densΛ38 c Λ w := by
  rw [field_eq38 B hB]; rfl

theorem gapTerm_zero (W : ℝ → ℝ) (u : PhysicalL2) (n : ℤ)
    (hn : ¬ actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n) :
    gapRemainderTermE02_38 W u n = 0 := by
  have hle := actualGapLower_le_upper38' u n
  have heq : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n := le_antisymm hle (not_lt.1 hn)
  unfold gapRemainderTermE02_38
  rw [heq, intervalIntegral.integral_same, mul_zero]

/-- The pointwise block of I-017. -/
theorem pointwise (B : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (Λ : Finset ℤ) (w : Λ → ℂ) :
    Integrable (fun t : ℝ => weight c (2 * t) * actualGapHeightE02_38 (finiteGapField Λ w) t) ∧
      Summable (fun n : ℤ => |gapRemainderTermE02_38 (weight c) (finiteGapField Λ w) n|) ∧
      (∑ n : Λ, fullWeightRate c n * ‖w n‖ ^ 2) ≤ spectralEnergy (weight c) (finiteGapField Λ w) ∧
      remainderForWeight (weight c) (finiteGapField Λ w) =
        spectralEnergy (weight c) (finiteGapField Λ w) - (∑ n : Λ, fullWeightRate c n * ‖w n‖ ^ 2) := by
  have hW := weight_continuous38 hlower hbound hupper
  have hrem := remainderForWeight_eq c hW (finiteGapField Λ w)
  rw [field_eq_proj B hB Λ w] at hrem ⊢
  obtain ⟨-, hfin, -⟩ := B.finiteGap_structure38 Λ (extZero38 Λ w)
  obtain ⟨-, heq, hnn⟩ := B.remainder38_finiteGap_proj lower upper c hlower hbound hupper Λ (extZero38 Λ w)
  rw [sum_extZero] at heq
  rw [spectralEnergy_eq]
  unfold energyW38
  refine ⟨integrable_energyIntegrand38 c hW _ hfin, ?_, ?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := hfin.toFinset) (fun n hn => ?_)
    rw [gapTerm_zero _ _ n (fun h => hn (by simpa using h)), abs_zero]
  · linarith
  · rw [hrem, heq]

theorem integrable_dens (B : BirkhoffTop38)
    (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (Λ : Finset ℤ) :
    Integrable (fun w : Λ → ℂ => B.densΛ38 c Λ w) (finiteComplexVolume Λ) := by
  haveI : IsProbabilityMeasure (gammaΛ38 c Λ) := by unfold gammaΛ38; infer_instance
  have hR := B.measurable_Rext38 lower upper c hlower hbound hupper Λ
  have hiγ : Integrable (fun w : Λ → ℂ => Real.exp (-(B.Rbar38 c (extZero38 Λ w)))) (gammaΛ38 c Λ) :=
    Integrable.of_bound (Real.measurable_exp.comp hR.neg).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        linarith [B.Rext_nonneg38 lower upper c hlower hbound hupper Λ w])
  have hm1 : Measurable (fun w : Λ → ℂ => ENNReal.ofReal (BirkhoffTop38.gaussDensΛ38 c Λ w)) :=
    (measurable_finiteGaussianPDF (rateΛ38 c Λ)).ennreal_ofReal
  rw [BirkhoffTop38.gammaΛ38_density lower upper c hlower hbound hupper Λ,
    integrable_withDensity_iff_integrable_smul' hm1
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hiγ
  have hi2 : Integrable (fun w : Λ → ℂ =>
      BirkhoffTop38.gaussDensΛ38 c Λ w * Real.exp (-(B.Rbar38 c (extZero38 Λ w)))) (finiteComplexVolume Λ) := by
    refine hiγ.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (BirkhoffTop38.gaussDensΛ38_nonneg lower upper c hlower hbound hupper Λ w)]
  refine (hi2.const_mul (∏ i : Λ, Real.pi / rateΛ38 c Λ i)).congr
    (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [B.densΛ38_eq lower upper c hlower hbound hupper Λ w]

theorem abs_eq (B : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (c : ℕ → ℝ) (Λ : Finset ℤ) : finiteAbsolutePartition (weight c) Λ = B.ZcalΛ38 c Λ := by
  unfold finiteAbsolutePartition BirkhoffTop38.ZcalΛ38
  exact integral_congr_ae (Filter.Eventually.of_forall fun w => dens_eq B hB c Λ w)

theorem rel_eq (B : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (Λ : Finset ℤ) :
    finiteRelativeNormalizer (weight c) Λ = B.ZΛ38 c Λ := by
  have hW := weight_continuous38 hlower hbound hupper
  rw [B.ZΛ38_eq_integral lower upper c hlower hbound hupper Λ]
  unfold finiteRelativeNormalizer gibbsPartition38
  change ∫ w, Real.exp (-(remainderForWeight (weight c) (finiteGapField Λ w))) ∂(gammaΛ38 c Λ) = _
  exact integral_congr_ae (Filter.Eventually.of_forall fun w => by
    simp only [rem_eq B hB c hW Λ w])

theorem law_rel (W : ℝ → ℝ) (Λ : Finset ℤ) :
    finiteGapCoordinateLaw W Λ = (finiteComplexGaussian (fun n : Λ =>
      W (2 * Real.pi * ((n : ℤ) : ℝ)))).withDensity
      (fun w => ENNReal.ofReal (Real.exp (-remainderForWeight W (finiteGapField Λ w)) /
        finiteRelativeNormalizer W Λ)) := rfl

theorem law_eq_nuHat (B : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (Λ : Finset ℤ) :
    finiteGapCoordinateLaw (weight c) Λ = B.nuHat38 c Λ := by
  have hW := weight_continuous38 hlower hbound hupper
  rw [law_rel, B.nuHat38_eq_relative lower upper c hlower hbound hupper Λ,
    rel_eq B hB lower upper c hlower hbound hupper Λ]
  change (gammaΛ38 c Λ).withDensity _ = _
  congr 1
  funext w
  rw [rem_eq B hB c hW Λ w]

/-- I-017 for any house record whose cleaned inverse is the I inverse. -/
theorem i017_of (B : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) (Λ : Finset ℤ) :
    let W := weight c.val
    (∀ w : Λ → ℂ,
      Integrable (fun t : ℝ => W (2 * t) * actualGapHeightE02_38 (finiteGapField Λ w) t) ∧
      Summable (fun n : ℤ => |gapRemainderTermE02_38 W (finiteGapField Λ w) n|) ∧
      (∑ n : Λ, fullWeightRate c.val n * ‖w n‖ ^ 2) ≤
        spectralEnergy W (finiteGapField Λ w) ∧
      remainderForWeight W (finiteGapField Λ w) =
        spectralEnergy W (finiteGapField Λ w) -
          (∑ n : Λ, fullWeightRate c.val n * ‖w n‖ ^ 2)) ∧
    Integrable (fun w : Λ → ℂ => Real.exp (-spectralEnergy W (finiteGapField Λ w)))
      (finiteComplexVolume Λ) ∧
    0 < finiteAbsolutePartition W Λ ∧
    finiteAbsolutePartition W Λ ≤ ∏ n : Λ, Real.pi / fullWeightRate c.val n ∧
    0 < finiteRelativeNormalizer W Λ ∧ finiteRelativeNormalizer W Λ ≤ 1 ∧
    finiteRelativeNormalizer W Λ =
      finiteAbsolutePartition W Λ / (∏ n : Λ, Real.pi / fullWeightRate c.val n) ∧
    finiteGapCoordinateLaw W Λ = (finiteComplexVolume Λ).withDensity
      (fun w => ENNReal.ofReal (Real.exp (-spectralEnergy W (finiteGapField Λ w)) /
        finiteAbsolutePartition W Λ)) ∧
    finiteGapCoordinateLaw W Λ = (gammaΛ38 c.val Λ).withDensity
      (fun w => ENNReal.ofReal (Real.exp (-remainderForWeight W (finiteGapField Λ w)) /
        finiteRelativeNormalizer W Λ)) ∧
    IsProbabilityMeasure (finiteGapCoordinateLaw W Λ) ∧ IsProbabilityMeasure (finiteGapLaw W Λ) := by
  intro W
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  have hAbs := abs_eq B hB c.val Λ
  have hRel := rel_eq B hB lower upper c.val hl hb' hu' Λ
  have hNu := law_eq_nuHat B hB lower upper c.val hl hb' hu' Λ
  obtain ⟨hZc1, hZc2⟩ := B.ZcalΛ38_pos_le lower upper c.val hl hb' hu' Λ
  obtain ⟨hZ1, hZ2⟩ := B.ZΛ38_pos_le_one lower upper c.val hl hb' hu' Λ
  refine ⟨fun w => pointwise B hB lower upper c.val hl hb' hu' Λ w, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (integrable_dens B lower upper c.val hl hb' hu' Λ).congr
      (Filter.Eventually.of_forall fun w => ?_)
    exact (dens_eq B hB c.val Λ w).symm
  · rw [hAbs]; exact hZc1
  · rw [hAbs]; exact hZc2
  · rw [hRel]; exact hZ1
  · rw [hRel]; exact hZ2
  · rw [hRel, hAbs]; rfl
  · rw [hNu]
    unfold BirkhoffTop38.nuHat38
    congr 1
    funext w
    rw [dens_eq B hB c.val Λ w, hAbs]
  · exact law_rel W Λ
  · rw [hNu]; exact B.isProbabilityMeasure_nuHat38 lower upper c.val hl hb' hu' Λ
  · unfold finiteGapLaw
    rw [hNu, field_eq38 B hB Λ]
    exact B.isProbabilityMeasure_nu38 lower upper c.val hl hb' hu' Λ

end NlsGge.ThirdConsultation.I017C
