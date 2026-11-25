import Mathlib
import NlsGge.Ramer.RamerStep8b
import NlsGge.Ramer.RamerStep7

/-!
# R8c: consequences of (**) (Ramer p.183)

See `RamerStep8c.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

section Abstract

theorem isUnit_one_add_of_norm_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H] (D : H →L[ℝ] H) (hD : ‖D‖ ≤ 1 / 2) : IsUnit (1 + D) :=
  ⟨Units.oneSub (-D) (by rw [norm_neg]; linarith), by simp [sub_neg_eq_add]⟩

end Abstract

section Step8c

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- `det₂ (I + D_H L x) ≠ 0` on `B̄`: `‖D_H L x‖ ≤ 1/2`. -/
theorem det2_hsDerivH_ne_zero (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    {ε : ℝ} (hyp : Step8Hyp c s hs L ε) {x : FullWeightedHilbert c s}
    (hx : x ∈ closedBall (0 : FullWeightedHilbert c s) ε) :
    det2 (hsDerivH c s hs L x) ≠ 0 := by
  apply det2_ne_zero_of_isUnit
  have h : ‖(hsDerivH c s hs L x).toCLM‖ ≤ 1 / 2 := by
    rw [hsDerivH_toCLM]; exact hyp.step.contr x hx
  exact isUnit_one_add_of_norm_le _ h

/-- **R8c (1)**: `J^S > 0` on `B̄`. -/
theorem ramerJE_pos_closedBall (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    {ε : ℝ} (hyp : Step8Hyp c s hs L ε) (δL : (ℤ → ℂ) → ℝ)
    {x : FullWeightedHilbert c s} (hx : x ∈ closedBall (0 : FullWeightedHilbert c s) ε) :
    0 < ramerJE c s hs L δL x := by
  rw [ramerJE_eq]
  exact mul_pos (abs_pos.2 (det2_hsDerivH_ne_zero c s hs L hyp hx)) (Real.exp_pos _)

variable {c s}

/-- **R8c (2a)**: (**) for open `O ⊆ ball 0 (ε/2)`. -/
theorem step8c_open (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c) {ε : ℝ}
    (hyp : Step8Hyp c s hs L ε) (δL : (ℤ → ℂ) → ℝ)
    (hδm : AEStronglyMeasurable δL (NlsGge.Measure.fullWeightSequenceGaussian c.val))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hδ : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun j => ramerA c s (zero_le_of_half_lt hs) (φ j) L z) atTop (𝓝 (δL z)))
    {O : Set (FullWeightedHilbert c s)} (hO : IsOpen O)
    (hOZ : O ⊆ ball (0 : FullWeightedHilbert c s) (ε / 2)) :
    ∫⁻ x in closedBall (0 : FullWeightedHilbert c s) ε ∩
        (fun y => y + inclE c s hs (L y)) ⁻¹' O,
      ENNReal.ofReal (ramerJE c s hs L δL x)
      ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) ≤
    NlsGge.Measure.fullWeightedSequenceGaussian c s O := by
  set μ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hμ
  set B := closedBall (0 : FullWeightedHilbert c s) ε with hB
  set Z := ball (0 : FullWeightedHilbert c s) (ε / 2) with hZ
  set S : FullWeightedHilbert c s → FullWeightedHilbert c s :=
    fun y => y + inclE c s hs (L y) with hS
  have hL1 : ContDiff ℝ 1 L := hyp.smooth.of_le (by norm_num)
  have hSc : Continuous S := continuous_id.add ((inclE c s hs).continuous.comp hL1.continuous)
  set J := ramerJE c s hs L δL with hJ
  have hJm : AEMeasurable J μ :=
    (aestronglyMeasurable_ramerJE c s hs L hL1 δL hδm).aemeasurable
  obtain ⟨F, hFc, hFO, hF1, hFmono, hFsup⟩ : ∃ F : ℕ → FullWeightedHilbert c s → ℝ,
      (∀ k, Continuous (F k)) ∧ (∀ k y, y ∉ O → F k y = 0) ∧ (∀ k y, F k y ≤ 1) ∧
      (∀ y, Monotone (fun k => F k y)) ∧
      (∀ y, ⨆ k, ENNReal.ofReal (F k y) = O.indicator 1 y) := by
    rcases Oᶜ.eq_empty_or_nonempty with hne | hne
    · have hOu : O = univ := by simpa using hne
      refine ⟨fun _ _ => 1, fun _ => continuous_const, fun k y hy => (hy (hOu ▸ mem_univ y)).elim,
        fun _ _ => le_rfl, fun y _ _ _ => le_rfl, fun y => ?_⟩
      simp [hOu]
    · refine ⟨fun k y => min 1 ((k : ℝ) * infDist y Oᶜ), fun k =>
        continuous_const.min (continuous_const.mul (continuous_infDist_pt _)), ?_,
        fun k y => min_le_left _ _, ?_, ?_⟩
      · intro k y hy
        simp [infDist_zero_of_mem (show y ∈ Oᶜ from hy)]
      · intro y k l hkl
        exact min_le_min le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) infDist_nonneg)
      · intro y
        by_cases hy : y ∈ O
        · rw [indicator_of_mem hy]
          have hd : 0 < infDist y Oᶜ :=
            (hO.isClosed_compl.notMem_iff_infDist_pos hne).1 (by simpa using hy)
          apply le_antisymm
          · exact iSup_le fun k => by simp
          · obtain ⟨k, hk⟩ := exists_nat_ge (1 / infDist y Oᶜ)
            refine le_iSup_of_le k ?_
            have : 1 ≤ (k : ℝ) * infDist y Oᶜ := by
              rw [div_le_iff₀ hd] at hk; exact hk
            simp [this]
        · rw [indicator_of_notMem hy]
          simp [infDist_zero_of_mem (show y ∈ Oᶜ from hy)]
  have hF0 : ∀ k y, y ∉ ball (0 : FullWeightedHilbert c s) (ε / 2) → F k y = 0 :=
    fun k y hy => hFO k y (fun h => hy (hOZ h))
  have hstep : ∀ k, ∫⁻ x in B ∩ S ⁻¹' Z,
      ENNReal.ofReal (F k (S x)) * ENNReal.ofReal (J x) ∂μ ≤ μ O := by
    intro k
    refine (step8b c s hs L hyp δL φ hφ hδ (F k) (hFc k) (hF0 k)).trans ?_
    calc ∫⁻ x in Z, ENNReal.ofReal (F k x) ∂μ ≤ ∫⁻ x in Z, O.indicator 1 x ∂μ := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ O
          · rw [indicator_of_mem hy]; simpa using ENNReal.ofReal_le_one.2 (hF1 k y)
          · rw [hFO k y hy]; simp
      _ ≤ ∫⁻ x, O.indicator 1 x ∂μ := setLIntegral_le_lintegral _ _
      _ = μ O := by simp [lintegral_indicator_one hO.measurableSet]
  have hZm : MeasurableSet (S ⁻¹' Z) := (isOpen_ball.preimage hSc).measurableSet
  have hOm : MeasurableSet (S ⁻¹' O) := (hO.preimage hSc).measurableSet
  have hsub : B ∩ S ⁻¹' O = (B ∩ S ⁻¹' Z) ∩ S ⁻¹' O := by
    ext x; simp only [mem_inter_iff, mem_preimage]
    exact ⟨fun ⟨a, b⟩ => ⟨⟨a, hOZ b⟩, b⟩, fun ⟨⟨a, _⟩, b⟩ => ⟨a, b⟩⟩
  have hBm : MeasurableSet (B ∩ S ⁻¹' Z) := measurableSet_closedBall.inter hZm
  calc ∫⁻ x in B ∩ S ⁻¹' O, ENNReal.ofReal (J x) ∂μ
      = ∫⁻ x in B ∩ S ⁻¹' Z, (S ⁻¹' O).indicator (fun x => ENNReal.ofReal (J x)) x ∂μ := by
        rw [hsub, lintegral_indicator hOm, Measure.restrict_restrict hOm,
          Set.inter_comm (S ⁻¹' O)]
    _ = ∫⁻ x in B ∩ S ⁻¹' Z, ⨆ k, ENNReal.ofReal (F k (S x)) * ENNReal.ofReal (J x) ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.iSup_mul, hFsup]
        by_cases hx : S x ∈ O
        · simp [hx]
        · simp [hx]
    _ = ⨆ k, ∫⁻ x in B ∩ S ⁻¹' Z, ENNReal.ofReal (F k (S x)) * ENNReal.ofReal (J x) ∂μ := by
        refine lintegral_iSup' (fun k => ?_) (Eventually.of_forall fun x k l hkl => ?_)
        · exact ((hFc k).comp hSc).measurable.ennreal_ofReal.aemeasurable.mul
            (hJm.ennreal_ofReal.mono_measure Measure.restrict_le_self)
        · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hFmono (S x) hkl)) _
    _ ≤ μ O := iSup_le hstep

/-- **R8c (2b)**: (**) for every set `M ⊆ ball 0 (ε/2)` (outer regularity of `γ_E`). -/
theorem step8c_set (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c) {ε : ℝ}
    (hyp : Step8Hyp c s hs L ε) (δL : (ℤ → ℂ) → ℝ)
    (hδm : AEStronglyMeasurable δL (NlsGge.Measure.fullWeightSequenceGaussian c.val))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hδ : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun j => ramerA c s (zero_le_of_half_lt hs) (φ j) L z) atTop (𝓝 (δL z)))
    {M : Set (FullWeightedHilbert c s)}
    (hMZ : M ⊆ ball (0 : FullWeightedHilbert c s) (ε / 2)) :
    ∫⁻ x in closedBall (0 : FullWeightedHilbert c s) ε ∩
        (fun y => y + inclE c s hs (L y)) ⁻¹' M,
      ENNReal.ofReal (ramerJE c s hs L δL x)
      ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) ≤
    NlsGge.Measure.fullWeightedSequenceGaussian c s M := by
  set μ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hμ
  rw [Set.measure_eq_iInf_isOpen M μ]
  refine le_iInf fun U => le_iInf fun hMU => le_iInf fun hU => ?_
  have hO : IsOpen (U ∩ ball (0 : FullWeightedHilbert c s) (ε / 2)) := hU.inter isOpen_ball
  calc _ ≤ ∫⁻ x in closedBall (0 : FullWeightedHilbert c s) ε ∩
        (fun y => y + inclE c s hs (L y)) ⁻¹' (U ∩ ball (0 : FullWeightedHilbert c s) (ε / 2)),
      ENNReal.ofReal (ramerJE c s hs L δL x) ∂μ := by
        refine lintegral_mono_set (inter_subset_inter_right _ (preimage_mono ?_))
        exact subset_inter hMU hMZ
    _ ≤ μ (U ∩ ball (0 : FullWeightedHilbert c s) (ε / 2)) :=
        step8c_open hs L hyp δL hδm φ hφ hδ hO inter_subset_right
    _ ≤ μ U := measure_mono inter_subset_left

/-- **R8c (3)**: null sets are preserved by `S` on `B̄`. -/
theorem step8c_null (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c) {ε : ℝ}
    (hyp : Step8Hyp c s hs L ε) (δL : (ℤ → ℂ) → ℝ)
    (hδm : AEStronglyMeasurable δL (NlsGge.Measure.fullWeightSequenceGaussian c.val))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hδ : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun j => ramerA c s (zero_le_of_half_lt hs) (φ j) L z) atTop (𝓝 (δL z)))
    {M : Set (FullWeightedHilbert c s)} (hM : MeasurableSet M)
    (hMZ : M ⊆ ball (0 : FullWeightedHilbert c s) (ε / 2))
    (h0 : NlsGge.Measure.fullWeightedSequenceGaussian c s M = 0) :
    NlsGge.Measure.fullWeightedSequenceGaussian c s
      (closedBall (0 : FullWeightedHilbert c s) ε ∩
        (fun y => y + inclE c s hs (L y)) ⁻¹' M) = 0 := by
  set μ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hμ
  set A := closedBall (0 : FullWeightedHilbert c s) ε ∩
        (fun y => y + inclE c s hs (L y)) ⁻¹' M with hA
  have hL1 : ContDiff ℝ 1 L := hyp.smooth.of_le (by norm_num)
  have hSc : Continuous (fun y => y + inclE c s hs (L y)) :=
    continuous_id.add ((inclE c s hs).continuous.comp hL1.continuous)
  have hAm : MeasurableSet A := measurableSet_closedBall.inter (hM.preimage hSc.measurable)
  have hle := step8c_set hs L hyp δL hδm φ hφ hδ hMZ
  rw [h0, nonpos_iff_eq_zero] at hle
  have hJm : AEMeasurable (fun x => ENNReal.ofReal (ramerJE c s hs L δL x)) (μ.restrict A) :=
    ((aestronglyMeasurable_ramerJE c s hs L hL1 δL hδm).aemeasurable.ennreal_ofReal).mono_measure
      Measure.restrict_le_self
  have h1 := (lintegral_eq_zero_iff' hJm).1 hle
  have h2 : ∀ᵐ x ∂μ.restrict A, False := by
    filter_upwards [h1, ae_restrict_mem hAm] with x hx hxA
    have := ramerJE_pos_closedBall c s hs L hyp δL hxA.1
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
    linarith
  have h3 := ae_iff.1 h2
  simpa [Measure.restrict_apply_univ] using h3

/-- **R8c, packaged**: with `δL` from L3b (`step8b_divergence`). -/
theorem step8c (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c) {ε : ℝ}
    (hyp : Step8Hyp c s hs L ε) :
    ∃ δL : (ℤ → ℂ) → ℝ,
      AEStronglyMeasurable δL (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
      (∀ x ∈ closedBall (0 : FullWeightedHilbert c s) ε, 0 < ramerJE c s hs L δL x) ∧
      (∀ M : Set (FullWeightedHilbert c s), M ⊆ ball (0 : FullWeightedHilbert c s) (ε / 2) →
        ∫⁻ x in closedBall (0 : FullWeightedHilbert c s) ε ∩
            (fun y => y + inclE c s hs (L y)) ⁻¹' M,
          ENNReal.ofReal (ramerJE c s hs L δL x)
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) ≤
        NlsGge.Measure.fullWeightedSequenceGaussian c s M) ∧
      (∀ M : Set (FullWeightedHilbert c s), MeasurableSet M →
        M ⊆ ball (0 : FullWeightedHilbert c s) (ε / 2) →
        NlsGge.Measure.fullWeightedSequenceGaussian c s M = 0 →
        NlsGge.Measure.fullWeightedSequenceGaussian c s
          (closedBall (0 : FullWeightedHilbert c s) ε ∩
            (fun y => y + inclE c s hs (L y)) ⁻¹' M) = 0) := by
  obtain ⟨δL, hm, ⟨φ, hφ, hlim⟩, -⟩ := step8b_divergence c s hs L hyp
  exact ⟨δL, hm, fun x hx => ramerJE_pos_closedBall c s hs L hyp δL hx,
    fun M hM => step8c_set hs L hyp δL hm φ hφ hlim hM,
    fun M hMm hM h0 => step8c_null hs L hyp δL hm φ hφ hlim hMm hM h0⟩

end Step8c

end NlsGge.Ramer

