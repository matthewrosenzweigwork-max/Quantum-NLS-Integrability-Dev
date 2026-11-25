import Mathlib
import NlsGge.Ramer.SpaceTransfer
import NlsGge.Ramer.ConstantShiftInverseOrientation
import NlsGge.Ramer.RamerLemma54
import NlsGge.Ramer.RamerJacobianHead
import NlsGge.Measure.ActualSourceCMFiniteScoreEvaluationPrerequisiteV1

/-!
# CM-E: the Cameron–Martin theorem on `E_s`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

section CME

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- The approximant of a constant field is the finite CM score, everywhere. -/
theorem ramerA_const_eq_score (hs : (1 : ℝ) / 2 < s) (n : ℕ) (e : ActualCM c) (z : ℤ → ℂ) :
    ramerA c s (zero_le_of_half_lt hs) n (fun _ => e) z =
      NlsGge.Measure.actualSourceCMFiniteScorePartial c e n z := by
  rw [ramerA_const hs n e z, NlsGge.Measure.actualSourceCMFiniteScorePartial_eq_coordinate_sum_v1]
  unfold basisIndex
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hw : 0 ≤ cmModeWeight c m := (cmModeWeight_pos c m).le
  have hb : ∀ (j : Fin 2) (x : ActualCM c),
      ⟪weightedRealHilbertBasis (cmModeWeight c) (m, j), x⟫ =
        ⟪Complex.orthonormalBasisOneI j,
          ((Real.sqrt (cmModeWeight c m) : ℝ) : ℂ) * cmCoord x m⟫ := by
    intro j x
    rw [weightedRealHilbertBasis_apply, weightedRealBasisVector_inner]
    rfl
  have hz : cmCoord (headPt c n z : ActualCM c) m = z m := by
    simp [cmCoord_headPt, hm]
  calc ∑ j : Fin 2, ⟪(headPt c n z : ActualCM c),
          weightedRealHilbertBasis (cmModeWeight c) (m, j)⟫ *
        ⟪weightedRealHilbertBasis (cmModeWeight c) (m, j), e⟫
      = ∑ j : Fin 2, ⟪Complex.orthonormalBasisOneI j,
          ((Real.sqrt (cmModeWeight c m) : ℝ) : ℂ) * z m⟫ *
        ⟪Complex.orthonormalBasisOneI j,
          ((Real.sqrt (cmModeWeight c m) : ℝ) : ℂ) * cmCoord e m⟫ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have h1 : ⟪(headPt c n z : ActualCM c),
            weightedRealHilbertBasis (cmModeWeight c) (m, j)⟫ =
            ⟪weightedRealHilbertBasis (cmModeWeight c) (m, j),
              (headPt c n z : ActualCM c)⟫ := real_inner_comm _ _
        rw [h1, hb, hb, hz]
    _ = ⟪((Real.sqrt (cmModeWeight c m) : ℝ) : ℂ) * z m,
          ((Real.sqrt (cmModeWeight c m) : ℝ) : ℂ) * cmCoord e m⟫ := by
        rw [← OrthonormalBasis.sum_inner_mul_inner Complex.orthonormalBasisOneI]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [real_inner_comm _ (Complex.orthonormalBasisOneI j)]
    _ = cmModeWeight c m * ⟪cmCoord e m, z m⟫ := by
        simp only [← Complex.real_smul, real_inner_smul_left, real_inner_smul_right]
        rw [← mul_assoc, Real.mul_self_sqrt hw, real_inner_comm]

/-- The finite CM score classes are a.e. equal to `ramerA n (const e)`. -/
theorem score_Lp_ae_eq_ramerA (hs : (1 : ℝ) / 2 < s) (n : ℕ) (e : ActualCM c) :
    (NlsGge.Measure.actualSourceCMFiniteScorePartialLp c e n : (ℤ → ℂ) → ℝ) =ᵐ[
        NlsGge.Measure.fullWeightSequenceGaussian c.val]
      ramerA c s (zero_le_of_half_lt hs) n (fun _ => e) := by
  have h : (NlsGge.Measure.actualSourceCMFiniteScorePartialLp c e n : (ℤ → ℂ) → ℝ) =ᵐ[
        NlsGge.Measure.fullWeightSequenceGaussian c.val]
      NlsGge.Measure.actualSourceCMFiniteScorePartial c e n := by
    unfold NlsGge.Measure.actualSourceCMFiniteScorePartialLp
    exact MemLp.coeFn_toLp _
  refine h.trans (Filter.Eventually.of_forall fun z => ?_)
  exact (ramerA_const_eq_score c s hs n e z).symm

/-- **Goal 1.** The Ramer divergence of the constant field `e` is the `L²` limit `S` of the
finite CM scores of `e`, `γ`-a.e. -/
theorem ramerDiv_const_ae_eq (hs : (1 : ℝ) / 2 < s) (e : ActualCM c)
    (S : Lp ℝ 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val))
    (hS : Tendsto (fun N : ℕ => NlsGge.Measure.actualSourceCMFiniteScorePartialLp c e N)
      atTop (𝓝 S)) :
    ramerDiv c s hs (fun _ => e) =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val] (S : (ℤ → ℂ) → ℝ) := by
  have h1 := (ramerDiv_spec c s hs (fun _ => e) contDiff_const).2.2
  have h2 := (tendstoInMeasure_of_tendsto_Lp hS).congr_left
    (fun n => score_Lp_ae_eq_ramerA c s hs n e)
  exact tendstoInMeasure_ae_unique h1 h2

theorem coordE_inclE (hs : (1 : ℝ) / 2 < s) (e : ActualCM c) :
    coordE c s (inclE c s hs e) = NlsGge.Measure.actualSourceCMSequence c e := rfl

theorem coordE_sub_inclE (hs : (1 : ℝ) / 2 < s) (e : ActualCM c) (x : FullWeightedHilbert c s) :
    coordE c s (x - inclE c s hs e) =
      fun n => coordE c s x n - NlsGge.Measure.actualSourceCMSequence c e n := by
  funext n; rfl

theorem coordE_add_inclE (hs : (1 : ℝ) / 2 < s) (e : ActualCM c) (x : FullWeightedHilbert c s) :
    coordE c s (x + inclE c s hs e) =
      fun n => coordE c s x n + NlsGge.Measure.actualSourceCMSequence c e n := by
  funext n; rfl

/-- The density of Goal 2 as a function on sequences. -/
theorem aemeasurable_constDensity (hs : (1 : ℝ) / 2 < s) (e : ActualCM c) :
    AEMeasurable (fun x : FullWeightedHilbert c s =>
      ENNReal.ofReal (ramerJac c s hs (fun _ => e) x))
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  have h := (ramerDiv_spec c s hs (fun _ => e) contDiff_const).1.aemeasurable
  have h2 : AEMeasurable (fun z => ENNReal.ofReal (Real.exp (-(ramerDiv c s hs (fun _ => e) z)
      - ‖e‖ ^ 2 / 2))) (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
    (Real.measurable_exp.comp_aemeasurable (h.neg.sub_const _)).ennreal_ofReal
  have h3 := h2.comp_quasiMeasurePreserving
    (measurePreserving_coordE c s hs).quasiMeasurePreserving
  refine h3.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp, ramerJac_const hs e x]

/-- **Goal 2.** Cameron–Martin on `E_s`, inverse-pushforward orientation:
`(x ↦ x - i e)_# γ_E = J^{const e} · γ_E`, `J^{const e} = exp(-δe - ‖e‖²/2)`. -/
theorem map_sub_inclE_eq_withDensity (hs : (1 : ℝ) / 2 < s) (e : ActualCM c) :
    (NlsGge.Measure.fullWeightedSequenceGaussian c s).map
        (fun x => x - inclE c s hs e) =
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (ramerJac c s hs (fun _ => e) x)) := by
  obtain ⟨S, hS, hmeas, hmass, hmap⟩ :=
    NlsGge.Ramer.exists_actualSourceCM_inverseShift_negativeScoreDensity c e
  have hdiv := ramerDiv_const_ae_eq c s hs e S hS
  have hQ : (∑' n : ℤ, cmModeWeight c n *
      ‖NlsGge.Measure.actualSourceCMSequence c e n‖ ^ 2) = ‖e‖ ^ 2 :=
    (actualCM_norm_sq e).symm
  rw [hQ] at hmap
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  set R := NlsGge.Measure.fullWeightedSequenceRealization c s with hR
  set D : (ℤ → ℂ) → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (-S z - ‖e‖ ^ 2 / 2)) with hD
  have hγE : NlsGge.Measure.fullWeightedSequenceGaussian c s = Measure.map R γ := rfl
  have hRm : Measurable R := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hτ : Measurable (fun x : FullWeightedHilbert c s => x - inclE c s hs e) :=
    measurable_id.sub_const _
  have hQm : Measurable (fun z : ℤ → ℂ => fun n => z n -
      NlsGge.Measure.actualSourceCMSequence c e n) :=
    measurable_pi_iff.2 fun n => (measurable_pi_apply n).sub_const _
  have hcoord := coordE_realization_ae c s hs
  refine Measure.ext fun A hA => ?_
  -- left side
  have hL : (Measure.map (fun x => x - inclE c s hs e)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s)) A =
      (Measure.map (fun z : ℤ → ℂ => fun n => z n -
        NlsGge.Measure.actualSourceCMSequence c e n) γ) (R ⁻¹' A) := by
    rw [Measure.map_apply hτ hA, Measure.map_apply hQm (hRm hA), hγE,
      Measure.map_apply hRm (hτ hA)]
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hcoord] with z hz
    have : (fun x : FullWeightedHilbert c s => x - inclE c s hs e) (R z) =
        R (fun n => z n - NlsGge.Measure.actualSourceCMSequence c e n) := by
      simp only
      rw [← realization_coordE c s (R z - inclE c s hs e), coordE_sub_inclE, hz]
    simp only [Set.mem_preimage, this]
  rw [hL, hmap, withDensity_apply _ (hRm hA), withDensity_apply _ hA]
  rw [← lintegral_indicator (hRm hA), ← lintegral_indicator hA, hγE]
  have hind : AEMeasurable (A.indicator (fun x : FullWeightedHilbert c s =>
      ENNReal.ofReal (ramerJac c s hs (fun _ => e) x))) (Measure.map R γ) := by
    rw [← hγE]; exact (aemeasurable_constDensity c s hs e).indicator hA
  rw [lintegral_map' hind hRm.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [hcoord, hdiv] with z hz hd
  rw [← Set.indicator_comp_right (R) (g := fun x => ENNReal.ofReal
    (ramerJac c s hs (fun _ => e) x))]
  by_cases hzA : z ∈ R ⁻¹' A
  · have hz' : coordE c s (R z) = z := hz
    simp only [Set.indicator_of_mem hzA, Function.comp, ramerJac_const hs e (R z), hz', hd]
  · simp only [Set.indicator_of_notMem hzA]

/-- **Goal 2, `+` form.** `(x ↦ x + i e)_# γ_E = J^{const (-e)} · γ_E`. -/
theorem map_add_inclE_eq_withDensity (hs : (1 : ℝ) / 2 < s) (e : ActualCM c) :
    (NlsGge.Measure.fullWeightedSequenceGaussian c s).map
        (fun x => x + inclE c s hs e) =
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (ramerJac c s hs (fun _ => -e) x)) := by
  have h := map_sub_inclE_eq_withDensity c s hs (-e)
  simpa only [map_neg, sub_neg_eq_add] using h

/-- **Goal 3 (minus).** -/
theorem quasiMeasurePreserving_sub_inclE (hs : (1 : ℝ) / 2 < s) (e : ActualCM c) :
    Measure.QuasiMeasurePreserving (fun x : FullWeightedHilbert c s => x - inclE c s hs e)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) :=
  ⟨measurable_id.sub_const _, by
    rw [map_sub_inclE_eq_withDensity c s hs e]
    exact withDensity_absolutelyContinuous _ _⟩

/-- **Goal 3.** For every `e ∈ H`, translation by `i e` is quasi-measure-preserving on `γ_E`. -/
theorem quasiMeasurePreserving_add_inclE (hs : (1 : ℝ) / 2 < s) (e : ActualCM c) :
    Measure.QuasiMeasurePreserving (fun x : FullWeightedHilbert c s => x + inclE c s hs e)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) :=
  ⟨measurable_id.add_const _, by
    rw [map_add_inclE_eq_withDensity c s hs e]
    exact withDensity_absolutelyContinuous _ _⟩

/-- Null-set preservation by a translation on any `U` (R9c's `hT` shape for `T = τ_{ie}`). -/
theorem translation_null_preserving (hs : (1 : ℝ) / 2 < s) (e : ActualCM c)
    (U : Set (FullWeightedHilbert c s)) :
    ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s
        (U ∩ (fun y => y + inclE c s hs e) ⁻¹' N) = 0 := fun _ hN =>
  measure_mono_null Set.inter_subset_right
    ((quasiMeasurePreserving_add_inclE c s hs e).preimage_null hN)

/-- Truncations of the constant field are translations by `i (P_k e)`. -/
theorem TM_projField_const (hs : (1 : ℝ) / 2 < s) (k : ℕ) (e : ActualCM c) :
    TM c s hs (projField k (fun _ : FullWeightedHilbert c s => e)) =
      fun y => y + inclE c s hs (headProj c k e) := rfl

theorem TM_const (hs : (1 : ℝ) / 2 < s) (e : ActualCM c) :
    TM c s hs (fun _ : FullWeightedHilbert c s => e) = fun y => y + inclE c s hs e := rfl

/-- R9c's `hT` for `T = TM (const e)`, on any `U`. -/
theorem hT_TM_const (hs : (1 : ℝ) / 2 < s) (e : ActualCM c)
    (U : Set (FullWeightedHilbert c s)) :
    ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s
        (U ∩ TM c s hs (fun _ => e) ⁻¹' N) = 0 :=
  translation_null_preserving c s hs e U

/-- R9c's `hTk` for `T = TM (projField k (const e))`, for every `k`, on any `U`. -/
theorem hTk_TM_const (hs : (1 : ℝ) / 2 < s) (e : ActualCM c)
    (U : Set (FullWeightedHilbert c s)) :
    ∀ k : ℕ, ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s
        (U ∩ TM c s hs (projField k (fun _ => e)) ⁻¹' N) = 0 :=
  fun k => translation_null_preserving c s hs (headProj c k e) U

/-- `hTk` in the "eventually in `k`" shape (R9c'). -/
theorem hTk_TM_const_eventually (hs : (1 : ℝ) / 2 < s) (e : ActualCM c)
    (U : Set (FullWeightedHilbert c s)) :
    ∀ᶠ k : ℕ in atTop, ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s
        (U ∩ TM c s hs (projField k (fun _ => e)) ⁻¹' N) = 0 :=
  Filter.Eventually.of_forall (hTk_TM_const c s hs e U)

/-- **Goal 4, Ramer's (*) for the translation `τ_{ie}`** (Ramer §3 translation Jacobi formula). -/
theorem lintegral_image_add_inclE (hs : (1 : ℝ) / 2 < s) (e : ActualCM c)
    (F : FullWeightedHilbert c s → ℝ≥0∞) (hF : Measurable F)
    (V : Set (FullWeightedHilbert c s)) (hV : MeasurableSet V) :
    ∫⁻ y in (fun x => x + inclE c s hs e) '' V, F y
        ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) =
      ∫⁻ x in V, F (x + inclE c s hs e) * ENNReal.ofReal (ramerJac c s hs (fun _ => e) x)
        ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  set μ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hμ
  have hτ : Measurable (fun x : FullWeightedHilbert c s => x - inclE c s hs e) :=
    measurable_id.sub_const _
  have himg : (fun x => x + inclE c s hs e) '' V =
      (fun x : FullWeightedHilbert c s => x - inclE c s hs e) ⁻¹' V := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hy; exact ⟨_, hy, sub_add_cancel _ _⟩
  have hg : Measurable (V.indicator (fun x : FullWeightedHilbert c s =>
      F (x + inclE c s hs e))) :=
    (hF.comp (measurable_id.add_const _)).indicator hV
  rw [himg, ← lintegral_indicator (hτ hV), ← lintegral_indicator hV]
  have h1 : ∀ y : FullWeightedHilbert c s,
      ((fun x : FullWeightedHilbert c s => x - inclE c s hs e) ⁻¹' V).indicator F y =
        (V.indicator (fun x : FullWeightedHilbert c s => F (x + inclE c s hs e)))
          (y - inclE c s hs e) := by
    intro y
    by_cases hy : y - inclE c s hs e ∈ V
    · rw [Set.indicator_of_mem (show y ∈ _ from hy), Set.indicator_of_mem hy, sub_add_cancel]
    · rw [Set.indicator_of_notMem (show y ∉ _ from hy), Set.indicator_of_notMem hy]
  simp_rw [h1]
  rw [← lintegral_map hg hτ, map_sub_inclE_eq_withDensity c s hs e,
    lintegral_withDensity_eq_lintegral_mul₀ (aemeasurable_constDensity c s hs e) hg.aemeasurable]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ V
  · simp [Set.indicator_of_mem hx, mul_comm]
  · simp [Set.indicator_of_notMem hx]

/-- Goal 1 transported to `E_s`. -/
theorem ramerDiv_const_coordE_ae_eq (hs : (1 : ℝ) / 2 < s) (e : ActualCM c)
    (S : Lp ℝ 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val))
    (hS : Tendsto (fun N : ℕ => NlsGge.Measure.actualSourceCMFiniteScorePartialLp c e N)
      atTop (𝓝 S)) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s),
      ramerDiv c s hs (fun _ => e) (coordE c s x) = S (coordE c s x) :=
  ae_of_ae_coordE c s hs (ramerDiv_const_ae_eq c s hs e S hS)

/-- R9c's translation corollary with `hT`, `hTk` discharged, on any open `U`. -/
theorem ramer_translation_unconditional (hs : (1 : ℝ) / 2 < s)
    (U : Set (FullWeightedHilbert c s)) (hU : IsOpen U) (e : ActualCM c)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), x ∈ U →
      ramerJac c s hs ((fun _ => e) + G ∘ fun y => y + inclE c s hs e) x =
        ramerJac c s hs G (x + inclE c s hs e) *
          Real.exp (-(ramerDiv c s hs (fun _ => e) (coordE c s x)) - ‖e‖ ^ 2 / 2) :=
  ramer_translation hs U hU e G hG (translation_null_preserving c s hs e U)
    (fun k => translation_null_preserving c s hs (headProj c k e) U)

end CME

end NlsGge.Ramer
