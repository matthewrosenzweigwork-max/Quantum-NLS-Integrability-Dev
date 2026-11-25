import Mathlib
import NlsGge.Atomic.R.R023
import NlsGge.Ramer.ConstantShiftInverseOrientation
import NlsGge.Measure.ActualSourceCMFiniteScoreCovariancePrerequisiteV2
import NlsGge.Measure.FiniteScalarMoments
import NlsGge.Measure.RealLp2RepresentativeCalculus

                                                                                    
                                                                
                                                                                                                          
                                                                                                    
                                                                                                                                
                                                                                                                           
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The constant function `1` as an element of `L²(μ)`. -/
private def oneL2 (μ : Measure Ω) [IsProbabilityMeasure μ] : Lp ℝ 2 μ :=
  (memLp_const (μ := μ) (p := 2) (1 : ℝ)).toLp (fun _ => (1 : ℝ))

private lemma integral_eq_inner_one (g : Lp ℝ 2 μ) :
    ∫ a, g a ∂μ = inner ℝ (oneL2 μ) g := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_const (μ := μ) (p := 2) (1 : ℝ)).coeFn_toLp] with a ha
  unfold oneL2
  rw [ha]
  simp

private lemma integral_sq_eq_inner (g : Lp ℝ 2 μ) :
    ∫ a, (g a) ^ 2 ∂μ = inner ℝ g g := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp [RCLike.inner_apply, sq]

private lemma tendsto_inner_pair {α : Type*} {l : Filter α} {f g : α → Lp ℝ 2 μ}
    {a b : Lp ℝ 2 μ} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun t => inner ℝ (f t) (g t)) l (𝓝 (inner ℝ a b)) :=
  (continuous_inner.tendsto (a, b)).comp (hf.prodMk_nhds hg)

end Helpers

private lemma partial_integral_zero {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)) (N : ℕ) :
    ∫ z : ℤ → ℂ, NlsGge.Measure.actualSourceCMFiniteScorePartial c x N z
      ∂NlsGge.Measure.fullWeightSequenceGaussian c.val = 0 :=
  NlsGge.Measure.integral_fullWeightSequenceGaussian_partialScalar c 0 N
    (NlsGge.Measure.actualSourceCMFiniteScoreFunctional c x)

private lemma partial_memLp {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)) (N : ℕ) :
    MemLp (fun z : ℤ → ℂ => NlsGge.Measure.actualSourceCMFiniteScorePartial c x N z) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
  (NlsGge.Measure.hasGaussianLaw_fullWeightSequenceGaussian_partialScalar c 0 N
    (NlsGge.Measure.actualSourceCMFiniteScoreFunctional c x)).memLp_two

private lemma partial_sq_integral {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)) (N : ℕ) :
    ∫ z : ℤ → ℂ, (NlsGge.Measure.actualSourceCMFiniteScorePartial c x N z) ^ 2
      ∂NlsGge.Measure.fullWeightSequenceGaussian c.val =
      ∑ n ∈ NlsGge.Pilot.symmetricModes N,
        NlsGge.Pilot.cmModeWeight c n * ‖NlsGge.Ramer.cmCoord x n‖ ^ 2 := by
  have hv := ProbabilityTheory.variance_of_integral_eq_zero (partial_memLp c x N).aemeasurable
    (partial_integral_zero c x N)
  have hv2 := NlsGge.Measure.variance_fullWeightSequenceGaussian_partialScalar c 0 N
    (NlsGge.Measure.actualSourceCMFiniteScoreFunctional c x)
  calc ∫ z : ℤ → ℂ, (NlsGge.Measure.actualSourceCMFiniteScorePartial c x N z) ^ 2
        ∂NlsGge.Measure.fullWeightSequenceGaussian c.val
      = ProbabilityTheory.variance
          (fun z : ℤ → ℂ => NlsGge.Measure.actualSourceCMFiniteScorePartial c x N z)
          (NlsGge.Measure.fullWeightSequenceGaussian c.val) := hv.symm
    _ = ∑ n ∈ NlsGge.Pilot.symmetricModes N,
          NlsGge.Measure.fullWeightedDualCovarianceTerm c 0
            (NlsGge.Measure.actualSourceCMFiniteScoreFunctional c x)
            (NlsGge.Measure.actualSourceCMFiniteScoreFunctional c x) n := hv2
    _ = ∑ n ∈ NlsGge.Pilot.symmetricModes N,
          NlsGge.Pilot.cmModeWeight c n * ‖NlsGge.Ramer.cmCoord x n‖ ^ 2 :=
      Finset.sum_congr rfl fun n _ =>
        NlsGge.Measure.actualSourceCMFiniteScoreFunctional_covarianceTerm_v1 c x n

private lemma partialLp_coe_ae {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)) (N : ℕ) :
    (NlsGge.Measure.actualSourceCMFiniteScorePartialLp c x N : (ℤ → ℂ) → ℝ) =ᵐ[
        NlsGge.Measure.fullWeightSequenceGaussian c.val]
      fun z : ℤ → ℂ => NlsGge.Measure.actualSourceCMFiniteScorePartial c x N z := by
  unfold NlsGge.Measure.actualSourceCMFiniteScorePartialLp
  exact MemLp.coeFn_toLp _

/-- **R-012 (inverse translation density, existential positive score).** -/
theorem inverse_translation_density
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (h : RamerH c) :
    ∃ Sc : Lp ℝ 2 (coordinateGaussian c),
      Tendsto
        (fun N : ℕ =>
          NlsGge.Measure.actualSourceCMFiniteScorePartialLp c h N)
        atTop (𝓝 Sc) ∧
      MemLp (fun x : RamerE c s => Sc (NlsGge.Ramer.coordE c s x))
        2 (ramerGaussian c s) ∧
      (∫ x : RamerE c s, Sc (NlsGge.Ramer.coordE c s x)
        ∂ramerGaussian c s) = 0 ∧
      ProbabilityTheory.variance
        (fun x : RamerE c s => Sc (NlsGge.Ramer.coordE c s x))
        (ramerGaussian c s) = ‖h‖ ^ 2 ∧
      Measure.map (fun x : RamerE c s => x - cmEmbedding c s hs h)
          (ramerGaussian c s) =
        (ramerGaussian c s).withDensity
          (fun x => ENNReal.ofReal
            (Real.exp (-Sc (NlsGge.Ramer.coordE c s x) - ‖h‖ ^ 2 / 2))) := by
  obtain ⟨S, hS, -, -, -⟩ :=
    NlsGge.Ramer.exists_actualSourceCM_inverseShift_negativeScoreDensity c h
  have hmp := NlsGge.Ramer.measurePreserving_coordE c s hs
  -- mean zero on the coordinate space
  have hmean : ∫ z, S z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) = 0 := by
    rw [integral_eq_inner_one S]
    have h0 : ∀ N : ℕ, inner ℝ (oneL2 (NlsGge.Measure.fullWeightSequenceGaussian c.val))
        (NlsGge.Measure.actualSourceCMFiniteScorePartialLp c h N) = 0 := by
      intro N
      rw [← integral_eq_inner_one]
      exact (integral_congr_ae (partialLp_coe_ae c h N)).trans
        (partial_integral_zero c h N)
    have hc := tendsto_inner_pair (tendsto_const_nhds (x := oneL2 (NlsGge.Measure.fullWeightSequenceGaussian c.val))) hS
    simp only [h0] at hc
    exact tendsto_nhds_unique hc tendsto_const_nhds
  -- second moment
  have hsq : inner ℝ S S = ‖h‖ ^ 2 := by
    have hc := tendsto_inner_pair hS hS
    have h0 : ∀ N : ℕ,
        inner ℝ (NlsGge.Measure.actualSourceCMFiniteScorePartialLp c h N)
          (NlsGge.Measure.actualSourceCMFiniteScorePartialLp c h N) =
        ∑ n ∈ NlsGge.Pilot.symmetricModes N,
          NlsGge.Pilot.cmModeWeight c n * ‖NlsGge.Ramer.cmCoord h n‖ ^ 2 := by
      intro N
      rw [← integral_sq_eq_inner, ← partial_sq_integral c h N]
      refine integral_congr_ae ?_
      filter_upwards [partialLp_coe_ae c h N] with z hz
      rw [hz]
    simp only [h0] at hc
    have hT : Tendsto (fun N : ℕ =>
        ∑ n ∈ NlsGge.Pilot.symmetricModes N,
          NlsGge.Pilot.cmModeWeight c n * ‖NlsGge.Ramer.cmCoord h n‖ ^ 2)
        atTop (𝓝 (‖h‖ ^ 2)) :=
      ((NlsGge.Pilot.weightedHilbert_hasSum (NlsGge.Pilot.cmModeWeight c)
        (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.cmModeWeight c) from h)).comp
          NlsGge.Pilot.symmetricModes_tendsto)
    exact tendsto_nhds_unique hc hT
  have hvarS : ProbabilityTheory.variance (⇑S)
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) = ‖h‖ ^ 2 := by
    rw [ProbabilityTheory.variance_eq_sub (Lp.memLp S), hmean]
    simp only [Pi.pow_apply]
    rw [integral_sq_eq_inner S, hsq]
    simp
  refine ⟨S, hS, ?_, ?_, ?_, ?_⟩
  · exact (Lp.memLp S).comp_measurePreserving hmp
  · show ∫ x : RamerE c s, S (NlsGge.Ramer.coordE c s x)
        ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) = 0
    have hf : AEStronglyMeasurable (⇑S)
        (Measure.map (NlsGge.Ramer.coordE c s) (NlsGge.Measure.fullWeightedSequenceGaussian c s)) := by
      rw [hmp.map_eq]
      exact Lp.aestronglyMeasurable S
    calc ∫ x : RamerE c s, S (NlsGge.Ramer.coordE c s x)
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s)
        = ∫ z, S z ∂(Measure.map (NlsGge.Ramer.coordE c s)
            (NlsGge.Measure.fullWeightedSequenceGaussian c s)) :=
          (integral_map (NlsGge.Ramer.measurable_coordE c s).aemeasurable hf).symm
      _ = ∫ z, S z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
          rw [hmp.map_eq]
      _ = 0 := hmean
  · show ProbabilityTheory.variance (fun x : RamerE c s => S (NlsGge.Ramer.coordE c s x))
        (NlsGge.Measure.fullWeightedSequenceGaussian c s) = ‖h‖ ^ 2
    have hAE : AEMeasurable (⇑S)
        (Measure.map (NlsGge.Ramer.coordE c s) (NlsGge.Measure.fullWeightedSequenceGaussian c s)) := by
      rw [hmp.map_eq]
      exact (Lp.aestronglyMeasurable S).aemeasurable
    have hvm := ProbabilityTheory.variance_map hAE (NlsGge.Ramer.measurable_coordE c s).aemeasurable
    rw [hmp.map_eq] at hvm
    exact hvm.symm.trans hvarS
  · have hden : ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s),
        ENNReal.ofReal (NlsGge.Ramer.ramerJac c s hs (fun _ => h) x) =
          ENNReal.ofReal (Real.exp (-S (NlsGge.Ramer.coordE c s x) - ‖h‖ ^ 2 / 2)) := by
      filter_upwards [NlsGge.Ramer.ramerDiv_const_coordE_ae_eq c s hs h S hS] with x hx
      rw [NlsGge.Ramer.ramerJac_const hs h x, hx]
    show Measure.map (fun x : RamerE c s => x - NlsGge.Ramer.inclE c s hs h)
        (NlsGge.Measure.fullWeightedSequenceGaussian c s) = _
    rw [NlsGge.Ramer.map_sub_inclE_eq_withDensity c s hs h]
    exact withDensity_congr_ae hden

end
end NlsGge.ThirdConsultation.R
