import NlsGge.Measure.ActualSourceCMFiniteScorePointwiseLikelihoodV3
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Measure

/-- The actual translated raw Gaussian law has the explicit exponential CM
score density. The density is AE-measurable and ENNReal-normalized; its law
identity is inherited from the verified countable-coordinate RN theorem and
rewritten using the pointwise likelihood formula. -/
theorem exists_actualSourceCM_expScoreRNdensity_v2
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)) :
    ∃ S : MeasureTheory.Lp ℝ 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun N : ℕ =>
        NlsGge.Measure.actualSourceCMFiniteScorePartialLp c x N)
        atTop (nhds S) ∧
      AEMeasurable
        (fun z : ℤ → ℂ => ENNReal.ofReal (Real.exp (S z -
          (∑' n : ℤ, NlsGge.Pilot.cmModeWeight c n *
            ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2) / 2)))
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
      (∫⁻ z : ℤ → ℂ, ENNReal.ofReal (Real.exp (S z -
        (∑' n : ℤ, NlsGge.Pilot.cmModeWeight c n *
          ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2) / 2))
        ∂NlsGge.Measure.fullWeightSequenceGaussian c.val) = 1 ∧
      (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
        (fun z : ℤ → ℂ => fun n => z n + NlsGge.Measure.actualSourceCMSequence c x n) =
      (NlsGge.Measure.fullWeightSequenceGaussian c.val).withDensity
        (fun z => ENNReal.ofReal (Real.exp (S z -
          (∑' n : ℤ, NlsGge.Pilot.cmModeWeight c n *
            ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2) / 2))) := by
  obtain ⟨S, L, hS, hL, hpointwise, hRN⟩ :=
    NlsGge.Measure.exists_actualSourceCMFiniteScore_pointwiseLikelihood_v3 c x
  let μ : Measure (ℤ → ℂ) := NlsGge.Measure.fullWeightSequenceGaussian c.val
  let Q : ℝ := ∑' n : ℤ, NlsGge.Pilot.cmModeWeight c n *
    ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2
  let density : (ℤ → ℂ) → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (S z - Q / 2))
  have hpointwiseENN : (fun z : ℤ → ℂ => ENNReal.ofReal (L z)) =ᵐ[μ] density := by
    filter_upwards [hpointwise] with z hz
    exact congrArg ENNReal.ofReal hz
  have hshift :
      μ.map (fun z : ℤ → ℂ => fun n => z n +
        NlsGge.Measure.actualSourceCMSequence c x n) = μ.withDensity density := by
    calc
      μ.map (fun z : ℤ → ℂ => fun n => z n +
          NlsGge.Measure.actualSourceCMSequence c x n) =
          μ.withDensity (fun z => ENNReal.ofReal (L z)) := by
            simpa [μ] using hRN
      _ = μ.withDensity density := MeasureTheory.withDensity_congr_ae hpointwiseENN
  have hSae : AEMeasurable (fun z : ℤ → ℂ => S z) μ :=
    (MeasureTheory.Lp.aestronglyMeasurable S).aemeasurable
  have hdensity : AEMeasurable density μ := by
    dsimp [density, Q]
    exact (hSae.sub_const _).exp.ennreal_ofReal
  have hmass : (μ.withDensity density) Set.univ = 1 := by
    rw [← hshift]
    have hmap : Measurable (fun z : ℤ → ℂ => fun n => z n +
        NlsGge.Measure.actualSourceCMSequence c x n) := by
      fun_prop
    rw [Measure.map_apply hmap MeasurableSet.univ]
    simp [μ]
  have hlintegral : (∫⁻ z : ℤ → ℂ, density z ∂μ) = 1 := by
    simpa [MeasureTheory.withDensity_apply, Measure.restrict_univ] using hmass
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · simpa [μ, density, Q] using hdensity
  · simpa [μ, density, Q] using hlintegral
  · simpa [μ, density, Q] using hshift

end NlsGge.Measure
