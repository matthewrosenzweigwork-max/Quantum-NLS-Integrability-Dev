import NlsGge.Measure.CountableGaussian
import NlsGge.Sobolev.SourceWeighted
import NlsGge.Measure.ComplexGaussian
import NlsGge.Measure.WeightedGaussianFiniteRestrictionPrerequisiteV2
import NlsGge.Measure.ENNRealFiniteProductStrictPosPrerequisiteV2
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option pp.maxSteps 10000000
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Measure.WeightedGaussianFiniteHeadBoxPositivityAfterRestrictionV5

/-- Every nonempty open disk has positive measure under the actual proper
complex Gaussian factor, by its pinned strictly positive density. -/
lemma complexGaussian_ball_pos (a : ℝ) (ha : 0 < a) (z : ℂ) (r : ℝ) (hr : 0 < r) :
    0 < NlsGge.Measure.complexGaussian a (Metric.ball z r) := by
  let ρ : ℂ → ℝ≥0∞ := fun y => ENNReal.ofReal
    ((a / Real.pi) * Real.exp (-a * ‖y‖ ^ 2))
  have hρ (y : ℂ) : 0 < ρ y := by
    dsimp [ρ]
    apply ENNReal.ofReal_pos.mpr
    positivity
  rw [NlsGge.Measure.complexGaussian_density a ha,
    MeasureTheory.withDensity_apply ρ Metric.isOpen_ball.measurableSet]
  rw [MeasureTheory.setLIntegral_pos_iff (by fun_prop)]
  have hball : 0 < (volume : MeasureTheory.Measure ℂ) (Metric.ball z r) :=
    Metric.isOpen_ball.measure_pos volume ⟨z, Metric.mem_ball_self hr⟩
  apply hball.trans_le
  apply MeasureTheory.measure_mono
  intro y hy
  constructor
  · change ρ y ≠ 0
    exact (hρ y).ne'
  · exact hy

/-- A finite box around any prescribed raw coordinate vector has positive
probability under the actual pinned full source-rate Gaussian law. -/
lemma positive_raw_finite_head_box
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (S : Finset ℤ) (x : ℤ → ℂ) (r : ℝ) (hr : 0 < r) :
    0 < NlsGge.Measure.fullWeightSequenceGaussian c.val
      {z : ℤ → ℂ | ∀ i : S, ‖z i.1 - x i.1‖ < r} := by
  classical
  let B : Set ((i : S) → ℂ) :=
    Set.pi Set.univ (fun i => Metric.ball (x i.1) r)
  have hB : MeasurableSet B := by
    dsimp [B]
    exact MeasurableSet.pi Set.countable_univ (fun i _ => Metric.isOpen_ball.measurableSet)
  have hEvent :
      {z : ℤ → ℂ | ∀ i : S, ‖z i.1 - x i.1‖ < r} =
        (Set.domRestrict (S : Set ℤ) : (ℤ → ℂ) → ((i : S) → ℂ)) ⁻¹' B := by
    ext z
    simp [B, Set.mem_pi, dist_eq_norm]
  rw [hEvent]
  rw [← MeasureTheory.Measure.map_apply
    (Set.measurable_restrict (S : Set ℤ)) hB]
  rw [NlsGge.Measure.WeightedGaussianFiniteRestrictionPrerequisiteV2.fullWeightSequenceGaussian_map_domRestrict]
  rw [MeasureTheory.Measure.pi_pi]
  exact NlsGge.Measure.ENNRealFiniteProductStrictPosPrerequisiteV2.finset_prod_pos
    Finset.univ (fun i : S => NlsGge.Measure.complexGaussian
      (NlsGge.Measure.fullWeightRate c.val i.1) (Metric.ball (x i.1) r))
    (fun i _ => complexGaussian_ball_pos (NlsGge.Measure.fullWeightRate c.val i.1)
      (NlsGge.Pilot.sourceRate_pos c i.1) (x i.1) r hr)

#check @complexGaussian_ball_pos
#check @positive_raw_finite_head_box

end NlsGge.Measure.WeightedGaussianFiniteHeadBoxPositivityAfterRestrictionV5
