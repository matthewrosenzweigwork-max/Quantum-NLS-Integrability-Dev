import Mathlib
import NlsGge.Atomic.R.R150
import NlsGge.Atomic.R.R151
import NlsGge.Measure.PhysicalWeightedLaw
import NlsGge.Measure.CountableGaussian
import NlsGge.Birkhoff.W05FiniteGap38

/-!
# R-108: the realized full weighted Gaussian carrier, with moments

Source head: Pro round 6 (commit c5547100), section 10G, R-108
`fullWeightedSequenceGaussian_fullSupport_Radon` (binding index entry R-108).

Carrier: `fullWeightedSequenceGaussian c s` is the pushforward of the product law
`fullWeightSequenceGaussian c.val` under the realization `fullWeightedSequenceRealization c s`.
Each conjunct is discharged by an existing checked fact on this same carrier:
* probability and Radon (inner regularity): `R-151` (`fullWeightedGaussian_isRadon`);
* positive mass of every norm ball: `R-150` (`fullWeightedGaussian_ball_pos`);
* integrability and the scalar moment of `‖x‖²`:
  `NlsGge.Measure.integrable_fullWeightedSequenceGaussian_sqNorm` and
  `NlsGge.Measure.integral_fullWeightedSequenceGaussian_sqNorm`
  (`NlsGge/Measure/PhysicalWeightedLaw.lean`);
* per-coordinate moments: the a.e. coordinate identity of the realization
  (`ae_fullWeightedSequenceRealization_apply`), the change of variables through the
  pushforward, and `integral_fullWeightSequenceGaussian_sqNorm` for the product law.
The coordinate `x ↦ eCoe38 c s x n` is continuous (`Birkhoff.continuous_eCoe_apply38`).
No new hypothesis is added; the norm moment summand is `a_n⟨n⟩^{-2s}·(1/a_n)`.
-/

open MeasureTheory
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Measure NlsGge.Weights

namespace NlsGge.ThirdConsultation.R

theorem fullWeightedSequenceGaussian_fullSupport_Radon
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    IsProbabilityMeasure (fullWeightedSequenceGaussian c s) ∧
    IsFiniteMeasure (fullWeightedSequenceGaussian c s) ∧
    (∀ (y : FullWeightedHilbert c s) (ε : ℝ), 0 < ε →
      0 < fullWeightedSequenceGaussian c s (Metric.ball y ε)) ∧
    MeasureTheory.Measure.InnerRegular (fullWeightedSequenceGaussian c s) ∧
    Integrable (fun x : FullWeightedHilbert c s => ‖x‖ ^ 2)
      (fullWeightedSequenceGaussian c s) ∧
    (∫ x : FullWeightedHilbert c s, ‖x‖ ^ 2
      ∂fullWeightedSequenceGaussian c s) =
        ∑' n : ℤ, Real.rpow (japaneseBracket n) (-2 * s) ∧
    (∀ n : ℤ,
      Integrable (fun x : FullWeightedHilbert c s =>
        ‖eCoe38 c s x n‖ ^ 2) (fullWeightedSequenceGaussian c s) ∧
      (∫ x : FullWeightedHilbert c s, ‖eCoe38 c s x n‖ ^ 2
        ∂fullWeightedSequenceGaussian c s) =
          (fullWeightRate c.val n)⁻¹) := by
  have hRad := fullWeightedGaussian_isRadon lower upper c s hs
  have hlower : 0 < lower := c.property.1
  have hbound : ∀ j : ℕ, lower ≤ c.val j := fun j => (c.property.2.2 j).1
  have hupper : ∀ j : ℕ, c.val j ≤ upper := fun j => (c.property.2.2 j).2
  have hmoment : ∀ n : ℤ,
      Integrable (fun x : FullWeightedHilbert c s => ‖eCoe38 c s x n‖ ^ 2)
        (fullWeightedSequenceGaussian c s) ∧
      (∫ x : FullWeightedHilbert c s, ‖eCoe38 c s x n‖ ^ 2
        ∂fullWeightedSequenceGaussian c s) = (fullWeightRate c.val n)⁻¹ := by
    intro n
    have hcont : Continuous (fun x : FullWeightedHilbert c s => ‖eCoe38 c s x n‖ ^ 2) :=
      (continuous_eCoe_apply38 c s n).norm.pow 2
    have hg : Measurable (fun x : FullWeightedHilbert c s => ‖eCoe38 c s x n‖ ^ 2) :=
      hcont.measurable
    have hae : (fun z : ℤ → ℂ => ‖eCoe38 c s (fullWeightedSequenceRealization c s z) n‖ ^ 2)
        =ᵐ[fullWeightSequenceGaussian c.val] (fun z : ℤ → ℂ => ‖z n‖ ^ 2) := by
      filter_upwards [ae_fullWeightedSequenceRealization_apply c s hs] with z hz
      exact congrArg (fun t : ℂ => ‖t‖ ^ 2) (hz n)
    have hR : AEMeasurable (fullWeightedSequenceRealization c s) (fullWeightSequenceGaussian c.val) :=
      (measurable_fullWeightedSequenceRealization c s).aemeasurable
    constructor
    · unfold fullWeightedSequenceGaussian
      rw [integrable_map_measure hg.aestronglyMeasurable hR]
      exact (integrable_fullWeightSequenceGaussian_sqNorm c.val n).congr hae.symm
    · unfold fullWeightedSequenceGaussian
      rw [integral_map hR hg.aestronglyMeasurable, integral_congr_ae hae,
        integral_fullWeightSequenceGaussian_sqNorm lower upper c.val hlower hbound hupper n,
        one_div]
  exact ⟨hRad.1, inferInstance,
    fun y ε hε => fullWeightedGaussian_ball_pos lower upper c s hs y ε hε,
    hRad.2,
    integrable_fullWeightedSequenceGaussian_sqNorm c s hs,
    integral_fullWeightedSequenceGaussian_sqNorm c s hs,
    hmoment⟩

end NlsGge.ThirdConsultation.R
