import NlsGge.Measure.FourierGaussian
import NlsGge.Measure.ComplexGaussianShiftDensity
import NlsGge.Measure.FinitePiWithDensity
import NlsGge.Measure.ENNRealExpProductNormalization

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NlsGge.Measure

/-- The actual full-rate finite Fourier Gaussian, translated by an arbitrary
complex vector on every signed mode, has its source-normalized output density. -/
theorem fullWeightFourierGaussian_map_add_withDensity_afterNormalization
    (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j, lower ≤ c j)
    (hupper : ∀ j, c j ≤ upper) (N : ℕ)
    (h : NlsGge.Pilot.FourierPlane N) :
    (fullWeightFourierGaussian N c).map (fun z i => z i + h i) =
      (fullWeightFourierGaussian N c).withDensity
        (fun z => ENNReal.ofReal (Real.exp (∑ i : Fin (2 * N + 1),
          (2 * fullWeightRate c (NlsGge.Pilot.modeIndex N i) *
              (star (h i) * z i).re -
          fullWeightRate c (NlsGge.Pilot.modeIndex N i) * ‖h i‖ ^ 2)))) := by
  let q : Fin (2 * N + 1) → ℝ := fun i => fullWeightRate c (NlsGge.Pilot.modeIndex N i)
  let ell : Fin (2 * N + 1) → ℂ → ℝ := fun i z =>
    2 * q i * (star (h i) * z).re - q i * ‖h i‖ ^ 2
  let F : (Fin (2 * N + 1) → ℂ) → Fin (2 * N + 1) → ℝ := fun z i =>
    ell i (z i)
  let density : Fin (2 * N + 1) → ℂ → ℝ≥0∞ := fun i z =>
    ENNReal.ofReal (Real.exp (ell i z))
  have hq (i : Fin (2 * N + 1)) : 0 < q i := by
    dsimp [q]
    exact fullWeightRate_pos lower upper c hlower hbound hupper _
  have hdensity_measurable (i : Fin (2 * N + 1)) : Measurable (density i) := by
    dsimp [density, ell]
    fun_prop
  have hdensity_finite (i : Fin (2 * N + 1)) (z : ℂ) : density i z ≠ ∞ := by
    dsimp [density]
    exact ENNReal.ofReal_ne_top
  have hcoordinate (i : Fin (2 * N + 1)) :
      (complexGaussian (q i)).map (fun z : ℂ => z + h i) =
        (complexGaussian (q i)).withDensity (density i) := by
    simpa [density, ell, q] using complexGaussian_map_add_const_withDensity
      (q i) (h i) (hq i)
  have hmap :
      (Measure.pi (fun i : Fin (2 * N + 1) => complexGaussian (q i))).map
          (fun z i => z i + h i) =
        Measure.pi (fun i => (complexGaussian (q i)).map (fun z : ℂ => z + h i)) := by
    exact Measure.pi_map_pi (μ := fun i : Fin (2 * N + 1) => complexGaussian (q i))
      (f := fun i z => z + h i) (fun i => (by fun_prop : Measurable (fun z : ℂ => z + h i)).aemeasurable)
  have hproduct_density : ∀ z : Fin (2 * N + 1) → ℂ,
      (∏ i : Fin (2 * N + 1), density i (z i)) =
        ENNReal.ofReal (Real.exp (∑ i : Fin (2 * N + 1), F z i)) := by
    intro z
    change (∏ i : Fin (2 * N + 1), ENNReal.ofReal (Real.exp (ell i (z i)))) =
      ENNReal.ofReal (Real.exp (∑ i : Fin (2 * N + 1), ell i (z i)))
    exact ennreal_ofReal_exp_prod_eq_exp_sum (fun i => ell i (z i))
  change (Measure.pi (fun i : Fin (2 * N + 1) => complexGaussian (q i))).map
      (fun z i => z i + h i) =
    (Measure.pi (fun i : Fin (2 * N + 1) => complexGaussian (q i))).withDensity
      (fun z => ENNReal.ofReal (Real.exp (∑ i : Fin (2 * N + 1), F z i)))
  calc
    (Measure.pi (fun i : Fin (2 * N + 1) => complexGaussian (q i))).map
        (fun z i => z i + h i) =
      Measure.pi (fun i => (complexGaussian (q i)).map (fun z : ℂ => z + h i)) := hmap
    _ = Measure.pi (fun i => (complexGaussian (q i)).withDensity (density i)) := by
      congr 1
      funext i
      exact hcoordinate i
    _ = (Measure.pi (fun i : Fin (2 * N + 1) => complexGaussian (q i))).withDensity
        (fun z => ∏ i, density i (z i)) :=
      measure_pi_withDensity_homogeneous
        (fun i : Fin (2 * N + 1) => complexGaussian (q i)) density
        hdensity_measurable hdensity_finite
    _ = (Measure.pi (fun i : Fin (2 * N + 1) => complexGaussian (q i))).withDensity
        (fun z => ENNReal.ofReal (Real.exp (∑ i : Fin (2 * N + 1), F z i))) := by
      congr 1
      funext z
      exact hproduct_density z

end NlsGge.Measure
