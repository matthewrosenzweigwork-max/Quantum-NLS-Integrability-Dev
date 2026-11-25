import NlsGge.Measure.CountableGaussian
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace NlsGge.Measure

/-- The actual project alias for the full countable source law, restricted to
any finite set of signed integer coordinates. -/
theorem countableComplexGaussian_map_finiteRestriction
    (q : ℤ → ℝ) (U : Finset ℤ) :
    (NlsGge.Measure.countableComplexGaussian q).map U.restrict =
      Measure.pi (fun u : U =>
        NlsGge.Measure.complexGaussian (q u.1)) := by
  unfold NlsGge.Measure.countableComplexGaussian
  exact Measure.infinitePi_map_restrict
    (fun n : ℤ => NlsGge.Measure.complexGaussian (q n))

/-- Coordinatewise translation of the actual countable source law, observed on
any finite signed-coordinate set, is the product of the translated marginals. -/
theorem countableComplexGaussian_map_add_finiteRestriction
    (q : ℤ → ℝ) (h : ℤ → ℂ) (U : Finset ℤ) :
    (NlsGge.Measure.countableComplexGaussian q).map
        (fun z : ℤ → ℂ => fun u : U => z u.1 + h u.1) =
      Measure.pi (fun u : U =>
        (NlsGge.Measure.complexGaussian (q u.1)).map
          (fun z : ℂ => z + h u.1)) := by
  let shift : (ℤ → ℂ) → (ℤ → ℂ) := fun z n => z n + h n
  have hcomp :
      (fun z : ℤ → ℂ => fun u : U => z u.1 + h u.1) = U.restrict ∘ shift := by
    funext z u
    rfl
  have hglobal :
      (NlsGge.Measure.countableComplexGaussian q).map shift =
        Measure.infinitePi (fun n : ℤ =>
          (NlsGge.Measure.complexGaussian (q n)).map
            (fun z : ℂ => z + h n)) := by
    unfold NlsGge.Measure.countableComplexGaussian
    exact Measure.infinitePi_map_pi
      (μ := fun n : ℤ => NlsGge.Measure.complexGaussian (q n))
      (f := fun n z => z + h n)
      (fun n => by fun_prop)
  calc
    (NlsGge.Measure.countableComplexGaussian q).map
        (fun z : ℤ → ℂ => fun u : U => z u.1 + h u.1) =
        ((NlsGge.Measure.countableComplexGaussian q).map shift).map U.restrict := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rw [hcomp]
    _ = (Measure.infinitePi (fun n : ℤ =>
          (NlsGge.Measure.complexGaussian (q n)).map
            (fun z : ℂ => z + h n))).map U.restrict := by rw [hglobal]
    _ = Measure.pi (fun u : U =>
          (NlsGge.Measure.complexGaussian (q u.1)).map
            (fun z : ℂ => z + h u.1)) := by
          exact Measure.infinitePi_map_restrict
            (fun n : ℤ =>
              (NlsGge.Measure.complexGaussian (q n)).map
                (fun z : ℂ => z + h n))

end NlsGge.Measure
