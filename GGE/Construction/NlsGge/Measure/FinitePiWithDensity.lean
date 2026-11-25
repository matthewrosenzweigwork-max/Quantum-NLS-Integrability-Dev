import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import NlsGge.Measure.FinitePiLIntegralProduct

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NlsGge.Measure

/-- A finite product of coordinatewise densities is the density of the finite
product measure, for a homogeneous factor space. -/
theorem measure_pi_withDensity_homogeneous
    {n : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Fin n → Measure α) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → α → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (hfinite : ∀ i x, f i x ≠ ∞) :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  haveI : ∀ i, SigmaFinite ((μ i).withDensity (f i)) := fun i =>
    SigmaFinite.withDensity_of_ne_top' (hfinite i)
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ x, (∏ i, f i (x i)) ∂(Measure.pi μ).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  rw [lintegral_fin_nat_prod_eq_prod
    (μ := fun i => (μ i).restrict (s i)) (f := f) hf]
  simp_rw [withDensity_apply _ (hs _)]

end NlsGge.Measure
