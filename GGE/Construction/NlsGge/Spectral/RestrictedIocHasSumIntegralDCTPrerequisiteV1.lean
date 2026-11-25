import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open MeasureTheory

namespace NlsGge.SpectralFoundations

/-- The exact pinned dominated-convergence interchange on the restricted
measure for the source interval `(0,t]`. The hypotheses are stated on that
actual restricted measure, so no conversion from `uIoc` is hidden. -/
theorem hasSum_integral_restrict_Ioc_of_dominated_convergence
    (t : ℝ) (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ)
    (bound : ℕ → ℝ → ℝ)
    (hFmeas : ∀ n : ℕ,
      MeasureTheory.AEStronglyMeasurable (F n)
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)))
    (hFbound : ∀ n : ℕ, ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)),
      ‖F n s‖ ≤ bound n s)
    (hboundSummable : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)),
      Summable fun n : ℕ => bound n s)
    (hboundIntegrable : MeasureTheory.Integrable
      (fun s : ℝ => ∑' n : ℕ, bound n s)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)))
    (hpointwise : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)),
      HasSum (fun n : ℕ => F n s) (f s)) :
    HasSum
      (fun n : ℕ => ∫ s, F n s ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)))
      (∫ s, f s ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t))) := by
  exact MeasureTheory.hasSum_integral_of_dominated_convergence
    bound hFmeas hFbound hboundSummable hboundIntegrable hpointwise

end NlsGge.SpectralFoundations
