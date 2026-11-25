import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# LIB-061: exponential conditional Jensen on the actual probability space

Both the real variable and its exponential are assumed integrable before
conditional Jensen is applied. The actual sub-sigma-algebra inclusion and
probability instance supply a finite trimmed measure, so no additional
sigma-finiteness, boundedness, or measurability hypothesis is imposed.
-/

set_option autoImplicit false

namespace NlsGge.Atomic.LIB061
open MeasureTheory

/-- Exponential conditional Jensen for every sub-sigma-algebra of a probability space. -/
theorem exp_condExp_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A : MeasurableSpace Ω} {X : Ω → ℝ}
    (hX : Integrable X μ) (heX : Integrable (fun ω => Real.exp (X ω)) μ)
    (hA : A ≤ mΩ) :
    (fun ω => Real.exp (μ[X | A] ω)) ≤ᵐ[μ]
      μ[(fun ω => Real.exp (X ω)) | A] := by
  have h := ConvexOn.map_condExp_le_univ hA convexOn_exp
    Real.continuous_exp.lowerSemicontinuous hX heX
  simpa only [Function.comp_def] using h

end NlsGge.Atomic.LIB061
