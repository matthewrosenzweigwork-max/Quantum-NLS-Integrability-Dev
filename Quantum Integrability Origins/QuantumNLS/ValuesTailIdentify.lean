import Mathlib
import QuantumNLS.R275Unconditional
import QuantumNLS.BulkResponseDefinition

/-!
# R-CB4CC6EE (`values:lem:tail`), B4: identification `μ_{κ,φ} = M_{κ,φ}` and moments

For a unit smooth periodic profile `φ` (`‖smoothL2 hf‖ = 1`) and any probability measure `μ` with
`IsLimitingRapidityMeasure L κ hκ (smoothL2 hf) hu μ`:

* `limit_eq_Mmeas`: `(μ : Measure ℝ) = Mmeas κ (smoothL2 hf)` (uniqueness of the limit, `fullMass_eq`,
  `measure_eq_Mmeas`);
* `integrable_moment_of_limit`: `Integrable (fun t => |t|^r) μ` for every `r : ℕ` (from `R_275B7656`).

No new analysis. Frozen support step for B4 of R-CB4CC6EE. Nothing here is accepted.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace QuantumNLS.ValuesTailIdentify

open QuantumNLS.ClassicalCharges QuantumNLS.CauchyUniqueness QuantumNLS.FullMass
open QuantumNLS.SmoothScalarMomentsAsymptotic QuantumNLS.SmoothScalarMomentsCauchy
open QuantumNLS.SmoothScalarMomentsPhysical

variable {L : ℝ} [Fact (0 < L)] {f : ℝ → ℂ}

/-- `μ_{κ,φ} = M_{κ,φ}` for a unit profile `φ = smoothL2 hf`. -/
theorem limit_eq_Mmeas {κ : ℝ} (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : QuantumNLS.BulkResponseActual.IsLimitingRapidityMeasure L κ hκ (smoothL2 hf) hu μ) :
    (μ : Measure ℝ) = Mmeas κ (smoothL2 hf) := by
  have h1 := QuantumNLS.BulkResponseActual.IsLimitingRapidityMeasure.unique hμ
    (QuantumNLS.BulkResponseDefinition.limiting (κ := κ) hκ (smoothL2 hf) hu)
  rw [h1, ← QuantumNLS.BulkResponseDefinition.fullMass_eq (κ := κ) hκ (smoothL2 hf) hu,
    QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas hκ (smoothL2 hf)]

/-- Finite moments of every order for the limiting measure of a unit smooth profile. -/
theorem integrable_moment_of_limit {κ : ℝ} (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : QuantumNLS.BulkResponseActual.IsLimitingRapidityMeasure L κ hκ (smoothL2 hf) hu μ) (r : ℕ) :
    Integrable (fun t : ℝ => |t| ^ r) (μ : Measure ℝ) := by
  rw [limit_eq_Mmeas hκ hf hu hμ]
  exact ((QuantumNLS.R275Unconditional.R_275B7656 κ hκ hf).2 r).1

end QuantumNLS.ValuesTailIdentify

#print axioms QuantumNLS.ValuesTailIdentify.limit_eq_Mmeas
#print axioms QuantumNLS.ValuesTailIdentify.integrable_moment_of_limit
