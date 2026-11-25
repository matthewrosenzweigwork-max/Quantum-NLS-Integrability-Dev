import Mathlib
import QuantumNLS.BulkResponseActual
import QuantumNLS.BulkResponseForm
import QuantumNLS.RootEnergyMoment
import QuantumNLS.RootCoreH1
import QuantumNLS.RootSpectralInputsDischarge
import QuantumNLS.PhysicalUnconditionalTrace
import QuantumNLS.RootMeasureExistence
import QuantumNLS.FreeLimit

/-!
# R-BB7EDFF3 (`CC:F03:actual`): the actual limiting measure of a unit `H¹` profile satisfies the standing
assumptions of the section, as a theorem

Source: `source-text/chapters/root_response/F03.tex`: "Let `μ = μ_{κ,u}` and define `Q, F, Q_N, F_N` as above"
presupposes that the actual measure `μ_{κ,u}` has the standing assumptions of the section (a probability measure
without atoms, with finite second moment, with the density assumptions of `CC:F03:core`).  Every one of them is
PROVED here for the quantum-derived `μ_{κ,u}` of a unit `H¹` input, from accepted theorems; nothing is carried as
a hypothesis:

* `μ` is a probability measure: it is a `ProbabilityMeasure`;
* no atoms: `PhysicalUnconditionalTrace.atomless` for the canonical measure `measure hκ u`, which equals `μ` by
  `RootSpectralInputsDischarge.measure_eq_limit` (the limit is the canonical full-mass measure);
* finite second moment: `RootEnergyMoment.unit_scalar` (R-484B3F6D: `∫ t² dμ = ‖u'‖² + κ‖u‖₄⁴ < ∞`);
* the density assumptions: `RootCoreH1.coreDensity_unitH1` (R-1602B09D, `CC:F03:core` for unit `H¹` input).

`actualBulkData` is then the `BulkResponseActual.ActualBulkData` of `(L, κ, u)`: `μ` is the limiting measure of
R-09E1EAE9 (`RootMeasureExistence.exists_limiting_measure`), characterised uniquely by
`IsLimitingRapidityMeasure`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QuantumNLS.F03ActualData

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BulkResponseActual (IsLimitingRapidityMeasure ActualBulkData)
open QuantumNLS.BulkResponseForm (BulkMeasure)
open QuantumNLS.ProductEnergyPreparation (OneH1)
open QuantumNLS.PhysicalQuantumMeasure (measure)

variable {L κ : ℝ} [Fact (0 < L)]

/-- `Integrable t²` gives the finite second moment in the sense of `BulkMeasure` (DEF-012). -/
theorem hasFiniteMoment_two_of_integrable {μ : Measure ℝ} (h : Integrable (fun t : ℝ => t ^ 2) μ) :
    QuantumNLS.RapidityTransport.HasFiniteMoment 2 μ := by
  unfold QuantumNLS.RapidityTransport.HasFiniteMoment QuantumNLS.RapidityTransport.moment
  have : ∀ x : ℝ, ‖x‖ₑ ^ (2 : ℝ) = ‖x ^ 2‖ₑ := fun x => by
    rw [enorm_pow]; exact ENNReal.rpow_two _
  simp_rw [this]
  exact h.hasFiniteIntegral

/-- The limiting measure `μ_{κ,u}` of a unit `H¹` input satisfies the standing assumptions of
`CC:F03:section`. -/
theorem bulkMeasure_actual (hκ : 0 < κ) {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u)
    {μ : ProbabilityMeasure ℝ} (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) :
    BulkMeasure (μ : Measure ℝ) := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
  have hmeas : (μ : Measure ℝ) = measure hκ u :=
    QuantumNLS.RootSpectralInputsDischarge.measure_eq_limit hκ hu hμ
  have hmu : μ = QuantumNLS.FreeLimit.muKappa u hu κ :=
    hμ.unique (QuantumNLS.FreeLimit.muKappa_spec u hu hκ)
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [hmeas]
    exact QuantumNLS.PhysicalUnconditionalTrace.atomless hκ u
  · have h := (QuantumNLS.RootEnergyMoment.unit_scalar hκ u hu hH).1
    rw [← hmu] at h
    exact hasFiniteMoment_two_of_integrable h
  · rw [hmeas]
    exact QuantumNLS.RootCoreH1.coreDensity_unitH1 hκ hu0 hH

/-- The actual bulk-response data `(μ_{κ,u}, bulk)` of a unit `H¹` input, existing by R-09E1EAE9. -/
theorem actualBulkData_nonempty (hκ : 0 < κ) {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) :
    Nonempty (ActualBulkData L κ hκ u hu) := by
  obtain ⟨μ, hμ⟩ := QuantumNLS.RootMeasureExistence.exists_limiting_measure hκ u hu
  exact ⟨⟨μ, hμ, bulkMeasure_actual hκ hu hH hμ⟩⟩

end QuantumNLS.F03ActualData

#print axioms QuantumNLS.F03ActualData.hasFiniteMoment_two_of_integrable
#print axioms QuantumNLS.F03ActualData.bulkMeasure_actual
#print axioms QuantumNLS.F03ActualData.actualBulkData_nonempty
