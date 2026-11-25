import QuantumNLS.F02TightnessActual
/-! integrator-authored trusted spec for R-E22E10B6 CC:F02:tightness (review record r18 FULL ACCEPT): headline statement(s) copied verbatim from F02TightnessActual (QuantumNLS.F02TightnessActual). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace QuantumNLS.RE22Spec
open QuantumNLS.F02TightnessActual
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis)
open QuantumNLS.RootOccupationLimit (occDist occVec summable_occDist occDist_nonneg occDist_le_two bornG_eq
  integrable_of_bdd root_occupation_limit)
open QuantumNLS.F02Tightness
open PhysicalTensor (L2T)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

set_option maxHeartbeats 8000000 in
theorem tightness_actual_spec (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {a b : ℤ} (hab : a ≠ b)
    (hIa : 0 < Ival hκ u a) (hIb : 0 < Ival hκ u b) :
    (∀ N : ℕ, 0 < N → ∀ m ∈ AN N a b (min (Ival hκ u a) (Ival hκ u b) / 2),
      |gap L κ a b m| ≤ Kab L κ (min (Ival hκ u a) (Ival hκ u b) / 2) a b) ∧
    (∀ N : ℕ, 0 < N →
      bornMeasure (physBasis L hκ N) u hu (AN N a b (min (Ival hκ u a) (Ival hκ u b) / 2))ᶜ ≤
        eN (bornMeasure (physBasis L hκ N) u hu) (Ival hκ u) /
          ENNReal.ofReal (min (Ival hκ u a) (Ival hκ u b) / 2)) ∧
    (∀ N : ℕ, 0 < N →
      bornMeasure (physBasis L hκ N) u hu {m : MArr N | 1 ≤ m.1 a ∧
          Kab L κ (min (Ival hκ u a) (Ival hκ u b) / 2) a b < |gap L κ a b m|} ≤
        eN (bornMeasure (physBasis L hκ N) u hu) (Ival hκ u) /
          ENNReal.ofReal (min (Ival hκ u a) (Ival hκ u b) / 2)) ∧
    Tendsto (fun N : ℕ => eN (bornMeasure (physBasis L hκ N) u hu) (Ival hκ u)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => bornMeasure (physBasis L hκ N) u hu
        (AN N a b (min (Ival hκ u a) (Ival hκ u b) / 2))ᶜ) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => bornMeasure (physBasis L hκ N) u hu {m : MArr N | 1 ≤ m.1 a ∧
        Kab L κ (min (Ival hκ u a) (Ival hκ u b) / 2) a b < |gap L κ a b m|}) atTop (𝓝 0) := by
  exact QuantumNLS.F02TightnessActual.tightness_actual hκ u hu hab hIa hIb

end QuantumNLS.RE22Spec
#print axioms QuantumNLS.RE22Spec.tightness_actual_spec
