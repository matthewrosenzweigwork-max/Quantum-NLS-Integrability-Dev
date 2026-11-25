import QuantumNLS.TerraMultiRound51CorrelationExpansion

/-! Transport the finite-orthant correlation expansion to the physical
large-parameter scale. This does not identify a recursive tree with it. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound52InverseScale
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev
open QuantumNLS.TerraMultiRound48Leading QuantumNLS.TerraMultiRound48TreeFubini
open QuantumNLS.TerraMultiRound51TaylorIntegral QuantumNLS.TerraMultiRound51CorrelationExpansion

variable {L : ℝ} [Fact (0 < L)]

theorem inverse_scale_paths {n q : ℕ} (paths : Fin q → Finset (Fin n))
    (Y : ℝ) (t : Fin n → ℝ) :
    scaledShift paths Y⁻¹ t = pathShift paths Y t := by
  ext j
  simp [scaledShift, pathShift, div_eq_mul_inv]

/-- All positive allowed Taylor degrees, transported to Y → +∞. -/
theorem correlation_expansion_atTop {n m k d : ℕ} (hk : 1 ≤ k)
    (f : Fin (m + 2) → Hk L k) (hd : d + 1 ≤ 2 * k)
    (paths : Fin (m + 2) → Finset (Fin n)) :
    (fun Y : ℝ => integratedCorrelation f paths Y⁻¹ -
      ∑ j ∈ Finset.range (d + 2), (Y⁻¹ ^ j) • integratedCoeff (Cfun f) paths j)
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (d + 1)) := by
  simpa only [Function.comp_def] using
    (correlation_expansion hk f hd paths).comp_tendsto
      (tendsto_inv_atTop_zero : Tendsto (fun Y : ℝ => Y⁻¹) atTop (𝓝 0))

/-- Degree zero is the fixed-field continuity assertion at large Y. -/
theorem correlation_leading_atTop {n m k : ℕ} (hk : 1 ≤ k)
    (f : Fin (m + 2) → Hk L k) (paths : Fin (m + 2) → Finset (Fin n)) :
    Tendsto (fun Y : ℝ => integratedCorrelation f paths Y⁻¹) atTop (𝓝 (Cfun f 0)) := by
  exact (correlation_leading hk f paths).comp
    (tendsto_inv_atTop_zero : Tendsto (fun Y : ℝ => Y⁻¹) atTop (𝓝 0))

#print axioms inverse_scale_paths
#print axioms correlation_expansion_atTop
#print axioms correlation_leading_atTop
end QuantumNLS.TerraMultiRound52InverseScale
