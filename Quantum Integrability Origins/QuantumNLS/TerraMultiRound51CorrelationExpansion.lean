import QuantumNLS.TerraMultiRound51TaylorLeading
import QuantumNLS.TerraMultiRound49IntegratedLittleO

/-! Integrated correlations split into the explicit finite coefficient sum
and the previously proved fixed-factor little-oh residual. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound51CorrelationExpansion
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev QuantumNLS.Fourier QuantumNLS.CorrelationTaylor
open QuantumNLS.TerraMultiRound48Leading QuantumNLS.TerraMultiRound48Orthant
open QuantumNLS.TerraMultiRound49IntegratedLittleO QuantumNLS.TerraMultiRound51TaylorCoeff
open QuantumNLS.TerraMultiRound51TaylorIntegral

variable {L : ℝ} [Fact (0 < L)]

theorem taylor_integrable {n q : ℕ} (C : (Fin q → ℝ) → ℂ)
    (paths : Fin q → Finset (Fin n)) (d : ℕ) (z : ℝ) :
    Integrable (fun t : Fin n → ℝ => ((∏ i, Real.exp (-t i) : ℝ) : ℂ) *
      taylorPoly C d (scaledShift paths z t))
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))) := by
  simp_rw [taylorPoly_path, Finset.mul_sum, mul_smul_comm]
  exact integrable_finsetSum _ (fun j _ => (pathCoeff_integrable C paths j).smul (z ^ j : ℝ))

def integratedCorrelation {n m k : ℕ} (f : Fin (m + 2) → Hk L k)
    (paths : Fin (m + 2) → Finset (Fin n)) (z : ℝ) : ℂ :=
  ∫ t : Fin n → ℝ, ((∏ i, Real.exp (-t i) : ℝ) : ℂ) *
    Cfun f (scaledShift paths z t) ∂
    (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ))))

/-- Exact splitting for every scale, including zero. -/
theorem residual_eq_difference {n m k : ℕ} (hk : 1 ≤ k)
    (f : Fin (m + 2) → Hk L k) (paths : Fin (m + 2) → Finset (Fin n))
    (d : ℕ) (z : ℝ) :
    integratedResidual f d paths z = integratedCorrelation f paths z -
      ∑ j ∈ Finset.range (d + 2), (z ^ j) • integratedCoeff (Cfun f) paths j := by
  have hc := orthant_bounded_integrable n (fun t => Cfun f (scaledShift paths z t))
    (L * cL L ^ (m + 2) * ∏ j, ‖f j‖)
    ((Cfun_continuous hk f).comp (scaledShift_continuous_t paths z))
    (fun t => norm_Cfun_le hk f _)
  have hp := taylor_integrable (Cfun f) paths (d + 1) z
  unfold integratedResidual integratedCorrelation
  simp_rw [mul_sub]
  rw [integral_sub hc hp, integral_taylorPoly_path]

/-- Each fixed family of factors has the positive-degree integrated
Taylor expansion with an actual little-oh remainder. -/
theorem correlation_expansion {n m k d : ℕ} (hk : 1 ≤ k)
    (f : Fin (m + 2) → Hk L k) (hd : d + 1 ≤ 2 * k)
    (paths : Fin (m + 2) → Finset (Fin n)) :
    (fun z : ℝ => integratedCorrelation f paths z -
      ∑ j ∈ Finset.range (d + 2), (z ^ j) • integratedCoeff (Cfun f) paths j)
      =o[𝓝 0] (fun z : ℝ => z ^ (d + 1)) := by
  simpa only [← residual_eq_difference hk f paths d] using
    integratedResidual_isLittleO hk f hd paths

#print axioms taylor_integrable
#print axioms residual_eq_difference
#print axioms correlation_expansion
end QuantumNLS.TerraMultiRound51CorrelationExpansion
