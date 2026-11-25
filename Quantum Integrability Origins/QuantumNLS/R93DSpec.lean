import QuantumNLS.PreparationStability
/-! integrator-authored trusted spec for R-93D28FE1 prop:stability (projective_reconstruction.tex; Terra r133 ACCEPT):
the exact density of a unit preparation is the partial trace of its occupation-coefficient image; the two
fidelity/distance bounds hold for any two unit physical preparations, uniformly for a common unitary family. Complete
physical basis and gauge are explicit parameters; N = 1+q. Statements copied verbatim. -/
namespace R93DSpec
open scoped InnerProductSpace ComplexConjugate ENNReal
open QuantumNLS.TraceClass QuantumNLS.TensorCarrier
open QuantumNLS.Occupation QuantumNLS.OccupationHilbert
open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.ExactDensity
open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform
  QuantumNLS.BetheOccupationGauge QuantumNLS.CartesianOccupationTransfer
open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.PreparationStability

theorem density_entry_spec {L : ℝ} [Fact (0 < L)] {q : ℕ} (b : BetheBasis L (1 + q)) (g : Gauge) (ψ : HN L (1 + q)) (a c : ℤ) :
    ⟪oneBasis a, density b g ψ (oneBasis c)⟫_ℂ = QuantumNLS.AuxiliaryDensity.gammaEntry b g ψ a c := by
  apply QuantumNLS.PreparationStability.density_entry <;> assumption

theorem density_partialTrace_spec {L : ℝ} [Fact (0 < L)] {q : ℕ} (b : BetheBasis L (1 + q)) (g : Gauge) (ψ : HN L (1 + q)) :
    density b g ψ = reducedDensity (physicalV b g ψ) := by
  apply QuantumNLS.PreparationStability.density_partialTrace <;> assumption

theorem stability_spec {L : ℝ} [Fact (0 < L)] {q : ℕ} (b : BetheBasis L (1 + q)) (g : Gauge)
    (ψ φ : HN L (1 + q)) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceNorm (density b g ψ - density b g φ) ≤
      ENNReal.ofReal (2 * Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2)) ∧
    ENNReal.ofReal (2 * Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2)) ≤
      ENNReal.ofReal (2 * ‖ψ - φ‖) := by
  apply QuantumNLS.PreparationStability.stability <;> assumption

theorem common_unitary_spec {L : ℝ} [Fact (0 < L)] {q : ℕ} {T : Type*} (b : BetheBasis L (1 + q)) (g : Gauge)
    (U : T → HN L (1 + q) ≃ₗᵢ[ℂ] HN L (1 + q))
    (ψ φ : HN L (1 + q)) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (t : T) :
    traceNorm (density b g (U t ψ) - density b g (U t φ)) ≤
      ENNReal.ofReal (2 * Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2)) := by
  apply QuantumNLS.PreparationStability.common_unitary <;> assumption

theorem uniform_stability_spec {L : ℝ} [Fact (0 < L)] {q : ℕ} {T : Type*} (b : BetheBasis L (1 + q)) (g : Gauge)
    (U : T → HN L (1 + q) ≃ₗᵢ[ℂ] HN L (1 + q))
    (ψ φ : HN L (1 + q)) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (K : Set T) :
    (⨆ t : K, traceNorm (density b g (U t ψ) - density b g (U t φ))) ≤
      ENNReal.ofReal (2 * Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2)) ∧
    ENNReal.ofReal (2 * Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2)) ≤
      ENNReal.ofReal (2 * ‖ψ - φ‖) := by
  apply QuantumNLS.PreparationStability.uniform_stability <;> assumption

theorem overlap_le_distance_spec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    2 * Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2) ≤ 2 * ‖ψ - φ‖ := by
  apply QuantumNLS.PreparationStability.overlap_le_distance <;> assumption

end R93DSpec
#print axioms R93DSpec.density_entry_spec
#print axioms R93DSpec.density_partialTrace_spec
#print axioms R93DSpec.stability_spec
#print axioms R93DSpec.common_unitary_spec
#print axioms R93DSpec.uniform_stability_spec
#print axioms R93DSpec.overlap_le_distance_spec
