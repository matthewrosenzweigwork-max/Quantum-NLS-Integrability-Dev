import QuantumNLS.QuantumHighAngleTail
/-! integrator-authored trusted spec for R-F1423202 QG:thm:quantum-high-angle-tail (Terra r158 FULL ACCEPT): headline statement(s) copied verbatim from QuantumHighAngleTail (QuantumNLS.QuantumHighAngleTail). -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Complex Filter Topology Set
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.RF142Spec
open QuantumNLS.QuantumHighAngleTail
open TensorCarrier PhysicalTensor KernelDefinition LinearTailGenerator LinearTailPhysicalEvolution
open HaarSpectralTail HaarNonlinearTail HaarNonlinearAbstract HighAngleReconstruction
open HighAngleLinearEvolution HighAngleEvolutionBridge CountRotations HighAngleRotations
variable (L : ℝ) [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem R_F1423202_spec {κ E : ℝ} (hκ : 0 < κ) (hE : 0 < E) {k : ℕ} (hk : 1 ≤ k) :
    ∃ NE : ℕ, ∃ η : ℝ → ℝ, 0 < NE ∧ (∀ R, 0 ≤ η R) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ (N : ℕ) (_hNN : NE ≤ N) (hkN : k ≤ N),
        ∃ P : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N,
          (∀ m, P (bas L hκ (hk.trans hkN) m) = mask L κ N E m • bas L hκ (hk.trans hkN) m) ∧
          ∀ ψ : SymSector ℂ (L2T L) N, P ψ = ψ → ‖ψ‖ = 1 →
          ∀ R : ℝ, 0 ≤ R → ∀ θ : AngleTorus,
            (∀ n : ℤ, |(n : ℝ)| ≤ R → θ n = 1) →
            TraceClass.traceNorm (reducedDensityN N k hkN
              (quantumRotation (bas L hκ (hk.trans hkN)) θ ψ).val -
                reducedDensityN N k hkN ψ.val) ≤ ENNReal.ofReal (η R) := by
  first
  | exact QuantumNLS.QuantumHighAngleTail.«R-F1423202»
  | (apply QuantumNLS.QuantumHighAngleTail.«R-F1423202» <;> assumption)

end QuantumNLS.RF142Spec
#print axioms QuantumNLS.RF142Spec.R_F1423202_spec
