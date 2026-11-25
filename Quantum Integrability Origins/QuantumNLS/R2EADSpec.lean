import QuantumNLS.RootIndexedPhase
/-! integrator-authored trusted spec for R-2EAD2BB6 lem:root-indexed-phase (Terra r162 FULL ACCEPT): headline statement(s) copied verbatim from RootIndexedPhase (QuantumNLS.RootIndexedPhase). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.R2EADSpec
open QuantumNLS.RootIndexedPhase
open PhysicalTensor (L2T)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_indexed_phase_spec (hκ : 0 < κ) (u : L2T L) :
    Continuous (PhysicalContinuousBoundary.boundary hκ u) ∧
    (∀ x : ℝ, Tendsto (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u))
      (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ))
      (𝓝 (PhysicalContinuousBoundary.boundary hκ u x))) ∧
    Continuous (theta hκ u) ∧ Monotone (theta hκ u) ∧ Function.Surjective (theta hκ u) ∧
    (∀ x : ℝ, |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2 →
      HasDerivAt (theta hκ u)
        (L/2+κ*∫ t : ℝ, (x-t)⁻¹^2 ∂(PhysicalQuantumMeasure.measure hκ u)) x ∧
      0 < deriv (theta hκ u) x) ∧
    (∀ a b : ℝ, a < b →
      (∀ x ∈ Ioo a b, 2 < |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re|) →
      ∃ n : ℤ, ∀ x ∈ Ioo a b, theta hκ u x = n*Real.pi) ∧
    (∀ n : ℤ, ∃! x : ℝ, theta hκ u x = MonotoneIndexedMasses.level n) ∧
    (∀ n : ℤ, L2SpatialTransfer.discriminant κ u (separator hκ u n : ℂ) = 0 ∧
      deriv (fun x : ℝ => (L2SpatialTransfer.discriminant κ u (x : ℂ)).re)
        (separator hκ u n) ≠ 0) ∧
    StrictMono (separator hκ u) ∧
    Tendsto (separator hκ u) atTop atTop ∧ Tendsto (separator hκ u) atBot atBot := by
  first
  | exact QuantumNLS.RootIndexedPhase.root_indexed_phase
  | (apply QuantumNLS.RootIndexedPhase.root_indexed_phase <;> assumption)

end QuantumNLS.R2EADSpec
#print axioms QuantumNLS.R2EADSpec.root_indexed_phase_spec
