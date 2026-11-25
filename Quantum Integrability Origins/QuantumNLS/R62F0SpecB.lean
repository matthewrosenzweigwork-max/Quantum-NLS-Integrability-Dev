import QuantumNLS.F07ContinuityR6
/-! integrator-authored trusted spec for R-62F0B724 CC:F07:root-stability, coupling continuity (Terra r157 FULL ACCEPT): headline statement(s) copied verbatim from F07ContinuityR6 (QuantumNLS.F07ContinuityR6). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace QuantumNLS.R62F0SpecB
open QuantumNLS.F07ContinuityR6
open BetheSmooth F07Round6

set_option maxHeartbeats 8000000 in
theorem coupling_continuity_spec {N : ℕ} (hN : 0 < N) {L K₀ K₁ : ℝ} (hL : 0 < L)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (b : Fin N → ℝ) :
    ‖(EuclideanSpace.equiv (Fin N) ℝ).symm
      (root L b (K₁/N) - root L b (K₀/N))‖ / Real.sqrt N ≤
        |Real.sqrt K₁ - Real.sqrt K₀| / Real.sqrt L := by
  first
  | exact QuantumNLS.F07ContinuityR6.coupling_continuity
  | (apply QuantumNLS.F07ContinuityR6.coupling_continuity <;> assumption)

end QuantumNLS.R62F0SpecB
#print axioms QuantumNLS.R62F0SpecB.coupling_continuity_spec
