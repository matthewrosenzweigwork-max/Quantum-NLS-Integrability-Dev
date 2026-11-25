import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Definitions.PilotInterfaces
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core
open NlsGge.Pilot

/-- The source Boolean convention preserves the actual field: `true` selects
its complex conjugate and `false` selects the field itself. -/
theorem continuous_riccatiBooleanJetFromContinuousFamilyMinimumRecovery30Fifth
    {X : Type*} [TopologicalSpace X]
    (F : ℕ → X → C(PhysicalCircle, ℂ))
    (hF : ∀ k, Continuous (F k)) (v : Jet) :
    Continuous (fun x => if v.1 then star (F v.2 x) else F v.2 x) := by
  cases hv : v.1 with
  | false =>
    simpa [hv] using hF v.2
  | true =>
    simp only [hv]
    change Continuous (fun x => star (F v.2 x))
    exact continuous_star.comp (hF v.2)

/-- Exact real norm-product square identity for the multiplier bound used in
the concrete H¹-valued jet map. -/
theorem riccatiSobolevJet_multiplierNormProductSquareMinimumRecovery30Fifth
    (k : ℕ) (x : ℝ) :
    ((2 * Real.pi) ^ k * ‖x‖) ^ 2 =
      ((2 * Real.pi) ^ k) ^ 2 * ‖x‖ ^ 2 := by
  rw [mul_pow]

end NlsGge.HierarchyRiccati.Core

end
