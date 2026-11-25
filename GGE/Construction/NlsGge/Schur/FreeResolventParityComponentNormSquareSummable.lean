import NlsGge.Schur.FreeResolventPotentialOffDiagonalEntries

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators InnerProduct InnerProductSpace ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot

/-- A fixed Bool component of the actual paired ℓ² representation has a
summable squared coordinate norm. -/
theorem parityPairRepr_component_normSq_summable
    (n : ℤ) (x : ParityPair n) (b : Bool) :
    Summable (fun m : Sector n => ‖parityPairRepr n x (b, m)‖ ^ 2) := by
  have hs : Summable (fun i : Bool × Sector n => ‖parityPairRepr n x i‖ ^ 2) := by
    have hmem := (lp.memℓp (parityPairRepr n x)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa using hmem
  simpa only [Function.comp_def] using hs.comp_injective (by
    intro m₁ m₂ h
    exact (Prod.mk.inj h).2)

end NlsGge.Schur
