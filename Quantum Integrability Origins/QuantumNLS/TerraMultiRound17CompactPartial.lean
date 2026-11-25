import QuantumNLS.TerraMultiRound17D01Repair

/-! Compact-set Lipschitz control for the actual field. This is a
continuation ingredient, not a global flow construction. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set
open scoped NNReal
open QuantumNLS.D01LocalPrimitive
namespace QuantumNLS.TerraMultiRound17CompactPartial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem field_lipschitz_on_compact (S : Hyp H) {K : Set H} (hK : IsCompact K) :
    ∃ L : ℝ≥0, LipschitzOnWith L S.Y K := by
  have ha := (QuantumNLS.TerraMultiRound17D01Repair.analytic_field_and_local_solutions S).1
  have hC : ContDiff ℝ 1 S.Y := contDiff_iff_contDiffAt.mpr (fun x => (ha x).contDiffAt)
  exact hC.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hK

#print axioms field_lipschitz_on_compact
end QuantumNLS.TerraMultiRound17CompactPartial
