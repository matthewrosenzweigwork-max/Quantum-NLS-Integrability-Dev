import QuantumNLS.HierarchyInputR25m
import QuantumNLS.Reg015HFinal

/-! Discharge the printed Sobolev antecedent for the very same global chart.
This uses the frozen REG015_final via the already authorized conditional route.
Its inherited acceptance qualification remains explicit in gaps.json.
No additional missing-predecessor hypothesis is introduced. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.Def033SobolevR25m
open QuantumNLS.PhysicalTensor QuantumNLS.REF88Chart QuantumNLS.REF88PrintedChart
open QuantumNLS.Reg015Setting QuantumNLS.Sobolev
variable {L κ : ℝ} [Fact (0 < L)]

theorem sobolev_homeomorphisms (hκ : 0 < κ) (w : L2T L → K)
    (hw : PrintedChart hκ w) : QuantumNLS.HierarchyInputR25m.SobolevHomeomorphisms w := by
  intro s hs
  have hcont := printedChart_continuity hκ hw
  let e0 : L2T L ≃ₜ K :=
    { toFun := w
      invFun := chartInv hw.symp
      left_inv := chartInv_left hw.symp
      right_inv := chartInv_right hw.symp
      continuous_toFun := hcont.1
      continuous_invFun := hcont.2 }
  let e : L2T L ≃ₜ (Set.univ : Set K) := e0.trans (Homeomorph.Set.univ K).symm
  have hmod : ExactModuli e hκ := fun u n => hw.moduli u n
  obtain ⟨F, hF⟩ := (QuantumNLS.Reg015HFinal.REG015_final (L := L) hκ s hs).2.2
    Set.univ e hmod
  let U : Target (L := L) Set.univ s hs ≃ₜ h02 L s :=
    { toFun := Subtype.val
      invFun := fun z => ⟨z, Set.mem_univ _⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  refine ⟨F.trans U, fun u n => ?_⟩
  exact hF u n

end QuantumNLS.Def033SobolevR25m
#print axioms QuantumNLS.Def033SobolevR25m.sobolev_homeomorphisms
