import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14Action

/- PDEACTRAW HOST PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target
   NlsGge/ThirdConsultation/PDE/Round14ActionRaw.lean, namespace NlsGge.ThirdConsultation.PDE. Bodies VERBATIM from the
   Pro r14 shared PDE block (l.2702-2710): the theorem obligation rawAction_scaled_mem (proved here: nonnegative summable
   ⇒ Memℓp _ 1 via memℓp_gen) and the definition rawActionToPositive. -/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

theorem rawAction_scaled_mem
    (I : ℤ → ℝ) (hI : I ∈ positiveActionCone) :
  Memℓp (fun n : ℤ => actionWeight n * I n) 1 := by
  apply memℓp_gen
  refine hI.2.congr (fun n => ?_)
  have h0 : 0 ≤ actionWeight n * I n := mul_nonneg (sobolevModeWeight_pos 1 n).le (hI.1 n)
  rw [ENNReal.toReal_one, Real.rpow_one, Real.norm_of_nonneg h0]

def rawActionToPositive (I : ℤ → ℝ) (hI : I ∈ positiveActionCone) :
    PositiveActionSpace :=
  ⟨⟨fun n : ℤ => actionWeight n * I n, rawAction_scaled_mem I hI⟩,
    fun n : ℤ => mul_nonneg (sobolevModeWeight_pos 1 n).le (hI.1 n)⟩

end
end NlsGge.ThirdConsultation.PDE
