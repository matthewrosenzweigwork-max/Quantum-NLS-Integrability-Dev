import Mathlib

/- M-047 HOST01 (proof development, AUTHOR; not reviewed).  Target NlsGge/Atomic/M/M047Host.lean.  Hosts
   M.actionMomentRelations and its alias M.ActionMomentRelations, bodies VERBATIM from Pro round 15
   followup13 handoff/definitions_design_20261027/DEFINITIONS/M.lean.md:282-286 (namespace
   NlsGge.ThirdConsultation.M, noncomputable section).  Grep of NlsGge/ (2026-11-01): neither name exists. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.M
noncomputable section

def actionMomentRelations (m : ℕ) (A0 A1 Am : ℝ) : Prop :=
  0 ≤ A0 ∧ A0 ≤ A1 ∧ A1 ≤ Am ∧
  A1^m ≤ Am*A0^(m-1)

def ActionMomentRelations := actionMomentRelations

end
end NlsGge.ThirdConsultation.M
