import Mathlib

/-!
# M-031 host: the source Sobolev weight (proof development, AUTHOR; not self-reviewed)

Single definition, verbatim from Pro round 14 cluster 4 (PRO_DEFINITION_RESPONSE_FP80_14.md, shared M block;
DEFINITIONS/M.lean.md followup12): `def sourceH1Weight (k : ℤ) : ℝ := 1 + |Real.pi * (k : ℝ)|`.
`noncomputable section` as Pro's block preamble prescribes.  No hypothesis, no other name.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

/-- Source Sobolev weight evaluated at the raw doubled index. -/
def sourceH1Weight (k : ℤ) : ℝ := 1 + |Real.pi * (k : ℝ)|

end NlsGge.ThirdConsultation.M

end
