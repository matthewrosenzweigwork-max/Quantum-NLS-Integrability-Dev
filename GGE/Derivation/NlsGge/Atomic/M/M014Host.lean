import Mathlib
import NlsGge.Atomic.M.M001

/- M-014 HOST01 (proof development, AUTHOR; not reviewed).  Host of `M.complexHigherAction`, body VERBATIM from Pro round 14
   (PRO_DEFINITION_RESPONSE_FP80_14.md cluster 4 "Complex level-k action J_{n,k}").  Grep of NlsGge/ (2026-11-01): the name does
   not exist.  Other round-14 cluster-4 hosts (sourceH1Weight, finiteGapPair, ...) belong to other packets and are NOT installed here. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M
noncomputable section

/-- Complex level-k action J_{n,k}; raw GK higherAction has the extra k. -/
def complexHigherAction (φ : PotPair) (n : ℤ) (k : ℕ) : ℂ :=
  if hk : 1 ≤ k then
    (k : ℂ)⁻¹ * NlsGge.GKDefinitionDesign.higherAction k φ n
  else 0

end
end NlsGge.ThirdConsultation.M
