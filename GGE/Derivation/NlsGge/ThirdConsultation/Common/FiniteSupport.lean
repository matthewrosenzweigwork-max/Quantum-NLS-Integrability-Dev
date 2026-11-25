import Mathlib
import NlsGge.GK38.Lib.InterpolationHilbertOp

/- COMMONFSS HOST PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target
   NlsGge/ThirdConsultation/Common/FiniteSupport.lean, namespace NlsGge.ThirdConsultation.Common (root/integrator to place;
   BirkhoffRaw.lean hosts the same COMMON block's actualPhi/actualPhiInv aliases in this namespace).
   Body VERBATIM from followup13 DEFINITIONS/COMMON.lean.md l.133-135 ("Finite support in the integer coordinate sequence").
   LEXICAL REPAIR (same as BirkhoffRaw's for actualPhi): binder type `NlsGge.Birkhoff.Lib.L2Z` -> `NlsGge.GK38.Lib.L2Z`
   (only the latter exists: NlsGge/GK38/Lib/InterpolationHilbertOp.lean:29, `abbrev L2Z := lp (fun _ : ℤ => ℂ) 2`).
   Consumers: PDE-058 (hv), PDE-063.. rotation curves. grep NlsGge/: no existing declaration of this name. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.Common

/-- Finite support in the integer coordinate sequence. -/
def FiniteSupportSequence (z : NlsGge.GK38.Lib.L2Z) : Prop :=
  {n : ℤ | z n ≠ 0}.Finite

end NlsGge.ThirdConsultation.Common
