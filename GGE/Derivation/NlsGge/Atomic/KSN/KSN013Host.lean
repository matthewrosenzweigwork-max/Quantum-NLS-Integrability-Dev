import Mathlib
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.TauGammaDefs
import NlsGge.GK38.StdRootBranchesDefs

/- KSN013 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN013Host.lean.
   Round-14 row KSN-013: "host literal criticalOmittedFactor/Product once". Bodies byte-identical to followup12
   DEFINITIONS/KSN.lean.md (first block). lamDot (GK38 PeriodicLabellingCanonical), tauN/gamma2 (GK38 TauGammaDefs) and
   stdRoot38 (GK38 StdRootBranchesDefs) are the landed bodies (not redeclared).
   grep NlsGge/ and Work/ (2026-11-01): neither name exists anywhere. Header opens: the subset of Pro's KSN block whose
   namespaces are imported here (NlsGge.Pilot, NlsGge.GK38). No repair. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

def criticalOmittedFactor (n k : ℤ) (φ : PotPair) (z : ℂ) : ℂ :=
  if k = n then 1 else
    (lamDot φ k - z) / stdRoot38 (tauN φ k) (gamma2 φ k) z

def criticalOmittedProduct (n : ℤ) (φ : PotPair) (z : ℂ) : ℂ :=
  ∏' k : ℤ, criticalOmittedFactor n k φ z

end
end NlsGge.ThirdConsultation.KSN
