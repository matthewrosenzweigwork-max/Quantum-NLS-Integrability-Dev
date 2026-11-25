import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.PeriodicLabellingCanonical

/- KSPS-019 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS019Host.lean.
   The two bodies are the design declarations `mu` and `criticalEigenvalue` of DEFINITIONS/KSPS.lean.md (identical text
   in followup5..10, namespace NlsGge.ThirdConsultation.KSPS, binders {N : ℕ} (φ : SobolevC N) (n : ℤ)). Pro's printed bodies
   call `NlsGge.GK38.dirichletEigenvalue38` and `NlsGge.GK38.criticalEigenvalue38`, which do not exist in the repository.
   Pro's own G2 section ("Existing spectral objects") states: `criticalEigenvalue -> lamDot` and `dirichlet -> muSeq` are the
   exact house declarations over `PotPair`, the potential argument first. The only change is therefore the lexical alias
   `dirichletEigenvalue38 -> NlsGge.GK38.muSeq` and `criticalEigenvalue38 -> NlsGge.GK38.lamDot`. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def mu {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  NlsGge.GK38.muSeq (toPotPair φ) n

def criticalEigenvalue {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  NlsGge.GK38.lamDot (toPotPair φ) n

end
end NlsGge.ThirdConsultation.KSPS
