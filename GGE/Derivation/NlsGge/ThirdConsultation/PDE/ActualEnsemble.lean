import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.Birkhoff.S04Moments38

/- PDE ENSEMBLE HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE-level host (root main probe; imports
   the landed PDE.BirkhoffTop).  Target NlsGge/ThirdConsultation/PDE/ActualEnsemble.lean, namespace
   NlsGge.ThirdConsultation.PDE.  Hosts ONLY finiteGapField, actualNu, actualMuW, bodies verbatim from followup13
   DEFINITIONS/PDE.lean.md:299-310 (grep NlsGge/ and Work/ 2026-11-02: none declared).  finiteGibbsDensity is NOT hosted
   (its body needs NlsGge.Birkhoff.nuHatDens38, absent from NlsGge).  Root may merge these into the PDE shared host. -/
set_option autoImplicit false
open MeasureTheory
open NlsGge.Pilot NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

def finiteGapField (Λ : Finset ℤ) (z : Λ → ℂ) : PhysicalL2 :=
  actualBirkhoffTop38.finiteGapField38 Λ z

def actualNu (c : ℕ → ℝ) (Λ : Finset ℤ) : Measure PhysicalL2 :=
  actualBirkhoffTop38.nu38 c Λ

/-- The full Gibbs law built from the same actual topological Birkhoff map. -/
def actualMuW (c : ℕ → ℝ) : Measure PhysicalL2 :=
  actualBirkhoffTop38.muW38 c

end
end NlsGge.ThirdConsultation.PDE
