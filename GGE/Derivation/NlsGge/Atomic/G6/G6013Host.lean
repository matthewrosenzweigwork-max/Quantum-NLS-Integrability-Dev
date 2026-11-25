import Mathlib
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff

/- G6-013 HOST (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6013Host.lean.
   Hosts the one design name the G6-013/G6-014 heads need that no NlsGge module defines (grep of NlsGge/, Armstrong/ and
   Work/isolated_20261027 worker folders, 2026-11-01): inverseBirkhoffCartesian.  Body byte-identical to followup12
   DEFINITIONS/G6.lean.md (round 14, line 78-79).  realBirkhoffCartesian / CartesianReal are the landed
   NlsGge/ThirdConsultation/G6/RealCartesianBirkhoff.lean declarations (not redeclared). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def inverseBirkhoffCartesian : CartesianReal → PhysicalL2 :=
  Function.invFun realBirkhoffCartesian

end
end NlsGge.GKDefinitionDesign
