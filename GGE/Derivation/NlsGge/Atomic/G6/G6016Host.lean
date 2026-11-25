import Mathlib
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.ThirdConsultation.G6.BirkhoffBasic

/- G6-016 HOST (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6016Host.lean, namespace NlsGge.GKDefinitionDesign.
   Bodies of `physicalHamiltonianField` and `rotateOneCoordinate` BYTE-IDENTICAL to followup12
   DEFINITIONS/G6.lean.md (round 14 active replacement); neither name is declared anywhere else in NlsGge/.
   G6 shared-context opens. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Physical real Hamiltonian convention: X_H = -(i/2) grad H. -/
def physicalHamiltonianField (H : PhysicalL2 → ℝ) (u : PhysicalL2) : PhysicalL2 :=
  -((1 / 2 : ℝ) • ((Complex.I : ℂ) • gradient H u))

def rotateOneCoordinate (n : ℤ) (t : ℝ) (z : Lib.L2Z) : Lib.L2Z :=
  z + lp.single 2 n ((Complex.exp (-Complex.I * (t : ℂ)) - 1) * z n)

end
end NlsGge.GKDefinitionDesign
