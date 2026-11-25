import Mathlib
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.ThirdConsultation.G6.BirkhoffBasic

                                                                      
                                                                               
                                                                                              
                                                                                                           
                              
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
