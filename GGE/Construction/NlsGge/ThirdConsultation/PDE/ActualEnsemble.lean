import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.Birkhoff.S04Moments38

                                                                                                                        
                                                                                                   
                                                                                                                 
                                                                                                                        
                                                                                                                       
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
