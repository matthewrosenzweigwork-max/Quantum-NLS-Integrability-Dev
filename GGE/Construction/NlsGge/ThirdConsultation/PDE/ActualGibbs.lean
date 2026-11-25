import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.Birkhoff.NuHatDens38

                                                                                                                                 
                                                                                                  
                                                                                                                           
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

def finiteGibbsDensity (c : ℕ → ℝ) (Λ : Finset ℤ) (z : Λ → ℂ) : ℝ≥0∞ :=
  NlsGge.Birkhoff.nuHatDens38 actualBirkhoffTop38 c Λ z

end
end NlsGge.ThirdConsultation.PDE
