import Mathlib
import NlsGge.Spectral.ActualSpectralRemainderE02_38

                                                                                                                       
                                                                                                                         
                                                                                                     
                                                                                                              
set_option autoImplicit false

open NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.I
noncomputable section

/-- Sum of gapwise differences; never a subtraction of two infinite energies. -/
def remainderForWeight (W : ℝ → ℝ) (u : NlsGge.Pilot.PhysicalL2) : ℝ :=
  ∑' n : ℤ, gapRemainderTermE02_38 W u n

end
end NlsGge.ThirdConsultation.I
