import Mathlib
import NlsGge.Atomic.F.F010Host
import NlsGge.Birkhoff.H03Diagonal38b

                                                                                    
                                                                                               
                                                                                                                     
                                                                                                               
                                                                         
set_option autoImplicit false
noncomputable section
open MeasureTheory
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.I

/-- Same F law, expressed in ordinary physical Fourier H^r coordinates. -/
def finiteOrderLaw (c : ℕ → ℝ) (r m : ℕ) : Measure (SobolevHilbert (r : ℝ)) :=
  (NlsGge.ThirdConsultation.F.finiteGapLaw m (coefficient c)).map
    (fun u => physFS38 r (sobolevToL2_38 (m - 1) u))

end NlsGge.ThirdConsultation.I
