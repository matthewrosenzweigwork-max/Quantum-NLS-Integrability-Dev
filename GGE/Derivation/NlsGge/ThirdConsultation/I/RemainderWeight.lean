import Mathlib
import NlsGge.Spectral.ActualSpectralRemainderE02_38

/- I REMAINDER-WEIGHT HOST01 (proof development, AUTHOR; not reviewed; target NlsGge/ThirdConsultation/I/RemainderWeight.lean,
   namespace NlsGge.ThirdConsultation.I). Hosts ONLY `remainderForWeight`, body verbatim from DEFINITIONS/I.lean.md:81-82
   (grep: absent from NlsGge). Opens reproduce the I.lean.md block restricted to what the body needs.
   `gapRemainderTermE02_38` is the production definition (Spectral/ActualSpectralRemainderE02_38.lean:287). -/
set_option autoImplicit false

open NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.I
noncomputable section

/-- Sum of gapwise differences; never a subtraction of two infinite energies. -/
def remainderForWeight (W : ℝ → ℝ) (u : NlsGge.Pilot.PhysicalL2) : ℝ :=
  ∑' n : ℤ, gapRemainderTermE02_38 W u n

end
end NlsGge.ThirdConsultation.I
