import Mathlib
import NlsGge.Spectral.ActualQuasimomentumE02_38
import NlsGge.Sobolev.SourceWeighted

                                                                                                                          
                                                                                                                                    
set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.I

/-- Extended energy is defined before any assertion of integrability. -/
def spectralEnergyENN (W : ℝ → ℝ) (u : PhysicalL2) : ℝ≥0∞ :=
  ENNReal.ofReal (2 / Real.pi) *
    ∫⁻ t : ℝ, ENNReal.ofReal (W (2 * t) * actualGapHeightE02_38 u t)

end NlsGge.ThirdConsultation.I
