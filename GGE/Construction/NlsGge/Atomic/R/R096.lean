import Mathlib
import NlsGge.Birkhoff.W04WeightedSmoothing38

                                                                                                                       
                                                                                                                                        
                                                                                                                       
set_option autoImplicit false

namespace NlsGge.Atomic.R096

theorem orbitWeight38_admissible {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) : NlsGge.Composition.AdmissibleWeight (NlsGge.Birkhoff.orbitWeight38 c s) :=
  NlsGge.Birkhoff.orbitWeight38_admissible c s

end NlsGge.Atomic.R096
