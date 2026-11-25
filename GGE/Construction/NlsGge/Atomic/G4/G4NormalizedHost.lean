import Mathlib
import NlsGge.Atomic.G2.G2019
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.GK38.AbelianRatio

                                                                                                        
                                                                                                   
                                                                                                  
                                                                           
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Unsigned own-gap product K_n, not GK's printed negative zeta. -/
def normalizedZeta (n : ℤ) (φ : PotPair) (lam : ℂ) : ℂ :=
  p2OmittedRatio38 n ((φ, p2Extend38 n (sourceF n φ)), lam)

abbrev localRoot (n : ℤ) (φ : PotPair) (lam : ℂ) : ℂ :=
  standardRoot φ n lam

                                                                                                                              

/-- Literal circle integral; positive orientation and the factor -1/(2*pi*i). -/
def gapContourMean (n : ℤ) (φ : PotPair) (f : ℂ → ℂ) : ℂ :=
  (-2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    circleIntegral (fun lam => f lam / localRoot n φ lam) (discC φ n) (discR φ n)

end
end NlsGge.GKDefinitionDesign
