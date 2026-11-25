import Mathlib
import NlsGge.Atomic.G4.G4NormalizedHost
import NlsGge.GK38.AbelianPsiNumerator
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.GradFundamentalDefs
import NlsGge.GK38.DirichletRealReality
import NlsGge.GK38.DirichletLabels
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic

                                                                                                               
                                                                                               
                                                                                                             
                                                                                                             
                                                                                                        
                                                                                                     
                                                                                                                
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

-- Actual terminal sheet, including complex collapsed gaps.
def terminalRoot (n : ℤ) (φ : PotPair) : ℂ :=
  antiDiscrim φ (muSeq φ n) /
    (((2 * Complex.I) / (Lib.piN n : ℂ)) *
      a5OmittedRootProduct38 n (φ, muSeq φ n))

def InteriorRealDirichletGap (n : ℤ) (u : PhysicalL2) : Prop :=
  NlsGge.SpectralFoundations.actualGapLowerAllE02_38 u n < gkMu u n ∧
  gkMu u n < NlsGge.SpectralFoundations.actualGapUpperAllE02_38 u n

def radiusQuotient (n : ℤ) (φ : PotPair) : ℂ :=
  normalizedZeta n φ (muSeq φ n) /
    p6PsiNumerator38 n (sourceF n) φ (muSeq φ n)

def signedRadius (n : ℤ) (φ : PotPair) : ℂ :=
  -Complex.I * terminalRoot n φ

end
end NlsGge.GKDefinitionDesign
