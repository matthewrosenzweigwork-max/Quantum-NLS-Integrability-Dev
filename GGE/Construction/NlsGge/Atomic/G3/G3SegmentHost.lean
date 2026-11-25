import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.G3.G3019
import NlsGge.Atomic.G3.G3RatioHost
import NlsGge.Atomic.G3.G3ZetaHost

                                                                                                       
                                                                                                      
                                                                                                    
                                                                
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def betaSegmentDensity (n m : ℤ) (φ : PotPair) (t : ℝ) : ℂ :=
  betaRootRatioAlong n m φ t * betaZeta n m φ (betaSegmentPoint m φ t) *
    betaOmega m φ

def betaFinalSegment (n m : ℤ) (φ : PotPair) (ε : ℝ) : ℂ :=
  ∫ t in ε..(1 : ℝ), betaSegmentDensity n m φ t

def collapsedBetaFinalSegment (n m : ℤ) (φ : PotPair) (ε : ℝ) : ℂ :=
  ∫ t in ε..(1 : ℝ),
    betaZeta n m φ (tauN φ m + (t : ℂ) * (muSeq φ m-tauN φ m)) *
      (muSeq φ m-tauN φ m)

def CollapsingOffEndpointSequence (m : ℤ) (v : ℕ → PotPair) (φ : PotPair) : Prop :=
  φ ∈ collapsedSet m \ endpointSet m ∧ Tendsto v atTop (𝓝 φ) ∧
  ∀ j : ℕ, v j ∈ sourceW \ (collapsedSet m ∪ endpointSet m) ∧
    ‖muSeq (v j) m-lamMinus (v j) m‖ ≤ ‖muSeq (v j) m-lamPlus (v j) m‖

end
end NlsGge.GKDefinitionDesign
