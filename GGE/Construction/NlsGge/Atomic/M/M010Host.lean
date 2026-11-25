import Mathlib
import NlsGge.Atomic.M.M009Support8
import NlsGge.Spectral.ActualGapActionAllNE02_38
import NlsGge.Spectral.ActualQuasimomentumE02_38

                                                                                                  
                                                                                                                               
                                                                                                                
                                                                                                               
                                                                                                                 
                                                                                                                   
                                                                                                                    
                                                                                                                      
                                                                                                                         
                                                                                                   
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.M
noncomputable section

def spectralHeight (u : PhysicalL2) (_n : ℤ) (x : ℝ) : ℝ :=
  actualGapHeightE02_38 u x

def openGap (u : PhysicalL2) (n : ℤ) : Set ℝ :=
  Set.Ioo (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)

def closedGap (u : PhysicalL2) (n : ℤ) : Set ℝ :=
  Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)

end
end NlsGge.ThirdConsultation.M

namespace NlsGge.ThirdConsultation.MPrimitive
noncomputable section

abbrev PositiveHeight := {t : ℝ // 0 < t}

def positiveHeightFilter : Filter PositiveHeight :=
  Filter.comap (fun t : PositiveHeight => t.1) (𝓝[>] (0 : ℝ))

def boundaryPoint (x : ℝ) (upper : Bool) (t : PositiveHeight) : ℂ :=
  (x : ℂ) + (if upper then Complex.I else -Complex.I) * (t.1 : ℂ)

def HasBoundaryValue (u : PhysicalL2) (x : ℝ) (upper : Bool) (A : ℂ) : Prop :=
  ∃ F : PositiveHeight → ℂ,
    (∀ t : PositiveHeight,
      ∃ ht : realSlice u ∈ gkW ∧
          boundaryPoint x upper t ∈ endpointClosureFiber (realSlice u),
        F t = M.primitive ⟨(realSlice u, boundaryPoint x upper t), ht⟩) ∧
    Tendsto F positiveHeightFilter (𝓝 A)

end
end NlsGge.ThirdConsultation.MPrimitive
