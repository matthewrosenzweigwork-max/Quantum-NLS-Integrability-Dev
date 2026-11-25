import Mathlib
import NlsGge.Atomic.G5.G5018M5bCore
import NlsGge.Atomic.G3.G3031All

                                                                                
                                                                              
                                                                                                           
                                                                                                                
                                                                                                                  
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38


namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5018_diagonal_endpoint_fderiv
    (u : PhysicalL2) (n : ℤ) (lam : ℂ)
    (hm : InteriorRealDirichletGap n u)
    (hn : gamma2 (realSlice u) n ≠ 0) :
    (angleDerivative n (realSlice u) -
      fderiv ℂ (betaSum n) (realSlice u))
      (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam) =
    (psiAt n (muSeq (realSlice u) n) (realSlice u) /
      antiDiscrim (realSlice u) (muSeq (realSlice u) n)) *
    fderiv ℂ (fun ψ : PotPair => muSeq ψ n) (realSlice u)
      (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam) :=
  g5018_diagonal_endpoint_fderiv_of_beta u n lam hm hn (betaSum_analyticOnNhd_sourceBetaW n)

end
end NlsGge.GKDefinitionDesign
