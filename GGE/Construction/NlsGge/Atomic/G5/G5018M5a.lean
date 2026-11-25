import Mathlib
import NlsGge.Atomic.G5.G5018M5Ep
import NlsGge.Atomic.G3.G3031All

                                                                                
                                                                              
                                                                                                      
                                                                                                        
                                                                                                          
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38


namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5018_diagonal_local_lift
    (u : PhysicalL2) (n : ℤ)
    (hn : gamma2 (realSlice u) n ≠ 0) :
    ∃ (V : Set PotPair) (e : PotPair → ℂ),
      IsOpen V ∧ realSlice u ∈ V ∧
      V ⊆ sourceBetaW \ collapsedSet n ∧
      AnalyticOnNhd ℂ e V ∧
      (∀ φ ∈ V, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
        Complex.exp (Complex.I * e φ) = s * etaExponential n φ) ∧
      ∀ φ ∈ V,
        angleDerivative n φ - fderiv ℂ (betaSum n) φ = fderiv ℂ e φ :=
  g5018_diagonal_local_lift_of_beta u n hn (betaSum_analyticOnNhd_sourceBetaW n)

end
end NlsGge.GKDefinitionDesign
