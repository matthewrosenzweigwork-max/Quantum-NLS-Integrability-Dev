import Mathlib
import NlsGge.Atomic.G5.G5019
import NlsGge.Atomic.G5.G5020
import NlsGge.Atomic.G5.G5025Sup2
import NlsGge.Atomic.G5.G5025Sup3

                                                                        
                                                                           
                                                                                                                                   
                                           
                                                                                                                                    
                                                                 
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5025 (u : PhysicalL2) (n : ℤ) (hn : gamma2 (realSlice u) n ≠ 0) :
  cartesianX n (realSlice u)^2 + cartesianY n (realSlice u)^2 ≠ 0 ∧
  ∀ lam : ℂ, 2 * pairPoissonCLM
    (fderiv ℂ (fun φ => discrim φ lam) (realSlice u))
    (angleDerivative n (realSlice u)) = psiAt n lam (realSlice u) := by
  refine ⟨G5025Sup3.radius_ne_zero u n hn, fun lam => ?_⟩
  have hB : realSlice u ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u)
  obtain ⟨V, hV, -, -, hsum, -⟩ := G5020 n (realSlice u) hB
  exact G5025Sup2.core25 u n (fun m lam' => G5019 u m n lam' hn)
    (hsum (realSlice u) (mem_of_mem_nhds hV)) lam

end
end NlsGge.GKDefinitionDesign
