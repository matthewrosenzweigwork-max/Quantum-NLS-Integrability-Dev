import Mathlib
import NlsGge.Atomic.G5.G5018
import NlsGge.Atomic.G5.G5018M5a
import NlsGge.Atomic.G5.G5020
import NlsGge.Atomic.G5.G5024
import NlsGge.Atomic.G5.G5019Sup1
import NlsGge.Atomic.G5.G5019Sup2
import NlsGge.Atomic.G5.G5019Sup3
import NlsGge.Atomic.G5.G5019Sup4
import NlsGge.Atomic.G5.G5019Sup5

                                                                        
                                                                           
                                                                                                                         
                                               
                                                                                                                          
                                                                                                                                        
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5019 (u : PhysicalL2) (m n : ℤ) (lam : ℂ)
    (hn : gamma2 (realSlice u) n ≠ 0) :
  2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice u))
    (angleIntegralDerivative m n (realSlice u)) =
    psiAt n (muSeq (realSlice u) m) (realSlice u) *
      PoissonMixed38.dirInterpolation38 (realSlice u) (muSeq (realSlice u) m) lam := by
  have hAID : ContinuousAt (fun w : PhysicalL2 => angleIntegralDerivative m n (realSlice w)) u := by
    by_cases hmn : m = n
    · subst hmn
      obtain ⟨V, e, hV, hu, -, he, -, hder⟩ := g5018_diagonal_local_lift u m hn
      exact G5019Sup3.continuousAt_angleIntegralDerivative_diag m u V e hV hu he hder
    · exact G5019Sup3.continuousAt_angleIntegralDerivative_offDiag m n hmn
        (G5020Aux.term_analytic n m) u
  exact G5019Sup5.core u m n lam hn (fun w hw hgw => G5018 w m n lam hw hgw)
    (dense_interiorRealDirichletGap m) hAID

end
end NlsGge.GKDefinitionDesign
