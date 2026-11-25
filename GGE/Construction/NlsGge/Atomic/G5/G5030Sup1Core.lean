import Mathlib
import NlsGge.Atomic.G5.G5025Sup2
import NlsGge.Atomic.G5.G5018Sup1
import NlsGge.Atomic.G5.G5029Host
import NlsGge.Atomic.G5.G5031Host

                                                                                
                                                                                                
                                                                                                                                   
                                                                                                                                 
                                                                                                                        
                                                                                                                 
                                                                                                     
                                                                          
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G5030Sup1Aux
noncomputable section

theorem hasSum_angleIntegralDerivative (u : PhysicalL2) (n : ℤ)
    (hbeta : HasSum (fun m : ℤ => if m = n then (0 : PotPair →L[ℂ] ℂ)
        else fderiv ℂ (beta m n) (realSlice u)) (fderiv ℂ (betaSum n) (realSlice u))) :
    HasSum (fun m : ℤ => angleIntegralDerivative m n (realSlice u))
      (angleDerivative n (realSlice u)) := by
  have h := hbeta.add (hasSum_ite_eq n (angleDerivative n (realSlice u) -
    fderiv ℂ (betaSum n) (realSlice u)))
  convert h using 1
  · funext m
    by_cases hm : m = n
    · simp [angleIntegralDerivative, hm]
    · simp [angleIntegralDerivative, hm]
  · abel

theorem g5030_core
    (h29 : ∀ (u : PhysicalL2) (k l m n : ℤ),
      AllDirichletLeft u → gamma2 (realSlice u) m ≠ 0 → gamma2 (realSlice u) n ≠ 0 →
      pairPoissonCLM (angleIntegralDerivative k m (realSlice u))
        (angleIntegralDerivative l n (realSlice u)) = 0)
    (hbeta : ∀ (u : PhysicalL2) (n : ℤ), HasSum (fun m : ℤ => if m = n then (0 : PotPair →L[ℂ] ℂ)
        else fderiv ℂ (beta m n) (realSlice u)) (fderiv ℂ (betaSum n) (realSlice u)))
    (u : PhysicalL2) (m n : ℤ) (hleft : AllDirichletLeft u)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0) :
    anglePoisson m n (realSlice u) = 0 := by
  have hSm := hasSum_angleIntegralDerivative u m (hbeta u m)
  have hSn := hasSum_angleIntegralDerivative u n (hbeta u n)
  have hterm : ∀ l : ℤ, pairPoissonCLM (angleDerivative m (realSlice u))
      (angleIntegralDerivative l n (realSlice u)) = 0 := by
    intro l
    rw [pairPoissonCLM_antisymm]
    have h2 := G5025Sup2.hasSum_pairPoisson (angleIntegralDerivative l n (realSlice u)) _ _ hSm
    have hz : (fun k : ℤ => pairPoissonCLM (angleIntegralDerivative l n (realSlice u))
        (angleIntegralDerivative k m (realSlice u))) = fun _ => (0 : ℂ) :=
      funext fun k => h29 u l k n m hleft hn hm
    rw [hz] at h2
    rw [h2.unique hasSum_zero, neg_zero]
  have h1 := G5025Sup2.hasSum_pairPoisson (angleDerivative m (realSlice u)) _ _ hSn
  have hz : (fun l : ℤ => pairPoissonCLM (angleDerivative m (realSlice u))
      (angleIntegralDerivative l n (realSlice u))) = fun _ => (0 : ℂ) := funext hterm
  rw [hz] at h1
  unfold anglePoisson
  exact h1.unique hasSum_zero

end
end G5030Sup1Aux
end NlsGge.GKDefinitionDesign
