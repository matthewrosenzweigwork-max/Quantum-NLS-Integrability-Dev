import Mathlib
import NlsGge.Atomic.G5.G5025Sup1
import NlsGge.Atomic.G5.G5018Sup1
import NlsGge.Atomic.G5.G5018Host
import NlsGge.Atomic.G5.G5023
import NlsGge.Atomic.G5.G5024

                                                                                       
                                                                                         
                                                                                                                    
                                                                          
                                                                                                      
                                                                                                                                 
                                                                                                                       
                                                                                                                                 
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G5025Sup2
noncomputable section

theorem hasSum_pairPoisson {ι : Type*} (L : PotPair →L[ℂ] ℂ) (f : ι → (PotPair →L[ℂ] ℂ))
    (S : PotPair →L[ℂ] ℂ) (h : HasSum f S) :
    HasSum (fun i => pairPoissonCLM L (f i)) (pairPoissonCLM L S) := by
  have h1 : HasSum (fun i => f i (-Complex.I • (pairGradientCLM L).2, Complex.I • (pairGradientCLM L).1))
      (S (-Complex.I • (pairGradientCLM L).2, Complex.I • (pairGradientCLM L).1)) :=
    (ContinuousLinearMap.apply ℂ ℂ
      ((-Complex.I • (pairGradientCLM L).2, Complex.I • (pairGradientCLM L).1) : PotPair)).hasSum h
  have e : ∀ M : PotPair →L[ℂ] ℂ, pairPoissonCLM L M =
      -(M (-Complex.I • (pairGradientCLM L).2, Complex.I • (pairGradientCLM L).1)) := fun M => by
    rw [pairPoissonCLM_antisymm]
    rfl
  simp only [e]
  exact h1.neg

theorem tendsto_Icc_atTop : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun x => ?_)
  · exact Finset.Icc_subset_Icc (by exact_mod_cast Int.neg_le_neg (Int.ofNat_le.mpr hab))
      (Int.ofNat_le.mpr hab)
  · exact ⟨x.natAbs, by simp only [Finset.mem_Icc]; omega⟩

theorem core25 (u : PhysicalL2) (n : ℤ)
    (h19 : ∀ (m : ℤ) (lam : ℂ),
      2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice u))
        (angleIntegralDerivative m n (realSlice u)) =
        psiAt n (muSeq (realSlice u) m) (realSlice u) *
          PoissonMixed38.dirInterpolation38 (realSlice u) (muSeq (realSlice u) m) lam)
    (hbeta : HasSum (fun m : ℤ => if m = n then (0 : PotPair →L[ℂ] ℂ)
        else fderiv ℂ (beta m n) (realSlice u)) (fderiv ℂ (betaSum n) (realSlice u)))
    (lam : ℂ) :
    2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice u))
      (angleDerivative n (realSlice u)) = psiAt n lam (realSlice u) := by
  have hS : HasSum (fun m : ℤ => angleIntegralDerivative m n (realSlice u))
      (angleDerivative n (realSlice u)) := by
    have h := hbeta.add (hasSum_ite_eq n (angleDerivative n (realSlice u) -
      fderiv ℂ (betaSum n) (realSlice u)))
    convert h using 1
    · funext m
      by_cases hm : m = n
      · simp [angleIntegralDerivative, hm]
      · simp [angleIntegralDerivative, hm]
    · abel
  have hP := (hasSum_pairPoisson (fderiv ℂ (fun φ => discrim φ lam) (realSlice u)) _ _ hS).mul_left 2
  have hinj : Function.Injective (fun m : ℤ => muSeq (realSlice u) m) := (G5024 n u).2.1
  have hmu : NlsGge.Atomic.G1044S3M.mu (realSlice u) = muSeq (realSlice u) :=
    NlsGge.Atomic.G1070.mu_eq_muSeq (realSlice u)
  have hsum : Summable (fun k : ℤ => ‖muSeq (realSlice u) k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2) := by
    rw [← hmu]
    exact NlsGge.Atomic.G1044S3M.mu_summable (realSlice u)
  have hf : Differentiable ℂ (fun z : ℂ => psiAt n z (realSlice u)) := fun z =>
    ((p6PsiNumerator_entire38 n (sourceF n) (realSlice u)) z (mem_univ _)).differentiableAt
  have hI := (G5023 (fun m => muSeq (realSlice u) m) (fun z => psiAt n z (realSlice u)) lam hsum hinj hf
    (G5024 n u).1).2.1
  have hterm : ∀ m : ℤ, 2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice u))
      (angleIntegralDerivative m n (realSlice u)) =
      psiAt n (muSeq (realSlice u) m) (realSlice u) *
        cardinalProduct (fun k : ℤ => muSeq (realSlice u) k) m lam := fun m => by
    rw [h19 m lam, G5025Sup1.dirInterpolation_eq_cardinalProduct]
  have hP' : HasSum (fun m : ℤ => psiAt n (muSeq (realSlice u) m) (realSlice u) *
      cardinalProduct (fun k : ℤ => muSeq (realSlice u) k) m lam)
      (2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice u))
        (angleDerivative n (realSlice u))) := by
    simpa only [hterm] using hP
  have hT : Tendsto (fun s : Finset ℤ => ∑ m ∈ s, psiAt n (muSeq (realSlice u) m) (realSlice u) *
      cardinalProduct (fun k : ℤ => muSeq (realSlice u) k) m lam) atTop
      (𝓝 (2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice u))
        (angleDerivative n (realSlice u)))) := hP'
  have hT1 := hT.comp tendsto_Icc_atTop
  have hT2 := SummationFilter.hasSum_symmetricIcc_iff.mp hI
  exact tendsto_nhds_unique hT1 hT2

end
end G5025Sup2
end NlsGge.GKDefinitionDesign
