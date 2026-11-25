import Mathlib
import NlsGge.Atomic.G5.G5023
import NlsGge.Atomic.G1.G1070
import NlsGge.GK38.DirichletRealDerivative
import NlsGge.GK38.DirichletRealReality

                                                                                       
                                                                                         
                                                                                                                              
                                                                                                  
                                                                                                                              
                                                                                                                                    
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38
open NlsGge.Atomic.G1070

namespace NlsGge.GKDefinitionDesign
namespace G5025Sup1
noncomputable section

theorem dirInterpolation_eq_cardinalProduct (u : PhysicalL2) (j : ℤ) (lam : ℂ) :
    PoissonMixed38.dirInterpolation38 (realSlice u) (muSeq (realSlice u) j) lam =
      cardinalProduct (fun m : ℤ => muSeq (realSlice u) m) j lam := by
  have hmu : NlsGge.Atomic.G1044S3M.mu (realSlice u) = muSeq (realSlice u) := mu_eq_muSeq (realSlice u)
  have hsd : simpleDirichlet (realSlice u) (NlsGge.Atomic.G1044S3M.mu (realSlice u) j) := by
    rw [hmu, muSeq_eq_gkMu38]
    exact ⟨gkMu_root38 u j, dirichlet_root_deriv_ne_zero38 u (gkMu u j) (gkMu_root38 u j)⟩
  have hinj : Function.Injective (fun m : ℤ => muSeq (realSlice u) m) := (G5024 0 u).2.1
  have hsum : Summable (fun k : ℤ => ‖muSeq (realSlice u) k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2) := by
    rw [← hmu]
    exact NlsGge.Atomic.G1044S3M.mu_summable (realSlice u)
  have hdecay : CircleRatioTendstoZero (fun _ : ℂ => (0 : ℂ)) Complex.sin :=
    fun ε hε => ⟨0, fun R _ z _ => by simpa using mul_nonneg hε.le (norm_nonneg (Complex.sin z))⟩
  have hmult := (G5023 (fun m => muSeq (realSlice u) m) (fun _ => 0) lam hsum hinj
    (differentiable_const 0) hdecay).1 j
  have hcard := (SummationFilter.hasProd_symmetricIcc_iff.mp hmult.hasProd)
  have hA := reducedProd_tendsto (realSlice u) j lam
  have hB := reducedProd_tendsto (realSlice u) j (NlsGge.Atomic.G1044S3M.mu (realSlice u) j)
  have hne : reducedProd (realSlice u) j (NlsGge.Atomic.G1044S3M.mu (realSlice u) j) ≠ 0 :=
    reducedProd_ne_zero_of (realSlice u) j hsd
  have hratio := hA.div hB hne
  have hfun : (fun N : ℕ => ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (if m = j then (1 : ℂ) else (muSeq (realSlice u) m - lam) / (muSeq (realSlice u) m - muSeq (realSlice u) j))) =
      fun N : ℕ =>
        (∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (if m = j then (1 : ℂ) else (NlsGge.Atomic.G1044S3M.mu (realSlice u) m - lam) / (πn m : ℂ))) /
        (∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (if m = j then (1 : ℂ) else
            (NlsGge.Atomic.G1044S3M.mu (realSlice u) m - NlsGge.Atomic.G1044S3M.mu (realSlice u) j) / (πn m : ℂ))) := by
    funext N
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun m _ => ?_
    by_cases hm : m = j
    · simp [hm]
    · simp only [hm, ite_false, hmu]
      have hπ : (πn m : ℂ) ≠ 0 := πn_ne_zero' m
      have hd : muSeq (realSlice u) m - muSeq (realSlice u) j ≠ 0 :=
        sub_ne_zero.mpr (fun h => hm (hinj h))
      rw [div_div_div_cancel_right₀ hπ]
  have hlim : cardinalProduct (fun m : ℤ => muSeq (realSlice u) m) j lam =
      reducedProd (realSlice u) j lam /
        reducedProd (realSlice u) j (NlsGge.Atomic.G1044S3M.mu (realSlice u) j) := by
    refine tendsto_nhds_unique hcard ?_
    rw [hfun]
    exact hratio
  rw [hlim, ← interp_eq_ratio (realSlice u) j hsd lam, hmu]

end
end G5025Sup1
end NlsGge.GKDefinitionDesign
