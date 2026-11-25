import Mathlib
import NlsGge.Atomic.G1.G1071
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.DirichletRealDerivative
import NlsGge.GK38.GradEigenNorming
import NlsGge.GK38.PoissonMixedKernelAlgebra
import NlsGge.GK38.PoissonMixedPairing
import NlsGge.GK38.PoissonSpectralModel
import NlsGge.Atomic.G5.G5001Host

                                                                                  
                                                                              
                                                                                                                                   
                                                                                             
                                                                                                                              
                                                                                                                     
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5018dir_simple (u : PhysicalL2) (m : ℤ) :
    NlsGge.Atomic.G1070.simpleDirichlet (realSlice u) (muSeq (realSlice u) m) := by
  have ha := analyticOnNhd_dirichletChar_z (realSlice u) (muSeq (realSlice u) m) (mem_univ _)
  have h := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ha (n := 1)).mp
    (muSeq_simple38 u m)
  refine ⟨muSeq_root38 _ m, ?_⟩
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h.2

theorem g5018dir_fderiv_mu (u : PhysicalL2) (m : ℤ) (v : PotPair) :
    fderiv ℂ (fun ψ : PotPair => muSeq ψ m) (realSlice u) v =
      integralPairCLM38 (PoissonDirichlet38.dirEigenKernel38 (realSlice u) (muSeq (realSlice u) m)) GradEigen38.t1 v := by
  have hd := (angleDirichlet_analytic_derivative38 (realSlice u) (realSlice_mem_gkW u) m).2
  rw [hd.fderiv]
  unfold GradEigen38.bilinearGradient PoissonDirichlet38.dirEigenKernel38
  rw [GradEigen38.integralPairCLM38_kernelSmul]

theorem g5018_dirichlet_fderiv_hamField
    (u : PhysicalL2) (m : ℤ) (lam : ℂ)
    (hm : InteriorRealDirichletGap m u) :
    2 * fderiv ℂ (fun ψ : PotPair => muSeq ψ m) (realSlice u)
      (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam) =
    -(antiDiscrim (realSlice u) (muSeq (realSlice u) m) *
      PoissonMixed38.dirInterpolation38 (realSlice u)
        (muSeq (realSlice u) m) lam) := by
  have hs := g5018dir_simple u m
  have hH : PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam =
      PoissonMixed38.kernelHamField38 (gradDiscrimCont38 (realSlice u) lam) := rfl
  rw [g5018dir_fderiv_mu, hH]
  rw [(PoissonMixed38.kernelPairingTarget _ _).2.2,
    PoissonMixed38.kernelPoisson_swap38 (gradDiscrimCont38 (realSlice u) lam)
      (PoissonDirichlet38.dirEigenKernel38 (realSlice u) (muSeq (realSlice u) m))]
  have h := (G1_071 (realSlice u) m lam hs).2
  linear_combination -h

end
end NlsGge.GKDefinitionDesign
