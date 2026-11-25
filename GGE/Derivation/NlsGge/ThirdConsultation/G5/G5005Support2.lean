import Mathlib
import NlsGge.Atomic.G5.G5005Host
import NlsGge.ThirdConsultation.G5.G5005Support1
import NlsGge.Atomic.G5.G5017Host
import NlsGge.ThirdConsultation.G5.G5017Support1
import NlsGge.GK38.GradTauGamma
import NlsGge.GK38.GradTauGammaKernelContinuity
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.GradFundamentalGradient
import NlsGge.Atomic.G1.G1061

/- G5-005 SUPPORT2 (proof development, AUTHOR; not self-reviewed, not accepted). Target
   NlsGge/ThirdConsultation/G5/G5005Support2.lean, namespace NlsGge.ThirdConsultation.G5005Support2.
   The three Riesz bridges  pairGradient(tau_n), pairGradient(mu_n), pairGradient(delta(., z)) = L2 class of the
   landed gradient kernels, and the two scalar-free conjuncts of G5-005:
   (1) pairGradient tau_n is square summable in pairGradientNorm (GK38 tauGamma_gradient_l2 at fixed time, integrated);
   (2) pairGradient mu_n minus (1/2)(fourierMode 1 n + fourierMode (-1) n) is square summable (G1061 Dirichlet part). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.G5005Support1

namespace NlsGge.ThirdConsultation.G5005Support2
noncomputable section

theorem pairGradient_tauN (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    pairGradient (fun ψ => tauN ψ n) φ = pairKernelL2Class38 (gradTauCont38 φ n) := by
  unfold pairGradient
  rw [(hasFDerivAt_gradTauCont38 φ hφ n).fderiv]
  exact NlsGge.ThirdConsultation.G5017Support1.pairGradientCLM_integralPairCLM38 _

theorem pairGradient_muSeq (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    pairGradient (fun ψ => muSeq ψ n) φ =
      pairKernelL2Class38 (NlsGge.GK38.PoissonDirichlet38.dirEigenKernel38 φ (muSeq φ n)) := by
  unfold pairGradient
  rw [(angleDirichlet_analytic_derivative38 φ hφ n).2.fderiv]
  have h : NlsGge.GK38.GradEigen38.bilinearGradient
      (NlsGge.GK38.GradEigen38.state φ (muSeq φ n) (![1, 1] : PairVec38)) =
      integralPairCLM38 (NlsGge.GK38.PoissonDirichlet38.dirEigenKernel38 φ (muSeq φ n))
        ⟨1, zero_le_one, le_rfl⟩ := by
    unfold NlsGge.GK38.GradEigen38.bilinearGradient NlsGge.GK38.PoissonDirichlet38.dirEigenKernel38
    rw [NlsGge.GK38.GradEigen38.integralPairCLM38_kernelSmul]
    rfl
  rw [h]
  exact NlsGge.ThirdConsultation.G5017Support1.pairGradientCLM_integralPairCLM38 _

theorem pairGradient_antiDiscrim (φ : PotPair) (z : ℂ) :
    pairGradient (fun ψ => antiDiscrim ψ z) φ = pairKernelL2Class38 (gradAntiDiscrimCont38 φ z) := by
  unfold pairGradient
  rw [(hasFDerivAt_gradAntiDiscrimCLM φ z).fderiv]
  exact NlsGge.ThirdConsultation.G5017Support1.pairGradientCLM_integralPairCLM38 _

/-- Conjunct (1) of G5-005. -/
theorem part1 (φ : PotPair) (hφ : φ ∈ gkW) :
    Memℓp (fun n : ℤ => pairGradientNorm (pairGradient (fun ψ => tauN ψ n) φ)) 2 := by
  obtain ⟨U, hU, -, -, B, -, hB⟩ := tauGamma_gradient_l2 φ hφ
  have hφU : φ ∈ U := mem_of_mem_nhds hU
  have hs : Summable (fun n : ℤ => pairGradientNorm (pairKernelL2Class38 (gradTauCont38 φ n)) ^ 2) := by
    refine summable_pgn_sq (fun n => gradTauCont38 φ n) (B := B) ∅ (fun t S _ => ?_)
    have h := (hB φ hφU t).1.1 S
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_)) h
    rw [gradTauCont38_apply φ hφ n t]
    rfl
  have e : (fun n : ℤ => pairGradientNorm (pairGradient (fun ψ => tauN ψ n) φ)) =
      fun n : ℤ => pairGradientNorm (pairKernelL2Class38 (gradTauCont38 φ n)) :=
    funext fun n => by rw [pairGradient_tauN φ hφ n]
  rw [e]
  exact memlp_of_sq_summable hs

theorem pairKernelClass_sub_smul (g h : PairKernelCont38) (c : ℂ) :
    pairKernelL2Class38 (g - c • h) = pairKernelL2Class38 g - c • pairKernelL2Class38 h := by
  have h1 := map_sub pairKernelL2CLM38 g (c • h)
  rw [map_smul] at h1
  simpa only [pairKernelL2CLM38_apply] using h1

/-- Conjunct (2) of G5-005. -/
theorem part2 (φ : PotPair) (hφ : φ ∈ gkW) :
    Memℓp (fun n : ℤ => pairGradientNorm
      (pairGradient (fun ψ => muSeq ψ n) φ -
        (1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n))) 2 := by
  obtain ⟨V, hV, N, C, hVC⟩ := NlsGge.Atomic.G1061S1.G1061_dirichlet φ
  have hφV : φ ∈ V := mem_of_mem_nhds hV
  let g : ℤ → PairKernelCont38 := fun n =>
    NlsGge.GK38.PoissonDirichlet38.dirEigenKernel38 φ (muSeq φ n) - (1 / 2 : ℂ) • fkE n
  have hfun : (fun n : ℤ => pairGradientNorm
      (pairGradient (fun ψ => muSeq ψ n) φ -
        (1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n))) =
      fun n : ℤ => pairGradientNorm (pairKernelL2Class38 (g n)) := by
    funext n
    rw [pairGradient_muSeq φ hφ n, ← class_fkE n, ← pairKernelClass_sub_smul]
  rw [hfun]
  refine memlp_of_sq_summable ?_
  refine summable_pgn_sq g (B := C) (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun t S hS => ?_)
  have hN : ∀ n ∈ S, N < n.natAbs := by
    intro n hn
    by_contra hcon
    refine hS n hn (Finset.mem_Icc.mpr ?_)
    have := Nat.not_lt.mp hcon
    omega
  obtain ⟨hs, hle⟩ := (hVC φ hφV t.1 t.2).2.2.2
  refine le_trans ?_ hle
  refine le_trans ?_ (hs.sum_le_tsum S (fun n _ => ?_))
  · refine le_of_eq (Finset.sum_congr rfl (fun n hn => ?_))
    simp only [hN n hn, ↓reduceIte]
    have e0 : g n t 0 =
        (NlsGge.GK38.GradEigen38.Q (NlsGge.GK38.GradEigen38.state φ (muSeq φ n) (![1, 1] : PairVec38)))⁻¹ *
          pairKernelExt38 (NlsGge.GK38.GradEigen38.square
            (NlsGge.GK38.GradEigen38.state φ (muSeq φ n) (![1, 1] : PairVec38))) t.1 0 -
        (1 / 2 : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I) := by
      simp only [g, ContinuousMap.sub_apply, ContinuousMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, NlsGge.GK38.PoissonDirichlet38.dirEigenKernel38]
      rw [pairKernelExt38_of_mem _ t.2]
      rfl
    have e1 : g n t 1 =
        (NlsGge.GK38.GradEigen38.Q (NlsGge.GK38.GradEigen38.state φ (muSeq φ n) (![1, 1] : PairVec38)))⁻¹ *
          pairKernelExt38 (NlsGge.GK38.GradEigen38.square
            (NlsGge.GK38.GradEigen38.state φ (muSeq φ n) (![1, 1] : PairVec38))) t.1 1 -
        (1 / 2 : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I)) := by
      simp only [g, ContinuousMap.sub_apply, ContinuousMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, NlsGge.GK38.PoissonDirichlet38.dirEigenKernel38]
      rw [pairKernelExt38_of_mem _ t.2]
      rfl
    rw [e0, e1]
  · split_ifs <;> positivity

end
end NlsGge.ThirdConsultation.G5005Support2
