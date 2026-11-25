import Mathlib
import NlsGge.Atomic.G3.G3013
import NlsGge.Atomic.G5.G5018Asm
import NlsGge.Atomic.G5.G5018Dir
import NlsGge.Atomic.G5.G5017Host
import NlsGge.ThirdConsultation.G5.G5017Support1
import NlsGge.GK38.GradEigenBranch
import NlsGge.GK38.PoissonMixedPeriodicBasic
import NlsGge.GK38.GradEigenRealPeriodicLabels

                                                                           
                                                                         
                                                                                                                             
                                                                                                                             
                                                                                                                                        
                                                                                                                      
                                               
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38
open NlsGge.GKDefinitionDesign

namespace NlsGge.Atomic.G5028
noncomputable section

theorem eventually_lamMinus_eq (m : ℤ) (φ : PotPair) (A B : PotPair → ℂ)
    (hA : AnalyticAt ℂ A φ) (hB : AnalyticAt ℂ B φ)
    (hV : ∀ᶠ ψ in 𝓝 φ, (A ψ = lamMinus ψ m ∧ B ψ = lamPlus ψ m) ∨
      (A ψ = lamPlus ψ m ∧ B ψ = lamMinus ψ m))
    (hAφ : A φ = lamMinus φ m) (hBφ : B φ = lamPlus φ m)
    (hlt : (lamMinus φ m).re < (lamPlus φ m).re) :
    ∀ᶠ ψ in 𝓝 φ, lamMinus ψ m = A ψ := by
  have hre : ∀ᶠ ψ in 𝓝 φ, (A ψ).re < (B ψ).re :=
    (Complex.continuous_re.continuousAt.comp hA.continuousAt).eventually_lt
      (Complex.continuous_re.continuousAt.comp hB.continuousAt)
      (by simpa only [Function.comp_apply, hAφ, hBφ] using hlt)
  filter_upwards [hV, hre] with ψ hψ hr
  rcases hψ with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact h1.symm
  · exfalso
    have hle := lamMinus_le_lamPlus38 ψ m
    rw [← h1, ← h2] at hle
    rcases (complexLexLE_iff38 _ _).mp hle with h | h
    · linarith
    · linarith [h.1]

theorem lamMinus_branch (v : PhysicalL2) (m : ℤ) (hm : InteriorRealDirichletGap m v) :
    ∃ A : PotPair → ℂ, AnalyticAt ℂ A (realSlice v) ∧ A (realSlice v) = lamMinus (realSlice v) m ∧
      ∀ᶠ ψ in 𝓝 (realSlice v), lamMinus ψ m = A ψ := by
  have hgk : realSlice v ∈ gkW := realSlice_mem_gkW v
  obtain ⟨hP, hM⟩ := lamPlus_real v m
  have hlo := hm.1
  have hhi := hm.2
  have hlt : (lamMinus (realSlice v) m).re < (lamPlus (realSlice v) m).re := by
    rw [hP, hM, Complex.ofReal_re, Complex.ofReal_re]
    exact lt_trans hlo hhi
  have hZ : lamPlus (realSlice v) m ≠ lamMinus (realSlice v) m := by
    intro h
    rw [h] at hlt
    exact lt_irrefl _ hlt
  have hδ := g5018_antiDiscrim_ne_zero v m hm
  have hsq := dirichlet_perChar_eq_anti_sq38 (realSlice v) (muSeq (realSlice v) m)
    (muSeq_root38 (realSlice v) m)
  have hper : perChar (realSlice v) (muSeq (realSlice v) m) ≠ 0 := by
    rw [hsq]; exact pow_ne_zero 2 hδ
  have hE : muSeq (realSlice v) m ≠ lamMinus (realSlice v) m ∧
      muSeq (realSlice v) m ≠ lamPlus (realSlice v) m :=
    ⟨fun h => hper (by rw [h]; exact (lamSeq_enumeration38 (realSlice v)).1 (2 * m)),
     fun h => hper (by rw [h]; exact (lamSeq_enumeration38 (realSlice v)).1 (2 * m + 1))⟩
  obtain ⟨V, hVo, -, hφV, hVgk, ρm, ρp, hρm, hρp, hspec⟩ :=
    NlsGge.Atomic.G3013S3.G3013_main m (realSlice v) hgk hZ hE
  have hVn : V ∈ 𝓝 (realSlice v) := hVo.mem_nhds hφV
  have hev : ∀ᶠ ψ in 𝓝 (realSlice v),
      (ρm ψ = lamMinus ψ m ∧ ρp ψ = lamPlus ψ m) ∨ (ρm ψ = lamPlus ψ m ∧ ρp ψ = lamMinus ψ m) := by
    filter_upwards [hVn] with ψ hψ using (hspec ψ hψ).1
  have hAm := hρm (realSlice v) hφV
  have hAp := hρp (realSlice v) hφV
  rcases (hspec (realSlice v) hφV).1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨ρm, hAm, h1, eventually_lamMinus_eq m _ ρm ρp hAm hAp hev h1 h2 hlt⟩
  · refine ⟨ρp, hAp, h2, eventually_lamMinus_eq m _ ρp ρm hAp hAm ?_ h2 h1 hlt⟩
    filter_upwards [hev] with ψ hψ
    rcases hψ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩

theorem lamMinus_hasFDerivAt (v : PhysicalL2) (m : ℤ) (hm : InteriorRealDirichletGap m v) :
    HasFDerivAt (fun ψ : PotPair => lamMinus ψ m)
      (perImplicitGradient (realSlice v) (lamMinus (realSlice v) m)) (realSlice v) := by
  obtain ⟨A, hA, hAφ, hev⟩ := lamMinus_branch v m hm
  obtain ⟨hP, hM⟩ := lamPlus_real v m
  have hgap : actualGapLowerAllE02_38 v m < actualGapUpperAllE02_38 v m := lt_trans hm.1 hm.2
  set z : ℂ := lamMinus (realSlice v) m with hz
  have hs : deriv (perChar (realSlice v)) z ≠ 0 := by
    have h := NlsGge.GK38.GradEigen38.endpoint_perChar_deriv_ne_zero v m false hgap
    simp only [endpoint, Bool.false_eq_true, if_false] at h
    rw [hM]; exact h
  have hd : deriv (discrim (realSlice v)) z ≠ 0 := periodic_simple_discrim_nonzero _ z hs
  have hΔ : discrim (realSlice v) z ≠ 0 := by
    intro h0
    apply hs
    rw [periodic_perChar_deriv, h0]; ring
  have hpartial : (fderiv ℂ (fun p : PotPair × ℂ => perChar p.1 p.2) (realSlice v, z)) (0, 1) ≠ 0 := by
    rw [periodic_joint_spectral_partial]; exact hs
  have hf : AnalyticAt ℂ (fun p : PotPair × ℂ => perChar p.1 p.2) (realSlice v, z) :=
    ((analyticOnNhd_discrim.pow 2).sub analyticOnNhd_const) (realSlice v, z) (mem_univ _)
  have hroot : ∀ᶠ ψ in 𝓝 (realSlice v), (fun p : PotPair × ℂ => perChar p.1 p.2) (ψ, A ψ) = 0 := by
    filter_upwards [hev] with ψ h
    change perChar ψ (A ψ) = 0
    rw [← h]
    exact (lamSeq_enumeration38 ψ).1 (2 * m)
  have hder := complex_root_derivative (fun p : PotPair × ℂ => perChar p.1 p.2) (realSlice v) z
    hf hpartial A hA hAφ hroot
  have hinv : -((2 * discrim (realSlice v) z) * deriv (discrim (realSlice v)) z)⁻¹ *
      (2 * discrim (realSlice v) z) = -(deriv (discrim (realSlice v)) z)⁻¹ := by
    field_simp [hΔ, hd]
  rw [periodic_joint_potential_partial, periodic_joint_spectral_partial,
    periodic_perChar_deriv, smul_smul, hinv] at hder
  change HasFDerivAt A (perImplicitGradient (realSlice v) z) (realSlice v) at hder
  exact hder.congr_of_eventuallyEq hev

theorem pairPoisson_mu_lamMinus (v : PhysicalL2) (k m : ℤ) (hm : InteriorRealDirichletGap m v) :
    pairPoisson (fun ψ : PotPair => muSeq ψ k) (fun ψ : PotPair => lamMinus ψ m) (realSlice v) =
      kernelPoisson38 (dirEigenKernel38 (realSlice v) (muSeq (realSlice v) k))
        (periodicKernel38 (realSlice v) (lamMinus (realSlice v) m)) := by
  have hg : pairGradient (fun ψ : PotPair => lamMinus ψ m) (realSlice v) =
      pairKernelL2Class38 (periodicKernel38 (realSlice v) (lamMinus (realSlice v) m)) := by
    unfold pairGradient
    rw [(lamMinus_hasFDerivAt v m hm).fderiv, ← periodic_kernel_CLM38]
    exact NlsGge.ThirdConsultation.G5017Support1.pairGradientCLM_integralPairCLM38 _
  have hH : pairHamiltonianField (fun ψ : PotPair => lamMinus ψ m) (realSlice v) =
      kernelHamField38 (periodicKernel38 (realSlice v) (lamMinus (realSlice v) m)) := by
    unfold pairHamiltonianField
    rw [hg]
    rfl
  unfold pairPoisson
  rw [hH, g5018dir_fderiv_mu]
  exact (kernelPairingTarget _ _).2.2

end
end NlsGge.Atomic.G5028
