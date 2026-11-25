import Mathlib
import NlsGge.Atomic.G1.G1073
import NlsGge.Atomic.G5.G5028Sup1
import NlsGge.Atomic.G5.G5028Sup2
import NlsGge.Atomic.G5.G5024

/- G5-029 SUPPORT 6 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5029Sup6.lean, namespace NlsGge.GKDefinitionDesign.G5029Sup6Aux.
   GK Lemma 18.4 (end of proof, proof development G5029_STOP.md N3): {mu_k, mu_l} = 0 and {lam_k^-, lam_l^-} = 0 at real potentials
   (lam needs interior Dirichlet points so that lamMinus is differentiable, landed G5028Sup1.lamMinus_hasFDerivAt).
   Route: same bridge as landed G5028Sup1.pairPoisson_mu_lamMinus (pairPoisson = kernelPoisson38 of the gradient kernels,
   kernelPairingTarget), then landed G1-073 (Dirichlet clause: g5018dir_simple; periodic clause: G5028Sup2.lower_endpoint_simple).
   Also: joint continuity of (phi, z) |-> psiAt m z phi at real points (p6PsiNumerator_joint_analytic38, as landed G5035Sup1.analyticAt_psiAt). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38

namespace NlsGge.GKDefinitionDesign
namespace G5029Sup6Aux
noncomputable section

theorem fderiv_mu_eq (v : PhysicalL2) (l : ℤ) :
    fderiv ℂ (fun ψ : PotPair => muSeq ψ l) (realSlice v) =
      integralPairCLM38 (dirEigenKernel38 (realSlice v) (muSeq (realSlice v) l)) t1 :=
  ContinuousLinearMap.ext (g5018dir_fderiv_mu v l)

theorem hamField_mu (v : PhysicalL2) (l : ℤ) :
    pairHamiltonianField (fun ψ : PotPair => muSeq ψ l) (realSlice v) =
      kernelHamField38 (dirEigenKernel38 (realSlice v) (muSeq (realSlice v) l)) := by
  have hg : pairGradient (fun ψ : PotPair => muSeq ψ l) (realSlice v) =
      pairKernelL2Class38 (dirEigenKernel38 (realSlice v) (muSeq (realSlice v) l)) := by
    unfold pairGradient
    rw [fderiv_mu_eq]
    exact NlsGge.ThirdConsultation.G5017Support1.pairGradientCLM_integralPairCLM38 _
  unfold pairHamiltonianField
  rw [hg]
  rfl

theorem hamField_lam (v : PhysicalL2) (l : ℤ) (hl : InteriorRealDirichletGap l v) :
    pairHamiltonianField (fun ψ : PotPair => lamMinus ψ l) (realSlice v) =
      kernelHamField38 (periodicKernel38 (realSlice v) (lamMinus (realSlice v) l)) := by
  have hg : pairGradient (fun ψ : PotPair => lamMinus ψ l) (realSlice v) =
      pairKernelL2Class38 (periodicKernel38 (realSlice v) (lamMinus (realSlice v) l)) := by
    unfold pairGradient
    rw [(NlsGge.Atomic.G5028.lamMinus_hasFDerivAt v l hl).fderiv, ← periodic_kernel_CLM38]
    exact NlsGge.ThirdConsultation.G5017Support1.pairGradientCLM_integralPairCLM38 _
  unfold pairHamiltonianField
  rw [hg]
  rfl

theorem pairPoisson_mu_mu (v : PhysicalL2) (k l : ℤ) :
    pairPoisson (fun ψ : PotPair => muSeq ψ k) (fun ψ : PotPair => muSeq ψ l) (realSlice v) = 0 := by
  unfold pairPoisson
  rw [hamField_mu, fderiv_mu_eq, (kernelPairingTarget _ _).2.2]
  have hk := g5018dir_simple v k
  have hl := g5018dir_simple v l
  exact ((G1_073 (realSlice v)).1 _ _ ⟨hk.1, hk.2⟩ ⟨hl.1, hl.2⟩).2.2

theorem pairPoisson_lam_lam (v : PhysicalL2) (k l : ℤ)
    (hk : InteriorRealDirichletGap k v) (hl : InteriorRealDirichletGap l v) :
    pairPoisson (fun ψ : PotPair => lamMinus ψ k) (fun ψ : PotPair => lamMinus ψ l) (realSlice v) = 0 := by
  unfold pairPoisson
  rw [hamField_lam v l hl, (NlsGge.Atomic.G5028.lamMinus_hasFDerivAt v k hk).fderiv, ← periodic_kernel_CLM38,
    (kernelPairingTarget _ _).2.2]
  have sk := NlsGge.Atomic.G5028.lower_endpoint_simple v k
    (NlsGge.Atomic.G5028.gamma2_ne_zero_of_lt v k (lt_trans hk.1 hk.2))
  have sl := NlsGge.Atomic.G5028.lower_endpoint_simple v l
    (NlsGge.Atomic.G5028.gamma2_ne_zero_of_lt v l (lt_trans hl.1 hl.2))
  exact ((G1_073 (realSlice v)).2 _ _ ⟨sk.2.1, sk.2.2⟩ ⟨sl.2.1, sl.2.2⟩).2.2


theorem psiAt_continuousAt (m : ℤ) (u : PhysicalL2) (z : ℂ) :
    ContinuousAt (fun q : PotPair × ℂ => psiAt m q.2 q.1) (realSlice u, z) := by
  have hB : realSlice u ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u)
  exact (p6PsiNumerator_joint_analytic38 m sourceW (sourceF m) (sourceFamily.F_analytic m)
    (realSlice u, z) ⟨sourceFamily.V_W hB, Set.mem_univ _⟩).continuousAt
end
end G5029Sup6Aux
end NlsGge.GKDefinitionDesign
