import Mathlib
import NlsGge.Atomic.G5.G5018Sup2
import NlsGge.ThirdConsultation.G2.RootProductSq
import NlsGge.Atomic.G2.G2021
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.PoissonSpectralCommute

/- G5-018 M4 SUPPORT `G5018M4Root` (proof development, AUTHOR; not self-reviewed, not accepted). Target
   NlsGge/Atomic/G5/G5018M4Root.lean, namespace NlsGge.GKDefinitionDesign.
   Fixed-z derivative-zero lemma for rootProduct m (psi, z) along X_{Delta_lam} at an OPEN m-th gap.
   Route (a simplification of Pro's 'fixed-contour' remark; a written route note is G5018M4Root_ROUTE.md): no contour is needed,
   since rootProduct^2 * (-4)((z-tau)^2 - gamma2/4) = perChar psi z near phi (RootProductSq.rootProduct_sq_identity), and
   tauN, gamma2 (open gap) and discrim have zero differential (G5018Sup2). rootProduct <> 0 by G2_021. -/
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5018m4_rootProduct_fderiv_zero (m : ℤ) (φ : PotPair) (lam z : ℂ)
    (hφ : φ ∈ gkW) (hk : gamma2 φ m ≠ 0)
    (hdom : (φ, z) ∈ a5OmittedRootDomain38 m)
    (hQ : (z - lamMinus φ m) * (z - lamPlus φ m) ≠ 0) :
    fderiv ℂ (fun ψ : PotPair => rootProduct m (ψ, z)) φ
      (PoissonSpectral38.spectralDiscrimHamField38 φ lam) = 0 := by
  set v := PoissonSpectral38.spectralDiscrimHamField38 φ lam with hvdef
  obtain ⟨hτv, hγv⟩ := g5018s2_tauGamma_invariant φ hφ m lam hk
  have hΔ : ∀ w : ℂ, fderiv ℂ (fun ψ : PotPair => discrim ψ w) φ v = 0 := fun w =>
    PoissonSpectral38.actual_fderiv_discrim_hamField_eq_zero φ w lam
  have hAa : AnalyticAt ℂ (fun ψ : PotPair => rootProduct m (ψ, z)) φ :=
    AnalyticAt.comp (g := rootProduct m) (f := fun ψ : PotPair => (ψ, z))
      ((G2_021 m).2.1 (φ, z) hdom) (analyticAt_id.prod analyticAt_const)
  have hA0 : rootProduct m (φ, z) ≠ 0 := (G2_021 m).2.2 (φ, z) hdom
  have hτd : DifferentiableAt ℂ (fun ψ => tauN ψ m) φ := (tauN_analytic m φ hφ).differentiableAt
  have hγd : DifferentiableAt ℂ (fun ψ => gamma2 ψ m) φ := (gamma2_analytic m φ hφ).differentiableAt
  have hD : AnalyticAt ℂ (fun ψ : PotPair => discrim ψ z) φ :=
    analyticOnNhd_discrim_phi z φ (mem_univ _)
  set A : PotPair → ℂ := fun ψ => rootProduct m (ψ, z) with hAdef
  set Q : PotPair → ℂ := fun ψ => -4 * (z - tauN ψ m) ^ 2 + gamma2 ψ m with hQdef
  have hev : (fun ψ : PotPair => discrim ψ z * discrim ψ z - 4) =ᶠ[𝓝 φ]
      fun ψ => Q ψ * (A ψ * A ψ) := by
    have hopen : ∀ᶠ ψ in 𝓝 φ, (ψ, z) ∈ a5OmittedRootDomain38 m :=
      ((isOpen_a5OmittedRootDomain38 m).preimage
        (continuous_id.prodMk continuous_const)).mem_nhds hdom
    filter_upwards [hopen] with ψ hψ
    have h := rootProduct_sq_identity m ψ hψ.1 z hψ.2
    have h2 : perChar ψ z = discrim ψ z * discrim ψ z - 4 := by
      show discrim ψ z ^ 2 - 4 = _
      ring
    have ht := tauN_value38 ψ hψ.1 m
    have hg := gamma2_value38 ψ hψ.1 m
    rw [← h2, h]
    simp only [hQdef, ht, hg]
    ring
  have hQφ : Q φ ≠ 0 := by
    have ht := tauN_value38 φ hφ m
    have hg := gamma2_value38 φ hφ m
    have e : Q φ = -4 * ((z - lamMinus φ m) * (z - lamPlus φ m)) := by
      simp only [hQdef, ht, hg]
      ring
    rw [e]
    exact mul_ne_zero (by norm_num) hQ
  obtain ⟨LQ, hLQ, hLQv⟩ : ∃ LQ : PotPair →L[ℂ] ℂ, HasFDerivAt Q LQ φ ∧ LQ v = 0 := by
    have hτ' : HasFDerivAt (fun ψ => tauN ψ m) _ φ := hτd.hasFDerivAt
    have hγ' : HasFDerivAt (fun ψ => gamma2 ψ m) _ φ := hγd.hasFDerivAt
    have h1 := ((((hasFDerivAt_const z φ).sub hτ').pow 2).const_mul (-4 : ℂ)).add hγ'
    refine ⟨_, h1, ?_⟩
    simp
    rw [hvdef, hτv, hγv]
    ring
  have hAd : HasFDerivAt A (fderiv ℂ A φ) φ := hAa.differentiableAt.hasFDerivAt
  have hDd : HasFDerivAt (fun ψ : PotPair => discrim ψ z) (fderiv ℂ (fun ψ : PotPair => discrim ψ z) φ) φ :=
    hD.differentiableAt.hasFDerivAt
  have h1 := (hDd.mul hDd).sub_const 4
  have h2 := hLQ.mul (hAd.mul hAd)
  have h3 := (hev.hasFDerivAt_iff).mp h1
  have h4 := h3.unique h2
  have h5 := congrArg (fun L : PotPair →L[ℂ] ℂ => L v) h4
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hΔ z,
    mul_zero, add_zero, hLQv, zero_mul] at h5
  have h6 : (Q φ * (2 * A φ)) * fderiv ℂ A φ v = 0 := by
    linear_combination -h5
  have hne : Q φ * (2 * A φ) ≠ 0 := mul_ne_zero hQφ (mul_ne_zero two_ne_zero hA0)
  exact (mul_eq_zero.mp h6).resolve_left hne

end
end NlsGge.GKDefinitionDesign
