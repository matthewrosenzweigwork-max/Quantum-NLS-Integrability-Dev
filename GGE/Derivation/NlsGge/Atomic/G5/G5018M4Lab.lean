import Mathlib
import NlsGge.Atomic.G5.G5018Sup2

/- G5-018 M4 SUPPORT `G5018M4Lab` (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/G5/G5018M4Lab.lean.
   Differentiable endpoint labels a, b with {a,b} = {lamMinus, lamPlus} near phi, at an open gap, have zero differential along
   X_{Delta_lam}: a + b = 2 tau and (a-b)^2 = gamma2 near phi, and tau, gamma2 are invariant (G5018Sup2).  This replaces the
   Sup3 'lamMinus/lamPlus' route (no local identification of the label with one edge is needed). -/
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5018m4_labels_fderiv_zero (m : ℤ) (φ : PotPair) (lam : ℂ) (a b : PotPair → ℂ)
    (hφ : φ ∈ gkW) (hk : gamma2 φ m ≠ 0)
    (ha : DifferentiableAt ℂ a φ) (hb : DifferentiableAt ℂ b φ)
    (hab : ∀ᶠ ψ in 𝓝 φ, ({a ψ, b ψ} : Set ℂ) = {lamMinus ψ m, lamPlus ψ m})
    (hne : ∀ᶠ ψ in 𝓝 φ, lamPlus ψ m - lamMinus ψ m ≠ 0) :
    fderiv ℂ a φ (PoissonSpectral38.spectralDiscrimHamField38 φ lam) = 0 ∧
    fderiv ℂ b φ (PoissonSpectral38.spectralDiscrimHamField38 φ lam) = 0 := by
  obtain ⟨hτv, hγv⟩ := g5018s2_tauGamma_invariant φ hφ m lam hk
  set v := PoissonSpectral38.spectralDiscrimHamField38 φ lam with hvdef
  have hgk : ∀ᶠ ψ in 𝓝 φ, ψ ∈ gkW := isOpen_gkW.mem_nhds hφ
  have hev : ∀ᶠ ψ in 𝓝 φ, a ψ + b ψ = 2 * tauN ψ m ∧ (a ψ - b ψ) ^ 2 = gamma2 ψ m := by
    filter_upwards [hab, hne, hgk] with ψ h1 h2 h3
    have ht := tauN_value38 ψ h3 m
    have hg := gamma2_value38 ψ h3 m
    rcases Set.pair_eq_pair_iff.1 h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2, ht, hg]; constructor <;> ring
    · rw [e1, e2, ht, hg]; constructor <;> ring
  have hτd : DifferentiableAt ℂ (fun ψ => tauN ψ m) φ := (tauN_analytic m φ hφ).differentiableAt
  have hγd : DifferentiableAt ℂ (fun ψ => gamma2 ψ m) φ := (gamma2_analytic m φ hφ).differentiableAt
  have hsum : fderiv ℂ a φ v + fderiv ℂ b φ v = 0 := by
    have h1 := ha.hasFDerivAt.add hb.hasFDerivAt
    have h2 := hτd.hasFDerivAt.const_mul (2 : ℂ)
    have e1 : (fun ψ => a ψ + b ψ) =ᶠ[𝓝 φ] fun ψ => 2 * tauN ψ m := hev.mono fun ψ h => h.1
    have h3 := (e1.hasFDerivAt_iff).mp h1
    have h4 := congrArg (fun L : PotPair →L[ℂ] ℂ => L v) (h3.unique h2)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at h4
    rw [h4]
    have : (fderiv ℂ (fun ψ => tauN ψ m) φ) v = 0 := hτv
    rw [this, mul_zero]
  have hdiff : fderiv ℂ a φ v - fderiv ℂ b φ v = 0 := by
    have h1 := (ha.hasFDerivAt.sub hb.hasFDerivAt).pow 2
    have e2 : (fun ψ => (a ψ - b ψ) ^ 2) =ᶠ[𝓝 φ] fun ψ => gamma2 ψ m := hev.mono fun ψ h => h.2
    have h3 := (e2.hasFDerivAt_iff).mp h1
    have h4 := congrArg (fun L : PotPair →L[ℂ] ℂ => L v) (h3.unique hγd.hasFDerivAt)
    have hg0 : (fderiv ℂ (fun ψ => gamma2 ψ m) φ) v = 0 := hγv
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.sub_apply] at h4
    rw [hg0] at h4
    have hab0 : a φ - b φ ≠ 0 := by
      intro h
      apply hk
      have := (hev.self_of_nhds).2
      rw [h] at this
      rw [← this]; ring
    have h5 : (2 * (a φ - b φ)) * (fderiv ℂ a φ v - fderiv ℂ b φ v) = 0 := by
      simp only [Pi.sub_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat, nsmul_eq_mul] at h4
      linear_combination h4
    exact (mul_eq_zero.mp h5).resolve_left (mul_ne_zero two_ne_zero hab0)
  constructor
  · linear_combination (1 / 2 : ℂ) * hsum + (1 / 2 : ℂ) * hdiff
  · linear_combination (1 / 2 : ℂ) * hsum - (1 / 2 : ℂ) * hdiff
end
end NlsGge.GKDefinitionDesign
