import Mathlib
import NlsGge.GK38.TauGamma
import NlsGge.GK38.PoissonSpectralCommute
import NlsGge.GK38.RealTypeMultiplicityCounting
import NlsGge.GK38.IsolatingCounting
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.PeriodicLabellingCanonical

/- G5-018 SUPPORT2 (proof development, AUTHOR; not self-reviewed, not accepted). Target
   NlsGge/Atomic/G5/G5018Sup2.lean, namespace NlsGge.GKDefinitionDesign.
   M3 of proof development/G5018_STOP.md, tau/gamma part: along X_{Delta_lam} = spectralDiscrimHamField38 phi lam the
   periodic-spectrum data tauN and gamma2 of an OPEN gap (gamma2 phi k <> 0) have zero differential.
   Route: simple periodic roots (isolating family) + a differentiable branch of the two roots of the
   analytic pair polynomial (z - tau)^2 - gamma2/4, differentiating perChar(psi, rho(psi)) = 0. -/
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5018s2_perChar_zero_lamMinus (φ : PotPair) (k : ℤ) : perChar φ (lamMinus φ k) = 0 :=
  (lamSeq_enumeration38 φ).1 (2 * k)

theorem g5018s2_perChar_zero_lamPlus (φ : PotPair) (k : ℤ) : perChar φ (lamPlus φ k) = 0 :=
  (lamSeq_enumeration38 φ).1 (2 * k + 1)

/-- A zero of order one has nonzero derivative. -/
theorem g5018s2_deriv_ne_of_order_one (f : ℂ → ℂ) (x : ℂ) (hf : AnalyticAt ℂ f x)
    (hx : f x = 0) (hord : analyticOrderAt f x = 1) : deriv f x ≠ 0 := by
  have hid := hf.analyticOrderAt_deriv_add_one
  simp only [hx, sub_zero] at hid
  rw [hord] at hid
  have hd0 : analyticOrderAt (deriv f) x = 0 := by simpa using hid
  exact (hf.deriv.analyticOrderAt_eq_zero).mp hd0

/-- At a point of `gkW` where the `k`-th gap is open, both gap edges are simple periodic roots. -/
theorem g5018s2_simple_roots (φ : PotPair) (hφ : φ ∈ gkW) (k : ℤ)
    (hgap : lamMinus φ k ≠ lamPlus φ k) :
    deriv (perChar φ) (lamMinus φ k) ≠ 0 ∧ deriv (perChar φ) (lamPlus φ k) ≠ 0 := by
  classical
  obtain ⟨C, R, hfam⟩ := exists_isolating_family38 φ hφ
  obtain ⟨c, N₀, hgeom, hspec⟩ := hfam
  obtain ⟨U, hU, N, _, hcount⟩ := prescribed_common_counting38 φ 0
  have hp := (hcount φ (mem_of_mem_nhds hU)).1
  have hms : (lamMinus φ k ::ₘ lamPlus φ k ::ₘ 0) =
      Lib.zeroMultiset (perChar φ) (ball (C k) (R k)) := (hspec.1 k).2.2.2.2.1
  have hnd : (Lib.zeroMultiset (perChar φ) (ball (C k) (R k))).Nodup := by
    rw [← hms]
    simp [hgap]
  have h1 : lamMinus φ k ∈ Lib.zeroMultiset (perChar φ) (ball (C k) (R k)) := by
    rw [← hms]; simp
  have h2 : lamPlus φ k ∈ Lib.zeroMultiset (perChar φ) (ball (C k) (R k)) := by
    rw [← hms]; simp
  exact ⟨g5018s2_deriv_ne_of_order_one _ _ (analyticOnNhd_perChar_z φ _ (mem_univ _))
      (g5018s2_perChar_zero_lamMinus φ k) (counting_nodup_order_one38 hp _ _ hnd h1),
    g5018s2_deriv_ne_of_order_one _ _ (analyticOnNhd_perChar_z φ _ (mem_univ _))
      (g5018s2_perChar_zero_lamPlus φ k) (counting_nodup_order_one38 hp _ _ hnd h2)⟩

/-- Core: a differentiable root branch of the periodic characteristic, through a simple root, has
zero differential along any direction annihilating every `discrim · z`. -/
theorem g5018s2_root_branch_deriv_zero (φ v : PotPair)
    (hv : ∀ z : ℂ, fderiv ℂ (fun ψ => NlsGge.GK38.discrim ψ z) φ v = 0)
    (ρ : PotPair → ℂ) (Tρ : PotPair →L[ℂ] ℂ) (hρ : HasFDerivAt ρ Tρ φ)
    (hroot : ∀ᶠ ψ in 𝓝 φ, perChar ψ (ρ ψ) = 0)
    (hsimple : deriv (perChar φ) (ρ φ) ≠ 0) : Tρ v = 0 := by
  set P : PotPair × ℂ → ℂ := fun p => perChar p.1 p.2 with hPdef
  have hP : HasFDerivAt P (fderiv ℂ P (φ, ρ φ)) (φ, ρ φ) :=
    ((analyticOnNhd_perChar_joint38 (φ, ρ φ) (mem_univ _)).differentiableAt).hasFDerivAt
  have hcomp : HasFDerivAt (fun ψ => (ψ, ρ ψ))
      ((ContinuousLinearMap.id ℂ PotPair).prod Tρ) φ := (hasFDerivAt_id φ).prodMk hρ
  have hg := hP.comp φ hcomp
  have hg0 : HasFDerivAt (P ∘ fun ψ => (ψ, ρ ψ)) (0 : PotPair →L[ℂ] ℂ) φ :=
    (hasFDerivAt_const (0 : ℂ) φ).congr_of_eventuallyEq
      (hroot.mono fun ψ hψ => by simpa [hPdef] using hψ)
  have hD : fderiv ℂ P (φ, ρ φ) (v, Tρ v) = 0 := by
    have := congrArg (fun T => T v) (hg.unique hg0)
    simpa using this
  -- split into the φ-part and the z-part
  have hsplit : fderiv ℂ P (φ, ρ φ) (v, Tρ v) =
      fderiv ℂ P (φ, ρ φ) (v, 0) + Tρ v * deriv (perChar φ) (ρ φ) := by
    have hz : deriv (perChar φ) (ρ φ) = fderiv ℂ P (φ, ρ φ) (0, 1) := by
      have hi : HasDerivAt (fun z : ℂ => (φ, z)) (0, 1) (ρ φ) :=
        (hasDerivAt_const (ρ φ) φ).prodMk (hasDerivAt_id (ρ φ))
      exact (hP.comp_hasDerivAt (ρ φ) hi).deriv
    have e : ((v, Tρ v) : PotPair × ℂ) = (v, 0) + (Tρ v) • ((0, 1) : PotPair × ℂ) := by
      ext <;> simp
    rw [e, map_add, map_smul, hz, smul_eq_mul]
  have hφpart : fderiv ℂ P (φ, ρ φ) (v, 0) = 0 := by
    have hc2 : HasFDerivAt (fun ψ : PotPair => (ψ, ρ φ))
        ((ContinuousLinearMap.id ℂ PotPair).prod (0 : PotPair →L[ℂ] ℂ)) φ :=
      (hasFDerivAt_id φ).prodMk (hasFDerivAt_const (ρ φ) φ)
    have h1 := hP.comp φ hc2
    have h2 : HasFDerivAt (fun ψ => P (ψ, ρ φ))
        ((2 * discrim φ (ρ φ)) • gradDiscrimCLM φ (ρ φ)) φ := by
      have := ((hasFDerivAt_discrim (ρ φ) φ).mul (hasFDerivAt_discrim (ρ φ) φ)).sub_const 4
      refine (this.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun ψ => ?_)
      · module
      · simp only [hPdef, perChar, perCharOf, Pi.mul_apply]
        ring
    have h3 := congrArg (fun T => T v) (h1.unique h2)
    have hv0 : gradDiscrimCLM φ (ρ φ) v = 0 := by
      have := hv (ρ φ)
      rwa [(hasFDerivAt_discrim (ρ φ) φ).fderiv] at this
    simpa [hv0] using h3
  rw [hφpart, zero_add] at hsplit
  rw [hsplit] at hD
  exact (mul_eq_zero.mp hD).resolve_right hsimple

/-- A differentiable square-root branch `s` of `gamma2 / 4` through the half-gap at `φ`. -/
theorem g5018s2_sqrt_branch (φ : PotPair) (hφ : φ ∈ gkW) (k : ℤ) (hk : gamma2 φ k ≠ 0) :
    ∃ s : PotPair → ℂ, DifferentiableAt ℂ s φ ∧ (∀ ψ, s ψ ^ 2 = gamma2 ψ k / 4) ∧
      s φ = (lamPlus φ k - lamMinus φ k) / 2 := by
  set s0 : ℂ := (lamPlus φ k - lamMinus φ k) / 2 with hs0
  have hs0sq : s0 ^ 2 = gamma2 φ k / 4 := by
    rw [hs0, gamma2_value38 φ hφ k]; ring
  have hγd : DifferentiableAt ℂ (fun ψ => gamma2 ψ k) φ :=
    (gamma2_analytic k φ hφ).differentiableAt
  have hq : DifferentiableAt ℂ (fun ψ => gamma2 ψ k / gamma2 φ k) φ := by
    simp only [div_eq_mul_inv]
    fun_prop
  have hslit : (fun ψ => gamma2 ψ k / gamma2 φ k) φ ∈ Complex.slitPlane := by
    simp only [div_self hk]
    exact Complex.one_mem_slitPlane
  refine ⟨fun ψ => s0 * (gamma2 ψ k / gamma2 φ k) ^ ((2 : ℂ)⁻¹), ?_, ?_, ?_⟩
  · exact (differentiableAt_const s0).mul (hq.cpow_const hslit)
  · intro ψ
    have h2 : ((gamma2 ψ k / gamma2 φ k) ^ ((2 : ℂ)⁻¹)) ^ 2 = gamma2 ψ k / gamma2 φ k :=
      Complex.cpow_ofNat_inv_pow _ 2
    rw [mul_pow, h2, hs0sq]
    field_simp
  · simp [div_self hk]

theorem g5018s2_tauGamma_invariant (φ : PotPair) (hφ : φ ∈ gkW) (k : ℤ) (lam : ℂ)
    (hk : gamma2 φ k ≠ 0) :
    fderiv ℂ (fun ψ => tauN ψ k) φ (PoissonSpectral38.spectralDiscrimHamField38 φ lam) = 0 ∧
    fderiv ℂ (fun ψ => gamma2 ψ k) φ (PoissonSpectral38.spectralDiscrimHamField38 φ lam) = 0 := by
  set v := PoissonSpectral38.spectralDiscrimHamField38 φ lam with hvdef
  have hv : ∀ z : ℂ, fderiv ℂ (fun ψ => NlsGge.GK38.discrim ψ z) φ v = 0 := fun z =>
    PoissonSpectral38.actual_fderiv_discrim_hamField_eq_zero φ z lam
  obtain ⟨s, hsd, hs2, hs0⟩ := g5018s2_sqrt_branch φ hφ k hk
  have hτd : DifferentiableAt ℂ (fun ψ => tauN ψ k) φ := (tauN_analytic k φ hφ).differentiableAt
  have hγd : DifferentiableAt ℂ (fun ψ => gamma2 ψ k) φ := (gamma2_analytic k φ hφ).differentiableAt
  have hgap : lamMinus φ k ≠ lamPlus φ k := by
    intro h
    apply hk
    rw [gamma2_value38 φ hφ k, h]; ring
  obtain ⟨hsm, hsp⟩ := g5018s2_simple_roots φ hφ k hgap
  have hnhds : ∀ᶠ ψ in 𝓝 φ, ψ ∈ gkW := isOpen_gkW.mem_nhds hφ
  -- the two branches
  have key : ∀ ε : ℂ, (ε = 1 ∨ ε = -1) →
      deriv (perChar φ) (tauN φ k + ε * s φ) ≠ 0 →
      (fderiv ℂ (fun ψ => tauN ψ k) φ + ε • fderiv ℂ s φ) v = 0 := by
    intro ε hε hsimple
    have hρ : HasFDerivAt (fun ψ => tauN ψ k + ε * s ψ)
        (fderiv ℂ (fun ψ => tauN ψ k) φ + ε • fderiv ℂ s φ) φ :=
      hτd.hasFDerivAt.add (hsd.hasFDerivAt.const_mul ε)
    refine g5018s2_root_branch_deriv_zero φ v hv _ _ hρ ?_ hsimple
    filter_upwards [hnhds] with ψ hψ
    have ht := tauN_value38 ψ hψ k
    have hg := gamma2_value38 ψ hψ k
    have hsq := hs2 ψ
    have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> ring
    have hprod : (tauN ψ k + ε * s ψ - lamMinus ψ k) * (tauN ψ k + ε * s ψ - lamPlus ψ k) = 0 := by
      rw [ht]
      rw [hg] at hsq
      have : (ε * s ψ) ^ 2 = (lamPlus ψ k - lamMinus ψ k) ^ 2 / 4 := by
        rw [mul_pow, hε2, one_mul, hsq]
      linear_combination this
    rcases mul_eq_zero.mp hprod with h | h
    · have : tauN ψ k + ε * s ψ = lamMinus ψ k := by linear_combination h
      rw [this]; exact g5018s2_perChar_zero_lamMinus ψ k
    · have : tauN ψ k + ε * s ψ = lamPlus ψ k := by linear_combination h
      rw [this]; exact g5018s2_perChar_zero_lamPlus ψ k
  have hτφ := tauN_value38 φ hφ k
  have h1 := key 1 (Or.inl rfl) (by
    have : tauN φ k + 1 * s φ = lamPlus φ k := by rw [hτφ, hs0]; ring
    rw [this]; exact hsp)
  have h2 := key (-1) (Or.inr rfl) (by
    have : tauN φ k + (-1) * s φ = lamMinus φ k := by rw [hτφ, hs0]; ring
    rw [this]; exact hsm)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at h1 h2
  have hτv : fderiv ℂ (fun ψ => tauN ψ k) φ v = 0 := by linear_combination (h1 + h2) / 2
  have hsv : fderiv ℂ s φ v = 0 := by linear_combination (h1 - h2) / 2
  refine ⟨hτv, ?_⟩
  have hfun : (fun ψ => gamma2 ψ k) = fun ψ => 4 * s ψ ^ 2 := by
    funext ψ; rw [hs2 ψ]; ring
  have hd := (hsd.hasFDerivAt.pow 2).const_mul (4 : ℂ)
  rw [hfun, hd.fderiv]
  simp [hsv]

end
end NlsGge.GKDefinitionDesign
