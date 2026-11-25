import Mathlib
import NlsGge.Atomic.G4.G4022Host
import NlsGge.Atomic.G4.G4022
import NlsGge.Atomic.G4.G4036Host
import NlsGge.Atomic.G4.G4036H2
import NlsGge.Atomic.G4.G4036H3
import NlsGge.Atomic.G4.G4027
import NlsGge.Atomic.G4.G4017
import NlsGge.Atomic.G2.G2046

/- G4-023 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G4/G4023.lean.
   Head `G4023`: design STATEMENTS/G4.md (G4-023 section; byte-identical in followup5..10 STATEMENTS; no Pro round entry
   touches G4-023), verbatim. No lexical repair needed (the head has no `lambda`).
   Route (see G4023_ROUTE.md): the Lean `regularEtaIntegral` is the algebraic primitive
   `localRootAtDirichlet * ownCorrection(mu) - constantEtaCorrection`, so the limit is proved termwise:
   (1) localRootAtDirichlet = standardRoot at mu on the non-collapsed set, analytic in phi, tends to tau - mu;
   (2) phi -> ownCorrection phi (mu phi) is continuous (landed G4036H3);
   (3) at the collapsed psi, (tau - mu) * ownCorrection psi mu = -chi psi (ODE of G4036H2 at gamma2 = 0, K(tau) = 1,
       FTC for h(z) = (z - tau) T(z) with h' = zetaDividedDifference, G4022);
   (4) constantEtaCorrection -> 0 because K(tau) - 1 = -(gamma2/4) T'(tau) = O(gamma2) (ODE at tau, T' locally bounded
       by joint analyticity of a fixed-circle Cauchy transform) while |slitPrimitive rho| <= 2|rho| + pi.
   No analytic anchor is used. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign
open NlsGge.Atomic.G4036Cauchy

namespace NlsGge.G4023Support
noncomputable section

/-- Identification of the fixed-circle Cauchy transform with the chosen-circle coefficient on the whole
overlap of the two discs (the general-point version of `g4036_identify`). -/
theorem identify_general (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (c : ℝ) (N : ℕ) (hg : IsolatingGeometry38 C R c N) (hs : IsolatingSpectral38 φ C R) :
    ∀ z ∈ ball (C n) (R n) ∩ ball (discC φ n) (discR φ n),
      ownCorrection n φ z =
        cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n) z := by
  have hgk : φ ∈ gkW := g5001_gk φ hφ
  obtain ⟨hA1, hO1⟩ := g4036_family_ode φ hgk C R c N hg hs n
    (g4036_zero_period_family n φ hφ C R c N hg hs)
  obtain ⟨hA2, hO2⟩ := ownCorrection_analytic_and_ode n φ hφ
  obtain ⟨c', N', hg', hs'⟩ := isolating_family38 φ hgk
  rw [g4036_ownCorrection_eq] at hA2 hO2 ⊢
  set T1 := cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n) with hT1
  set T2 := cauchyOwnCorr (discC φ n) (discR φ n) (normalizedZeta n φ) (standardRoot φ n) with hT2
  set I : Set ℂ := ball (C n) (R n) ∩ ball (discC φ n) (discR φ n) with hI
  have hIo : IsOpen I := isOpen_ball.inter isOpen_ball
  have hIc : IsPreconnected I :=
    ((convex_ball (C n) (R n)).inter (convex_ball (discC φ n) (discR φ n))).isPreconnected
  have heI : lamPlus φ n ∈ I :=
    ⟨((hs.1 n).1 (right_mem_segment ℝ _ _)), ((hs'.1 n).1 (right_mem_segment ℝ _ _))⟩
  have hPe : (lamPlus φ n - tauN φ n) ^ 2 - gamma2 φ n / 4 = 0 := by
    rw [tauN_value38 φ hgk n, gamma2_value38 φ hgk n]; ring
  have hS : AnalyticOnNhd ℂ (fun z => T1 z - T2 z) I :=
    (hA1.mono inter_subset_left).sub (hA2.mono inter_subset_right)
  have hode : ∀ z ∈ I, ((z - tauN φ n) ^ 2 - gamma2 φ n / 4) * deriv (fun z => T1 z - T2 z) z +
      (z - tauN φ n) * (T1 z - T2 z) = 0 := by
    intro z hz
    have d1 : DifferentiableAt ℂ T1 z := (hA1 z hz.1).differentiableAt
    have d2 : DifferentiableAt ℂ T2 z := (hA2 z hz.2).differentiableAt
    have hd : deriv (fun z => T1 z - T2 z) z = deriv T1 z - deriv T2 z :=
      (d1.hasDerivAt.sub d2.hasDerivAt).deriv
    rw [hd]
    linear_combination hO1 z hz.1 - hO2 z hz.2
  have hz0 := NlsGge.Atomic.G4036Unique.ode_unique hIc heI hIo hPe hS hode
  intro z hz
  have := hz0 z hz
  exact (sub_eq_zero.mp this).symm

/-- `K(tau) - 1 = O(gamma2)` uniformly near a point of `sourceBetaW`. -/
theorem Kminus_one_bound (n : ℤ) (ψ : PotPair) (hψ : ψ ∈ sourceBetaW) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ φ in 𝓝 ψ,
      ‖normalizedZeta n φ (tauN φ n) - 1‖ ≤ M * ‖gamma2 φ n‖ := by
  have hgk0 : ψ ∈ gkW := g5001_gk ψ hψ
  obtain ⟨ρ, hρ, c, N, hgeom, hspec⟩ :=
    fixed_family_persistence38 ψ (discC ψ) (discR ψ) (isolating_family38 ψ hgk0)
  set V : Set PotPair := Metric.ball ψ ρ ∩ sourceBetaW with hVdef
  have hVo : IsOpen V := isOpen_ball.inter sourceFamily.V_open
  have hψV : ψ ∈ V := ⟨mem_ball_self hρ, hψ⟩
  have hVS : V ⊆ sourceBetaW := inter_subset_right
  have hVs : ∀ φ ∈ V, IsolatingSpectral38 φ (discC ψ) (discR ψ) := fun φ hφ => hspec φ hφ.1
  have hr : 0 < discR ψ n := (hgeom.1 n).1
  have hJ := NlsGge.Atomic.G4036Param.joint_cauchy_analytic (E := PotPair) (D := V)
    (c := discC ψ n) (r := discR ψ n)
    (K := fun x z => normalizedZeta n x z) (w := fun x z => standardRoot x n z) hr
    (g4036_K_joint V hVS (discC ψ) (discR ψ) c N hgeom hVs n)
    (g4036_std_joint V hVS (discC ψ) (discR ψ) hVs n)
    (g4036_std_ne_sphere V hVS (discC ψ) (discR ψ) hVs n) hVo
  set F : PotPair × ℂ → ℂ := fun q => cauchyOwnCorr (discC ψ n) (discR ψ n)
      (normalizedZeta n q.1) (standardRoot q.1 n) q.2 with hF
  have htau : ∀ φ ∈ V, tauN φ n ∈ ball (discC ψ n) (discR ψ n) ∧
      tauN φ n ∈ ball (discC φ n) (discR φ n) := by
    intro φ hφ
    have hgkφ : φ ∈ gkW := g5001_gk φ (hVS hφ)
    obtain ⟨c', N', hg', hs'⟩ := isolating_family38 φ hgkφ
    have hmem := g4036_tau_mem φ hgkφ n
    exact ⟨((hVs φ hφ).1 n).1 hmem, (hs'.1 n).1 hmem⟩
  have hderiv : ∀ φ ∈ V, deriv (ownCorrection n φ) (tauN φ n) =
      fderiv ℂ F (φ, tauN φ n) ((0 : PotPair), (1 : ℂ)) := by
    intro φ hφ
    have hI := identify_general n φ (hVS hφ) (discC ψ) (discR ψ) c N hgeom (hVs φ hφ)
    have hmem := htau φ hφ
    have hnh : ball (discC ψ n) (discR ψ n) ∩ ball (discC φ n) (discR φ n) ∈ 𝓝 (tauN φ n) :=
      (isOpen_ball.inter isOpen_ball).mem_nhds hmem
    have heq : ownCorrection n φ =ᶠ[𝓝 (tauN φ n)] fun z => F (φ, z) := by
      filter_upwards [hnh] with z hz
      exact hI z hz
    rw [heq.deriv_eq]
    exact (NlsGge.G4022Support.slice_hasDerivAt (F := F) (p := (φ, tauN φ n))
      (hJ (φ, tauN φ n) ⟨hφ, hmem.1⟩)).deriv
  have hΘ : ContinuousAt
      (fun φ : PotPair => fderiv ℂ F (φ, tauN φ n) ((0 : PotPair), (1 : ℂ))) ψ := by
    have h1 := NlsGge.G4022Support.slice_deriv_analytic hJ (ψ, tauN ψ n) ⟨hψV, (htau ψ hψV).1⟩
    have h2 : AnalyticAt ℂ (fun φ : PotPair => (φ, tauN φ n)) ψ :=
      analyticAt_id.prod (tauN_analytic n ψ hgk0)
    exact (h1.comp_of_eq h2 rfl).continuousAt
  set Θψ : ℝ := ‖fderiv ℂ F (ψ, tauN ψ n) ((0 : PotPair), (1 : ℂ))‖ with hΘψ
  have hlt : Θψ < Θψ + 1 := lt_add_one _
  have hev : ∀ᶠ φ in 𝓝 ψ,
      ‖fderiv ℂ F (φ, tauN φ n) ((0 : PotPair), (1 : ℂ))‖ < Θψ + 1 :=
    hΘ.norm.eventually (gt_mem_nhds hlt)
  refine ⟨(Θψ + 1) / 4, by positivity, ?_⟩
  filter_upwards [hev, hVo.mem_nhds hψV] with φ hφev hφV
  obtain ⟨-, hode⟩ := ownCorrection_analytic_and_ode n φ (hVS hφV)
  have h := hode _ (htau φ hφV).2
  have hK : normalizedZeta n φ (tauN φ n) - 1 =
      -(gamma2 φ n / 4) * deriv (ownCorrection n φ) (tauN φ n) := by
    linear_combination (-1 : ℂ) * h
  rw [hK, hderiv φ hφV, norm_mul, norm_neg, norm_div]
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  rw [h4]
  have hn := norm_nonneg (gamma2 φ n)
  nlinarith [hφev.le, norm_nonneg (fderiv ℂ F (φ, tauN φ n) ((0 : PotPair), (1 : ℂ)))]

/-- At a collapsed point the regular numerator integral equals `-chi`. -/
theorem collapse_identity (n : ℤ) (ψ : PotPair) (hψ : ψ ∈ sourceBetaW)
    (hgap : gamma2 ψ n = 0) :
    (tauN ψ n - muSeq ψ n) * ownCorrection n ψ (muSeq ψ n) = -chi n ψ := by
  have hgk : ψ ∈ gkW := g5001_gk ψ hψ
  obtain ⟨hTa, hode⟩ := ownCorrection_analytic_and_ode n ψ hψ
  obtain ⟨c, N, hg, hs⟩ := isolating_family38 ψ hgk
  have hτB : tauN ψ n ∈ ball (discC ψ n) (discR ψ n) := (hs.1 n).1 (g4036_tau_mem ψ hgk n)
  have hμB : muSeq ψ n ∈ ball (discC ψ n) (discR ψ n) := (hs.1 n).2.1
  have hK1 : normalizedZeta n ψ (tauN ψ n) = 1 := by
    have h := hode _ hτB
    rw [hgap] at h
    linear_combination (-1 : ℂ) * h
  obtain ⟨V, hVn, -, -, hV2⟩ := G4022 n ψ hψ
  obtain ⟨hint, hana, -⟩ := hV2 ψ (mem_of_mem_nhds hVn)
  have hZc : ∀ z ∈ ball (discC ψ n) (discR ψ n),
      ContinuousAt (fun w : ℂ => zetaDividedDifference n ψ w) z := by
    intro z hz
    have h1 : ContinuousAt (fun p : PotPair × ℂ => zetaDividedDifference n p.1 p.2) (ψ, z) :=
      (hana z hz).continuousAt
    exact h1.comp (f := fun w : ℂ => (ψ, w)) (x := z) (by fun_prop)
  have hAne : ∀ z ∈ ball (discC ψ n) (discR ψ n), z ≠ tauN ψ n →
      ownCorrection n ψ z + (z - tauN ψ n) * deriv (ownCorrection n ψ) z =
        zetaDividedDifference n ψ z := by
    intro z hz hzτ
    have h := hode z hz
    rw [hgap] at h
    unfold zetaDividedDifference
    rw [if_neg hzτ, hK1]
    have hne : tauN ψ n - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzτ)
    rw [eq_div_iff hne]
    linear_combination (-1 : ℂ) * h
  have hA : ∀ z ∈ ball (discC ψ n) (discR ψ n),
      ownCorrection n ψ z + (z - tauN ψ n) * deriv (ownCorrection n ψ) z =
        zetaDividedDifference n ψ z := by
    intro z hz
    by_cases hzτ : z = tauN ψ n
    · subst hzτ
      have h1 : AnalyticAt ℂ (ownCorrection n ψ) (tauN ψ n) := hTa _ hτB
      have hcA : ContinuousAt (fun z : ℂ => ownCorrection n ψ z +
          (z - tauN ψ n) * deriv (ownCorrection n ψ) z) (tauN ψ n) :=
        h1.continuousAt.add ((continuousAt_id.sub continuousAt_const).mul h1.deriv.continuousAt)
      have hlim : Tendsto (fun z : ℂ => ownCorrection n ψ z +
          (z - tauN ψ n) * deriv (ownCorrection n ψ) z) (𝓝[≠] tauN ψ n)
          (𝓝 (ownCorrection n ψ (tauN ψ n) +
            (tauN ψ n - tauN ψ n) * deriv (ownCorrection n ψ) (tauN ψ n))) :=
        hcA.tendsto.mono_left nhdsWithin_le_nhds
      have hlim2 : Tendsto (fun w : ℂ => zetaDividedDifference n ψ w) (𝓝[≠] tauN ψ n)
          (𝓝 (zetaDividedDifference n ψ (tauN ψ n))) :=
        (hZc _ hτB).tendsto.mono_left nhdsWithin_le_nhds
      have hev : (fun z : ℂ => ownCorrection n ψ z +
          (z - tauN ψ n) * deriv (ownCorrection n ψ) z) =ᶠ[𝓝[≠] tauN ψ n]
          fun w : ℂ => zetaDividedDifference n ψ w := by
        filter_upwards [inter_mem_nhdsWithin ({tauN ψ n}ᶜ : Set ℂ) (isOpen_ball.mem_nhds hτB)]
          with z hz
        exact hAne z hz.2 hz.1
      exact tendsto_nhds_unique (hlim.congr' hev) hlim2
    · exact hAne z hz hzτ
  have hh : ∀ z ∈ ball (discC ψ n) (discR ψ n),
      HasDerivAt (fun w : ℂ => (w - tauN ψ n) * ownCorrection n ψ w)
        (zetaDividedDifference n ψ z) z := by
    intro z hz
    have hd : HasDerivAt (ownCorrection n ψ) (deriv (ownCorrection n ψ) z) z :=
      (hTa z hz).differentiableAt.hasDerivAt
    have h2 := ((hasDerivAt_id z).sub_const (tauN ψ n)).mul hd
    have e : zetaDividedDifference n ψ z =
        1 * ownCorrection n ψ z + (id z - tauN ψ n) * deriv (ownCorrection n ψ) z := by
      rw [← hA z hz]
      simp only [id_eq, one_mul]
    rw [e]
    exact h2
  have hpath : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => (tauN ψ n + (x : ℂ) * (muSeq ψ n - tauN ψ n) - tauN ψ n) *
          ownCorrection n ψ (tauN ψ n + (x : ℂ) * (muSeq ψ n - tauN ψ n)))
        (zetaDividedDifference n ψ (tauN ψ n + (s : ℂ) * (muSeq ψ n - tauN ψ n)) *
          (muSeq ψ n - tauN ψ n)) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have hlin : HasDerivAt (fun w : ℂ => tauN ψ n + w * (muSeq ψ n - tauN ψ n))
        (muSeq ψ n - tauN ψ n) (s : ℂ) := by
      simpa using ((hasDerivAt_id (s : ℂ)).mul_const (muSeq ψ n - tauN ψ n)).const_add (tauN ψ n)
    have hmem : tauN ψ n + (s : ℂ) * (muSeq ψ n - tauN ψ n) ∈ ball (discC ψ n) (discR ψ n) :=
      NlsGge.G4022Support.seg_mem (convex_ball _ _) hτB hμB hs
    have hcomp := (hh _ hmem).comp (s : ℂ) hlin
    exact hcomp.comp_ofReal
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hpath (hint.mul_const _)
  rw [intervalIntegral.integral_mul_const] at hftc
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero,
    add_sub_cancel, sub_self, sub_zero] at hftc
  unfold chi
  linear_combination hftc

/-- On the non-collapsed off-gap set the Dirichlet local root is the standard root at `mu`. -/
theorem localRoot_eq (n : ℤ) (φ : PotPair) (hφ : φ ∈ offGapSet n) (hg : gamma2 φ n ≠ 0) :
    localRootAtDirichlet n φ = standardRoot φ n (muSeq φ n) := by
  have hgk : φ ∈ gkW := g5001_gk φ hφ.1
  have hg2 : gamma2 φ n = (lamPlus φ n - lamMinus φ n) ^ 2 := gamma2_value38 φ hgk n
  have hγne : lamPlus φ n - lamMinus φ n ≠ 0 := by
    intro h; apply hg; rw [hg2, h]; ring
  have hne : ¬ (lamPlus φ n = lamMinus φ n) := fun h => hγne (sub_eq_zero.2 h)
  have hμτ : muSeq φ n - tauN φ n ≠ 0 := by
    intro h
    apply hφ.2
    have : muSeq φ n = tauN φ n := sub_eq_zero.1 h
    rw [this]
    exact g4036_tau_mem φ hgk n
  unfold localRootAtDirichlet
  rw [dif_neg hne]
  set γ := lamPlus φ n - lamMinus φ n with hγ
  have hρ : 2 * (muSeq φ n - tauN φ n) / γ ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero hμτ) hγne
  simp only [slitRoot, if_neg hρ]
  unfold standardRoot stdRoot38
  have hτμ : tauN φ n - muSeq φ n ≠ 0 := fun h => hμτ (by linear_combination -h)
  have e1 : γ / 2 * (0 - 2 * (muSeq φ n - tauN φ n) / γ) = tauN φ n - muSeq φ n := by
    field_simp
    ring
  have e2 : 1 - (4 : ℂ) / 4 / (0 - 2 * (muSeq φ n - tauN φ n) / γ) ^ 2 =
      1 - gamma2 φ n / 4 / (tauN φ n - muSeq φ n) ^ 2 := by
    rw [hg2]
    field_simp
    ring
  rw [← mul_assoc, e1, e2]

/-- Norm bound for the elementary slit primitive. -/
theorem slitPrimitive_norm_le (ρ : ℂ) : ‖slitPrimitive ρ‖ ≤ 2 * ‖ρ‖ + Real.pi := by
  have hsq : slitRoot ρ ^ 2 = ρ ^ 2 - 1 := G4027Aux.slitRoot_sq ρ
  have hwq := G4027Aux.wq ρ
  have hxne := G4027Aux.w_ne ρ
  have hsn : ‖slitRoot ρ‖ ≤ ‖ρ‖ + 1 := by
    have h1 : ‖slitRoot ρ‖ ^ 2 ≤ ‖ρ‖ ^ 2 + 1 := by
      have : ‖slitRoot ρ‖ ^ 2 = ‖ρ ^ 2 - 1‖ := by rw [← norm_pow, hsq]
      rw [this]
      calc ‖ρ ^ 2 - 1‖ ≤ ‖ρ ^ 2‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖ρ‖ ^ 2 + 1 := by rw [norm_pow, norm_one]
    by_contra h
    push_neg at h
    nlinarith [norm_nonneg (slitRoot ρ), norm_nonneg ρ]
  have hyne : -ρ + slitRoot ρ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hwq
    exact zero_ne_one hwq
  have hprod : ‖-ρ - slitRoot ρ‖ * ‖-ρ + slitRoot ρ‖ = 1 := by
    rw [← norm_mul, hwq, norm_one]
  have hxle : ‖-ρ - slitRoot ρ‖ ≤ 2 * ‖ρ‖ + 1 := by
    calc ‖-ρ - slitRoot ρ‖ ≤ ‖-ρ‖ + ‖slitRoot ρ‖ := norm_sub_le _ _
      _ ≤ 2 * ‖ρ‖ + 1 := by rw [norm_neg]; linarith
  have hyle : ‖-ρ + slitRoot ρ‖ ≤ 2 * ‖ρ‖ + 1 := by
    calc ‖-ρ + slitRoot ρ‖ ≤ ‖-ρ‖ + ‖slitRoot ρ‖ := norm_add_le _ _
      _ ≤ 2 * ‖ρ‖ + 1 := by rw [norm_neg]; linarith
  have hxpos : 0 < ‖-ρ - slitRoot ρ‖ := norm_pos_iff.2 hxne
  have hypos : 0 < ‖-ρ + slitRoot ρ‖ := norm_pos_iff.2 hyne
  have hlogsum : Real.log ‖-ρ - slitRoot ρ‖ + Real.log ‖-ρ + slitRoot ρ‖ = 0 := by
    rw [← Real.log_mul hxpos.ne' hypos.ne', hprod, Real.log_one]
  have hl1 : Real.log ‖-ρ - slitRoot ρ‖ ≤ 2 * ‖ρ‖ := by
    have := Real.log_le_sub_one_of_pos hxpos
    linarith
  have hl2 : Real.log ‖-ρ + slitRoot ρ‖ ≤ 2 * ‖ρ‖ := by
    have := Real.log_le_sub_one_of_pos hypos
    linarith
  have habs : |Real.log ‖-ρ - slitRoot ρ‖| ≤ 2 * ‖ρ‖ := by
    rw [abs_le]
    constructor <;> linarith
  unfold slitPrimitive
  calc ‖Complex.log (-ρ - slitRoot ρ)‖
      ≤ |(Complex.log (-ρ - slitRoot ρ)).re| + |(Complex.log (-ρ - slitRoot ρ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖-ρ - slitRoot ρ‖| + |Complex.arg (-ρ - slitRoot ρ)| := by
        rw [Complex.log_re, Complex.log_im]
    _ ≤ 2 * ‖ρ‖ + Real.pi := add_le_add habs (Complex.abs_arg_le_pi _)

/-- Bound for the constant correction on the non-collapsed off-gap set. -/
theorem const_bound (n : ℤ) (φ : PotPair) (hφ : φ ∈ offGapSet n) (hg : gamma2 φ n ≠ 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hK : ‖normalizedZeta n φ (tauN φ n) - 1‖ ≤ M * ‖gamma2 φ n‖) :
    ‖constantEtaCorrection n φ‖ ≤
      M * (4 * ‖muSeq φ n - tauN φ n‖ * Real.sqrt ‖gamma2 φ n‖ + Real.pi * ‖gamma2 φ n‖) := by
  have hgk : φ ∈ gkW := g5001_gk φ hφ.1
  have hg2 : gamma2 φ n = (lamPlus φ n - lamMinus φ n) ^ 2 := gamma2_value38 φ hgk n
  set γ := lamPlus φ n - lamMinus φ n with hγ
  have hγne : γ ≠ 0 := by
    intro h; apply hg; rw [hg2, h]; ring
  have hne : ¬ (lamPlus φ n = lamMinus φ n) := fun h => hγne (sub_eq_zero.2 h)
  have hnorm : ‖gamma2 φ n‖ = ‖γ‖ ^ 2 := by rw [hg2, norm_pow]
  have hsq : Real.sqrt ‖gamma2 φ n‖ = ‖γ‖ := by rw [hnorm, Real.sqrt_sq (norm_nonneg _)]
  have hconst : constantEtaCorrection n φ =
      (normalizedZeta n φ (tauN φ n) - 1) * slitPrimitive (2 * (muSeq φ n - tauN φ n) / γ) := by
    unfold constantEtaCorrection elementaryEtaIntegral elementarySlitIntegral
    rw [if_neg hne]
  have hgpos : 0 < ‖γ‖ := norm_pos_iff.2 hγne
  have hρ : ‖2 * (muSeq φ n - tauN φ n) / γ‖ = 2 * ‖muSeq φ n - tauN φ n‖ / ‖γ‖ := by
    rw [norm_div, norm_mul]; simp
  have h1 := slitPrimitive_norm_le (2 * (muSeq φ n - tauN φ n) / γ)
  rw [hρ] at h1
  rw [hconst, norm_mul, hsq, hnorm]
  rw [hnorm] at hK
  calc ‖normalizedZeta n φ (tauN φ n) - 1‖ *
        ‖slitPrimitive (2 * (muSeq φ n - tauN φ n) / γ)‖
      ≤ (M * ‖γ‖ ^ 2) * (2 * (2 * ‖muSeq φ n - tauN φ n‖ / ‖γ‖) + Real.pi) :=
        mul_le_mul hK h1 (norm_nonneg _) (by positivity)
    _ = M * (4 * ‖muSeq φ n - tauN φ n‖ * ‖γ‖ + Real.pi * ‖γ‖ ^ 2) := by
        field_simp
        ring

end
end NlsGge.G4023Support

namespace NlsGge.GKDefinitionDesign
noncomputable section

open NlsGge.G4023Support in
theorem G4023 (n : ℤ) (ψ : PotPair) (hψ : ψ ∈ offGapSet n)
    (hgap : gamma2 ψ n = 0) :
  Tendsto (regularEtaIntegral n)
    (𝓝[{φ : PotPair | φ ∈ offGapSet n ∧ gamma2 φ n ≠ 0}] ψ)
    (𝓝 (-chi n ψ)) := by
  have hψW : ψ ∈ sourceBetaW := hψ.1
  have hgk : ψ ∈ gkW := g5001_gk ψ hψW
  set S : Set PotPair := {φ : PotPair | φ ∈ offGapSet n ∧ gamma2 φ n ≠ 0} with hS
  -- analytic data at psi
  have hτa : AnalyticAt ℂ (fun φ : PotPair => tauN φ n) ψ := tauN_analytic n ψ hgk
  have hμa : AnalyticAt ℂ (fun φ : PotPair => muSeq φ n) ψ := analyticOnNhd_muSeq_complex38 n ψ hgk
  have hγa : AnalyticAt ℂ (fun φ : PotPair => gamma2 φ n) ψ := gamma2_analytic n ψ hgk
  have hμτ : tauN ψ n - muSeq ψ n ≠ 0 := by
    intro h
    apply hψ.2
    have : muSeq ψ n = tauN ψ n := by linear_combination -h
    rw [this]
    exact g4036_tau_mem ψ hgk n
  -- (1) the local root
  have hstd : AnalyticAt ℂ (fun φ : PotPair => standardRoot φ n (muSeq φ n)) ψ := by
    have hslit : 1 - (gamma2 ψ n / 4) / (tauN ψ n - muSeq ψ n) ^ 2 ∈ Complex.slitPlane := by
      rw [hgap]; simp
    exact stdRoot_analyticAt38 (τ := fun φ : PotPair => tauN φ n)
      (g2 := fun φ : PotPair => gamma2 φ n) (z := fun φ : PotPair => muSeq φ n)
      hτa hγa hμa hμτ hslit
  have hstdval : standardRoot ψ n (muSeq ψ n) = tauN ψ n - muSeq ψ n := by
    unfold standardRoot
    rw [hgap]
    exact stdRoot_degenerate38 _ _
  have L1 : Tendsto (fun φ : PotPair => localRootAtDirichlet n φ) (𝓝[S] ψ)
      (𝓝 (tauN ψ n - muSeq ψ n)) := by
    have h0 : Tendsto (fun φ : PotPair => standardRoot φ n (muSeq φ n)) (𝓝[S] ψ)
        (𝓝 (tauN ψ n - muSeq ψ n)) := by
      rw [← hstdval]
      exact hstd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with φ hφ
    exact (localRoot_eq n φ hφ.1 hφ.2).symm
  -- (2) the own correction at the Dirichlet point
  have L2 : Tendsto (fun φ : PotPair => ownCorrection n φ (muSeq φ n)) (𝓝[S] ψ)
      (𝓝 (ownCorrection n ψ (muSeq ψ n))) :=
    ((ownCorrection_at_dirichlet_analytic n ψ hψW).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  -- (4) the constant correction tends to zero
  obtain ⟨M, hM0, hMev⟩ := Kminus_one_bound n ψ hψW
  set b : PotPair → ℝ := fun φ => M * (4 * ‖muSeq φ n - tauN φ n‖ * Real.sqrt ‖gamma2 φ n‖ +
      Real.pi * ‖gamma2 φ n‖) with hb
  have hbc : ContinuousAt b ψ := by
    have h1 : ContinuousAt (fun φ : PotPair => muSeq φ n) ψ := hμa.continuousAt
    have h2 : ContinuousAt (fun φ : PotPair => tauN φ n) ψ := hτa.continuousAt
    have h3 : ContinuousAt (fun φ : PotPair => gamma2 φ n) ψ := hγa.continuousAt
    simp only [hb]
    fun_prop
  have hb0 : b ψ = 0 := by simp [hb, hgap]
  have L4 : Tendsto (fun φ : PotPair => constantEtaCorrection n φ) (𝓝[S] ψ) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (hb0 ▸ hbc.tendsto.mono_left nhdsWithin_le_nhds)
    have hev1 : ∀ᶠ φ in 𝓝[S] ψ, ‖normalizedZeta n φ (tauN φ n) - 1‖ ≤ M * ‖gamma2 φ n‖ :=
      nhdsWithin_le_nhds hMev
    filter_upwards [hev1, self_mem_nhdsWithin] with φ hφ1 hφS
    exact const_bound n φ hφS.1 hφS.2 M hM0 hφ1
  -- assembly
  have key : Tendsto (fun φ : PotPair => localRootAtDirichlet n φ * ownCorrection n φ (muSeq φ n) -
      constantEtaCorrection n φ) (𝓝[S] ψ)
      (𝓝 ((tauN ψ n - muSeq ψ n) * ownCorrection n ψ (muSeq ψ n) - 0)) :=
    (L1.mul L2).sub L4
  rw [sub_zero, collapse_identity n ψ hψW hgap] at key
  exact key

end
end NlsGge.GKDefinitionDesign
