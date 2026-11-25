import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.ThirdConsultation.G2.RootProductSq
import NlsGge.Atomic.G2.G2021
import NlsGge.Atomic.G2.G2048
import NlsGge.Atomic.G2.G2075
import NlsGge.Atomic.G3.G3003
import NlsGge.Atomic.G3.G3005
import NlsGge.Atomic.G3.G3012
import NlsGge.Atomic.G3.G3013
import NlsGge.Atomic.G3.G3014
import NlsGge.Atomic.G3.G3ZetaHost
import NlsGge.ThirdConsultation.G3.G3005Support1
import NlsGge.ThirdConsultation.G3.G3005C4Support
import NlsGge.ThirdConsultation.G3.G3005C36
import NlsGge.GK38.TauGammaSpectralDerivatives
import Armstrong.Work.RawBetaActualCoefficient

/- G3-015 SUPPORT (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/ThirdConsultation/G3/G3015Support.lean, namespace NlsGge.GKDefinitionDesign.G3015Aux.
   Supporting lemmas for the G3_015 head; no head is stated here.  Route (source: GK 15.2, p. 83):
   * labels: landed G3013_main (analytic endpoint labels, packet form) shrunk to an open set inside the nonexceptional set,
     giving LocalEndpointSegmentSeparation (the Pro G3_013 head);
   * beta_coef: for m <> n the actual beta is antiDiscrim(mu) * R(mu) for an analytic coefficient R solving
     P R' + (P'/2) R = psi on the WHOLE isolating disc (rawBetaPsiCoefficientOfZeroPeriod38, X-006 closure; native, no
     REVIEW_ONLY/DRAFT import) via the landed G3005C6 chain machinery;
   * factor: psi = 2 i rootProduct * (normalizedRoot - z) * betaZeta on the disc (G2_048 off the cut, identity theorem across it);
   * segment_integral: on the segment a -> mu with the G3_014 roots, S(t) = 2 i rootProduct sqrt(t) r_omega r_seg is a continuous
     sheet with S^2 = perChar, S(0)=0, S(1)=antiDiscrim(mu); S*R is a primitive, so the improper segment integral of
     H/sqrt(t) equals beta by the fundamental theorem of calculus.
   Armstrong imports: only Armstrong.Work.RawBetaActualCoefficient (X-006 closure, decision 8c) through the landed G3005/G3003 chain. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G3015Aux
noncomputable section

/-- Labels: the landed G3-013 packet theorem, restricted to an open set inside the nonexceptional set. -/
theorem labels (m : ℤ) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceW \ (collapsedSet m ∪ endpointSet m)) :
    ∃ V : Set PotPair, ∃ a b : PotPair → ℂ,
      φ0 ∈ V ∧ LocalEndpointSegmentSeparation m V a b := by
  obtain ⟨hW, hnot⟩ := hφ0
  have hgk : φ0 ∈ gkW := sourceFamily.W_gk hW
  have hg2 : gamma2 φ0 m = gap φ0 m ^ 2 :=
    gamma2_pair_gap38 discC discR isolating_selectors_admissible38 φ0 hgk m
  have hZ : lamPlus φ0 m ≠ lamMinus φ0 m := by
    intro h
    apply hnot
    left
    refine ⟨hW, ?_⟩
    rw [hg2]
    simp [gap, h]
  have hmroot : ∀ φ : PotPair, perChar φ (lamMinus φ m) = 0 := fun φ =>
    (lamSeq_enumeration38 φ).1 (2 * m)
  have hproot : ∀ φ : PotPair, perChar φ (lamPlus φ m) = 0 := fun φ =>
    (lamSeq_enumeration38 φ).1 (2 * m + 1)
  have hpc : perChar φ0 (muSeq φ0 m) ≠ 0 := fun h => hnot (Or.inr ⟨hW, h⟩)
  have hE : muSeq φ0 m ≠ lamMinus φ0 m ∧ muSeq φ0 m ≠ lamPlus φ0 m :=
    ⟨fun h => hpc (by rw [h]; exact hmroot φ0), fun h => hpc (by rw [h]; exact hproot φ0)⟩
  obtain ⟨V0, hV0o, -, hφV0, hV0gk, ρm, ρp, hρm, hρp, hspec⟩ :=
    NlsGge.Atomic.G3013S3.G3013_main m φ0 hgk hZ hE
  -- continuity at φ0 of the two exceptional detectors
  have hcg : ContinuousAt (fun φ : PotPair => (lamPlus φ m - lamMinus φ m) ^ 2) φ0 :=
    (NlsGge.Atomic.G3012S3.gammaSq_analytic m φ0 hgk).continuousAt
  have hcp : ContinuousAt (fun φ : PotPair => perChar φ (muSeq φ m)) φ0 := by
    have : AnalyticAt ℂ (fun φ : PotPair => perChar φ (muSeq φ m)) φ0 :=
      AnalyticAt.comp (g := fun p : PotPair × ℂ => perChar p.1 p.2)
        (f := fun ψ : PotPair => (ψ, muSeq ψ m))
        (analyticOnNhd_perChar_joint38 (φ0, muSeq φ0 m) (mem_univ _))
        ((analyticAt_id (𝕜 := ℂ)).prod (analyticOnNhd_muSeq_complex38 m φ0 hgk))
    exact this.continuousAt
  have hgne : (lamPlus φ0 m - lamMinus φ0 m) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hZ)
  have h1 : ∀ᶠ φ in 𝓝 φ0, (lamPlus φ m - lamMinus φ m) ^ 2 ≠ 0 := hcg.eventually_ne hgne
  have h2 : ∀ᶠ φ in 𝓝 φ0, perChar φ (muSeq φ m) ≠ 0 := hcp.eventually_ne hpc
  have h3 : ∀ᶠ φ in 𝓝 φ0, φ ∈ sourceW := sourceFamily.W_open.mem_nhds hW
  have h4 : ∀ᶠ φ in 𝓝 φ0, φ ∈ V0 := hV0o.mem_nhds hφV0
  obtain ⟨V, hVsub, hVo, hφV⟩ := _root_.mem_nhds_iff.1 ((h1.and (h2.and (h3.and h4))))
  refine ⟨V, ρm, ρp, hφV, hVo, ?_, (hρm.mono fun φ hφ => (hVsub hφ).2.2.2),
    (hρp.mono fun φ hφ => (hVsub hφ).2.2.2), ?_⟩
  · intro φ hφ
    obtain ⟨hg1, hp2, hW', -⟩ := hVsub hφ
    refine ⟨hW', ?_⟩
    rintro (⟨-, hz⟩ | ⟨-, hz⟩)
    · have hg2' : gamma2 φ m = gap φ m ^ 2 :=
        gamma2_pair_gap38 discC discR isolating_selectors_admissible38 φ (sourceFamily.W_gk hW') m
      apply hg1
      rw [← show gap φ m = lamPlus φ m - lamMinus φ m from rfl, ← hg2']
      exact hz
    · exact hp2 hz
  · intro φ hφ
    obtain ⟨-, -, -, hV0⟩ := hVsub hφ
    obtain ⟨hord, hsep⟩ := hspec φ hV0
    refine ⟨?_, ?_⟩
    · rcases hord with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, Set.pair_comm]
    · intro t ht
      have := hsep t ht
      have e : ρm φ + (t : ℂ) * (muSeq φ m - ρm φ) - ρp φ =
          -(ρp φ - ((t : ℂ) * muSeq φ m + (1 - (t : ℂ)) * ρm φ)) := by ring
      rw [e, norm_neg]
      have hgn : ‖gap φ m‖ = ‖lamPlus φ m - lamMinus φ m‖ := rfl
      rw [hgn]
      exact this

/-- The actual beta is `antiDiscrim(mu) * R(mu)` for an analytic coefficient `R` solving the ODE on the whole disc. -/
theorem beta_coef (n m : ℤ) (hmn : m ≠ n) (φ : SourcePotential) :
    ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)) ∧
      (∀ z ∈ ball (discC φ.1 m) (discR φ.1 m),
        perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z = psi n φ.1 z) ∧
      offDiagonalBeta n m φ.1 = antiDiscrim φ.1 (muSeq φ.1 m) * R (muSeq φ.1 m) := by
  have h0 : abelianPeriod38 m φ.1 (p6PsiNumerator38 n (sourceF n) φ.1) = 0 :=
    (p6PsiNumerator_integrable_and_off_diagonal_periods38 n φ.1 (sourceFamily.W_gk φ.2)
      (sourceF n) (sourceFamily.F_zero n φ.1 φ.2)).2 m (Ne.symm hmn)
  obtain ⟨R, hR, hODE⟩ := rawBetaPsiCoefficientOfZeroPeriod38 n m (sourceF n) φ.1
    (sourceFamily.W_gk φ.2) h0
  refine ⟨R, hR, hODE, ?_⟩
  obtain ⟨p, hp, -⟩ := G3005C6.offDiagonalBeta_valueSpec n m hmn φ
  have h₁ := G3005C6.chainLim_of_source n m φ p _ hp
  exact G3005C6.offdiag_of_chainLim n m sourceF (sourceGK φ) R hR
    (fun z hz => hODE z hz.1) _ _ _ _ _ (rawBetaPerCharLowerTipZero38 (sourceGK φ) m) h₁

theorem isClosed_seg (x y : ℂ) : IsClosed (segment ℝ x y) := by
  rw [segment_eq_image]
  exact (isCompact_Icc.image (by fun_prop : Continuous fun θ : ℝ => (1 - θ) • x + θ • y)).isClosed

theorem factor_off (n m : ℤ) (hmn : m ≠ n) (φ : PotPair) (hφ : φ ∈ sourceW) (z : ℂ)
    (hz : z ∈ ball (discC φ m) (discR φ m))
    (hnot : z ∉ segment ℝ (lamMinus φ m) (lamPlus φ m)) :
    psi n φ z = 2 * Complex.I * rootProduct m (φ, z) *
      ((normalizedRoot n m φ - z) * betaZeta n m φ z) := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  have hdom : (φ, z) ∈ rootDomain38 := ⟨hgk, G3005C4.not_gap φ hgk m z hz hnot⟩
  have hdom' : (φ, z) ∈ a5OmittedRootDomain38 m :=
    ⟨hgk, fun k hk => closedBall_avoids_other_gaps φ hgk m k hk z (ball_subset_closedBall hz)⟩
  obtain ⟨-, -, hsm, key⟩ := G2_048 φ hgk (p2Extend38 n (sourceF n φ)) n m hmn z hdom
  rw [← normalizedRoot_eq_sigmaOf n m φ hmn] at key
  have hrP : rootProduct m (φ, z) ≠ 0 := (G2_021 m).2.2 (φ, z) hdom'
  have hcanon : canonRoot38 φ z = 2 * Complex.I * standardRoot φ m z * rootProduct m (φ, z) := by
    have h := a5CanonRoot_omitted_factorization38 m (φ, z) hdom
    simp only at h
    rw [h]
    unfold rootFactor38 rootProduct standardRoot
    ring
  have hcne : canonRoot38 φ z ≠ 0 := by
    rw [hcanon]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hsm) hrP
  have key' : psi n φ z / canonRoot38 φ z =
      (normalizedRoot n m φ - z) / standardRoot φ m z * betaZeta n m φ z := key
  rw [div_eq_iff hcne] at key'
  rw [key', hcanon]
  field_simp

theorem exists_off_segment (φ : PotPair) (hφ : φ ∈ sourceW) (m : ℤ)
    (hγ : lamPlus φ m - lamMinus φ m ≠ 0) :
    ∃ z1 ∈ ball (discC φ m) (discR φ m), z1 ∉ segment ℝ (lamMinus φ m) (lamPlus φ m) := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  obtain ⟨c, N, hg, hspec⟩ := isolating_family38 φ hgk
  have hR : 0 < discR φ m := (hg.1 m).1
  have hz0 : discC φ m ∈ ball (discC φ m) (discR φ m) := mem_ball_self hR
  by_cases h : G3005C4.hgt (lamMinus φ m) (lamPlus φ m - lamMinus φ m) (discC φ m) = 0
  · obtain ⟨η, hη, hmem⟩ := G3005C4.exists_small (discC φ m) (Complex.I * (lamPlus φ m - lamMinus φ m))
      _ isOpen_ball hz0
    refine ⟨_, hmem, G3005C4.notseg_of_hgt hγ ?_⟩
    rw [G3005C4.hgt_add, h, mul_div_cancel_right₀ _ hγ]
    simpa using hη.ne'
  · exact ⟨_, hz0, G3005C4.notseg_of_hgt hγ h⟩

theorem factor (n m : ℤ) (hmn : m ≠ n) (φ : PotPair) (hφ : φ ∈ sourceW)
    (hγ : lamPlus φ m - lamMinus φ m ≠ 0) (z : ℂ)
    (hz : z ∈ ball (discC φ m) (discR φ m)) :
    psi n φ z = 2 * Complex.I * rootProduct m (φ, z) *
      ((normalizedRoot n m φ - z) * betaZeta n m φ z) := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  have hdomain : ∀ w ∈ ball (discC φ m) (discR φ m), (φ, w) ∈ a5OmittedRootDomain38 m :=
    fun w hw => ⟨hgk, fun k hk => closedBall_avoids_other_gaps φ hgk m k hk w (ball_subset_closedBall hw)⟩
  have hψ : AnalyticOnNhd ℂ (psi n φ) univ := (G2_075.2.2.2.2.1 n φ hφ).1
  have hζ : AnalyticOnNhd ℂ (betaZeta n m φ) (ball (discC φ m) (discR φ m)) := by
    have hC := normalizedChi_analytic_closedBall φ hφ n m hmn
    have hc : (Real.pi : ℂ) * ((n - m : ℤ) : ℂ) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
        (Int.cast_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hmn)))
    have heq : betaZeta n m φ = fun z =>
        ((Real.pi : ℂ) * ((n - m : ℤ) : ℂ))⁻¹ * normalizedChi n m φ z := by
      funext z
      simp only [betaZeta, normalizedChi]
      exact (inv_mul_cancel_left₀ hc _).symm
    rw [heq]
    intro w hw
    exact analyticAt_const.mul (hC w (ball_subset_closedBall hw))
  set E : ℂ → ℂ := fun w => psi n φ w - 2 * Complex.I * rootProduct m (φ, w) *
      ((normalizedRoot n m φ - w) * betaZeta n m φ w) with hE
  have hAn : AnalyticOnNhd ℂ E (ball (discC φ m) (discR φ m)) := by
    intro w hw
    have hrP : AnalyticAt ℂ (fun v : ℂ => rootProduct m (φ, v)) w :=
      AnalyticAt.comp (g := rootProduct m) (f := fun v : ℂ => (φ, v))
        ((G2_021 m).2.1 (φ, w) (hdomain w hw)) (analyticAt_const.prod analyticAt_id)
    exact (hψ w (mem_univ _)).sub
      ((analyticAt_const.mul hrP).mul ((analyticAt_const.sub analyticAt_id).mul (hζ w hw)))
  obtain ⟨z1, hz1, hz1n⟩ := exists_off_segment φ hφ m hγ
  have hopen : IsOpen (ball (discC φ m) (discR φ m) \ segment ℝ (lamMinus φ m) (lamPlus φ m)) :=
    isOpen_ball.sdiff (isClosed_seg _ _)
  have hev : E =ᶠ[𝓝 z1] 0 := by
    filter_upwards [hopen.mem_nhds ⟨hz1, hz1n⟩] with w hw
    simp only [hE, Pi.zero_apply]
    rw [factor_off n m hmn φ hφ w hw.1 hw.2, sub_self]
  have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hz1 hev hz
  simp only [hE, Pi.zero_apply] at this
  exact sub_eq_zero.mp this

theorem integrable_of_bound (H : ℝ → ℂ) (C : ℝ) (hH : ContinuousOn H (Icc (0 : ℝ) 1))
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖H t‖ ≤ C) :
    IntervalIntegrable (fun t : ℝ => H t / (Real.sqrt t : ℂ)) volume 0 1 := by
  have hmaj : IntervalIntegrable (fun t : ℝ => C * t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul C
  refine hmaj.mono_fun' ?_ ?_
  · rw [Set.uIoc_of_le zero_le_one]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine (hH.mono Ioc_subset_Icc_self).div
      (Complex.continuous_ofReal.comp_continuousOn Real.continuous_sqrt.continuousOn) ?_
    intro t ht
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne'
  · refine (ae_restrict_iff' measurableSet_uIoc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
    show ‖H t / (Real.sqrt t : ℂ)‖ ≤ C * t ^ (-(1 / 2 : ℝ))
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, g3005_rpow_neg_half_eq ht.1,
      ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (hC t ⟨ht.1.le, ht.2⟩) hs.le

theorem segment_integral (n m : ℤ) (hmn : m ≠ n) (φ : PotPair) (hφ : φ ∈ sourceW)
    (hγ : lamPlus φ m - lamMinus φ m ≠ 0) (a b rω : ℂ) (rseg : ℝ → ℂ)
    (hab : ({a, b} : Set ℂ) = {lamMinus φ m, lamPlus φ m})
    (hω0 : rω ≠ 0) (hωsq : rω ^ 2 = muSeq φ m - a)
    (hρc : ContinuousOn rseg (Icc (0 : ℝ) 1)) (hρ0 : ∀ t ∈ Icc (0 : ℝ) 1, rseg t ≠ 0)
    (hρsq : ∀ t ∈ Icc (0 : ℝ) 1, rseg t ^ 2 = a + (t : ℂ) * (muSeq φ m - a) - b)
    (hsign : 2 * Complex.I * rootProduct m (φ, muSeq φ m) * rω * rseg 1 =
      antiDiscrim φ (muSeq φ m))
    (hint : IntervalIntegrable (fun t : ℝ =>
      ((normalizedRoot n m φ - (a + (t : ℂ) * (muSeq φ m - a))) *
        betaZeta n m φ (a + (t : ℂ) * (muSeq φ m - a)) * rω / rseg t) /
        (Real.sqrt t : ℂ)) volume 0 1) :
    offDiagonalBeta n m φ = ∫ t in (0 : ℝ)..1,
      ((normalizedRoot n m φ - (a + (t : ℂ) * (muSeq φ m - a))) *
        betaZeta n m φ (a + (t : ℂ) * (muSeq φ m - a)) * rω / rseg t) /
        (Real.sqrt t : ℂ) := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  obtain ⟨c, N, hg, hspec⟩ := isolating_family38 φ hgk
  have hmem_a : a ∈ ball (discC φ m) (discR φ m) := by
    have h : a ∈ ({lamMinus φ m, lamPlus φ m} : Set ℂ) := by rw [← hab]; simp
    rcases h with h | h
    · rw [h]; exact (hspec.1 m).1 (left_mem_segment ℝ _ _)
    · rw [h]; exact (hspec.1 m).1 (right_mem_segment ℝ _ _)
  have hmem_μ : muSeq φ m ∈ ball (discC φ m) (discR φ m) := (hspec.1 m).2.1
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ → ℂ, z = fun t : ℝ => a + (t : ℂ) * (muSeq φ m - a) := ⟨_, rfl⟩
  have hzball : ∀ t ∈ Icc (0 : ℝ) 1, z t ∈ ball (discC φ m) (discR φ m) := by
    intro t ht
    rw [hzdef]
    exact G3005C4.line_mem_ball hmem_a hmem_μ t ht
  have hzc : Continuous z := by rw [hzdef]; fun_prop
  have hz1 : z 1 = muSeq φ m := by simp [hzdef]
  have hdom : ∀ t ∈ Icc (0 : ℝ) 1, (φ, z t) ∈ a5OmittedRootDomain38 m := fun t ht =>
    ⟨hgk, fun k hk => closedBall_avoids_other_gaps φ hgk m k hk (z t)
      (ball_subset_closedBall (hzball t ht))⟩
  have hrPc : ContinuousOn (fun t : ℝ => rootProduct m (φ, z t)) (Icc (0 : ℝ) 1) := by
    intro t ht
    have h1 : ContinuousAt (rootProduct m) (φ, z t) := ((G2_021 m).2.1 _ (hdom t ht)).continuousAt
    exact (h1.comp (f := fun s : ℝ => (φ, z s))
      (continuousAt_const.prodMk hzc.continuousAt)).continuousWithinAt
  have hrP0 : ∀ t ∈ Icc (0 : ℝ) 1, rootProduct m (φ, z t) ≠ 0 := fun t ht =>
    (G2_021 m).2.2 _ (hdom t ht)
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ → ℂ, S = fun t =>
      2 * Complex.I * rootProduct m (φ, z t) * (Real.sqrt t : ℂ) * rω * rseg t := ⟨_, rfl⟩
  have hSc : ContinuousOn S (Icc (0 : ℝ) 1) := by
    rw [hSdef]
    exact ((((continuousOn_const.mul hrPc).mul
      (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn).mul
      continuousOn_const).mul hρc)
  have hSsq : ∀ t ∈ Icc (0 : ℝ) 1, S t ^ 2 = perChar φ (z t) := by
    intro t ht
    have hid := rootProduct_sq_identity m φ hgk (z t) (fun k hk =>
      closedBall_avoids_other_gaps φ hgk m k hk (z t) (ball_subset_closedBall (hzball t ht)))
    have hpair : (z t - lamMinus φ m) * (z t - lamPlus φ m) = (z t - a) * (z t - b) := by
      rcases Set.pair_eq_pair_iff.1 hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]
      · rw [← h1, ← h2]; ring
    have hs : ((Real.sqrt t : ℝ) : ℂ) ^ 2 = t := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt ht.1]
    have e : S t ^ 2 = (2 * Complex.I) ^ 2 * rootProduct m (φ, z t) ^ 2 *
        ((Real.sqrt t : ℂ) ^ 2) * rω ^ 2 * rseg t ^ 2 := by rw [hSdef]; ring
    rw [e, hs, hωsq, hρsq t ht, hid, hpair]
    have hza : z t - a = (t : ℂ) * (muSeq φ m - a) := by rw [hzdef]; ring
    have hzb : z t - b = a + (t : ℂ) * (muSeq φ m - a) - b := by rw [hzdef]
    rw [hza, hzb]
    linear_combination (4 * rootProduct m (φ, z t) ^ 2 * (t : ℂ) * (muSeq φ m - a) *
      (a + (t : ℂ) * (muSeq φ m - a) - b)) * Complex.I_sq
  have hS0 : S 0 = 0 := by rw [hSdef]; simp
  have hS1 : S 1 = antiDiscrim φ (muSeq φ m) := by
    rw [hSdef]
    simp only [hz1, Real.sqrt_one, Complex.ofReal_one, mul_one]
    exact hsign
  have hSne : ∀ t ∈ Ioc (0 : ℝ) 1, S t ≠ 0 := by
    intro t ht
    have hs : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne'
    have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    rw [hSdef]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      (hrP0 t htc)) hs) hω0 |> fun h => mul_ne_zero h (hρ0 t htc)
  obtain ⟨R, hRan, hODE, hβ⟩ := beta_coef n m hmn ⟨φ, hφ⟩
  have hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun u => S u * R (z u))
      ((psi n φ (z t) / S t) * (muSeq φ m - a)) t := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have htn : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hd : HasDerivAt z (muSeq φ m - a) t := by
      rw [hzdef]
      simpa using (((hasDerivAt_id t).ofReal_comp).mul_const (muSeq φ m - a)).const_add a
    have hsc : ContinuousAt S t := hSc.continuousAt htn
    have he : (fun u => S u ^ 2) =ᶠ[𝓝 t] perChar φ ∘ z := by
      filter_upwards [htn] with u hu
      exact hSsq u hu
    exact G3005C6.sheet_primitive_hasDerivAt hd
      ((analyticOnNhd_perChar_z φ _ (mem_univ _)).differentiableAt.hasDerivAt)
      ((hRan _ (hzball t htc)).differentiableAt.hasDerivAt) hsc (hSne t ⟨ht.1, ht.2.le⟩) he
      (hODE _ (hzball t htc))
  have hFc : ContinuousOn (fun u => S u * R (z u)) (Icc (0 : ℝ) 1) :=
    hSc.mul (hRan.continuousOn.comp hzc.continuousOn (fun t ht => hzball t ht))
  have heq : ∀ t ∈ Ioc (0 : ℝ) 1, (psi n φ (z t) / S t) * (muSeq φ m - a) =
      ((normalizedRoot n m φ - (a + (t : ℂ) * (muSeq φ m - a))) *
        betaZeta n m φ (a + (t : ℂ) * (muSeq φ m - a)) * rω / rseg t) /
        (Real.sqrt t : ℂ) := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hs : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne'
    have hf := factor n m hmn φ hφ hγ (z t) (hzball t htc)
    have hr := hrP0 t htc
    have hρ := hρ0 t htc
    have hzt : a + (t : ℂ) * (muSeq φ m - a) = z t := by rw [hzdef]
    rw [hzt, hf, hSdef, ← hωsq]
    simp only []
    field_simp
  have hint' : IntervalIntegrable (fun t : ℝ => (psi n φ (z t) / S t) * (muSeq φ m - a))
      volume 0 1 := by
    refine hint.congr_uIoo (fun t ht => ?_)
    rw [Set.uIoo_of_le zero_le_one] at ht
    exact (heq t ⟨ht.1, ht.2.le⟩).symm
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hFc hder hint'
  have hcongr : (∫ t in (0 : ℝ)..1,
      ((normalizedRoot n m φ - (a + (t : ℂ) * (muSeq φ m - a))) *
        betaZeta n m φ (a + (t : ℂ) * (muSeq φ m - a)) * rω / rseg t) /
        (Real.sqrt t : ℂ)) = ∫ t in (0 : ℝ)..1, (psi n φ (z t) / S t) * (muSeq φ m - a) :=
    intervalIntegral.integral_congr_ae' (Filter.Eventually.of_forall fun t ht => (heq t ht).symm)
      (Filter.Eventually.of_forall fun t ht => absurd ht.2 (not_le.2 (zero_lt_one.trans ht.1)))
  rw [hcongr, hFTC, hβ, hS0, hS1, hz1, zero_mul, sub_zero]

theorem gap_ne_of_mem (m : ℤ) (φ : PotPair) (hφ : φ ∈ sourceW \ (collapsedSet m ∪ endpointSet m)) :
    lamPlus φ m - lamMinus φ m ≠ 0 := by
  intro h
  apply hφ.2
  left
  refine ⟨hφ.1, ?_⟩
  have hg2 : gamma2 φ m = gap φ m ^ 2 :=
    gamma2_pair_gap38 discC discR isolating_selectors_admissible38 φ (sourceFamily.W_gk hφ.1) m
  have h' : gap φ m = 0 := h
  rw [hg2, h']
  simp

theorem seg_mem_ball (m : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) (a b : ℂ)
    (hab : ({a, b} : Set ℂ) = {lamMinus φ m, lamPlus φ m}) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    a + (t : ℂ) * (muSeq φ m - a) ∈ ball (discC φ m) (discR φ m) := by
  obtain ⟨c, N, hg, hspec⟩ := isolating_family38 φ hφ
  have hmem_a : a ∈ ball (discC φ m) (discR φ m) := by
    have h : a ∈ ({lamMinus φ m, lamPlus φ m} : Set ℂ) := by rw [← hab]; simp
    rcases h with h | h
    · rw [h]; exact (hspec.1 m).1 (left_mem_segment ℝ _ _)
    · rw [h]; exact (hspec.1 m).1 (right_mem_segment ℝ _ _)
  exact G3005C4.line_mem_ball hmem_a (hspec.1 m).2.1 t ht

theorem sep_mono (m : ℤ) {V V' : Set PotPair} {a b : PotPair → ℂ}
    (h : LocalEndpointSegmentSeparation m V a b) (hV' : IsOpen V') (hsub : V' ⊆ V) :
    LocalEndpointSegmentSeparation m V' a b := by
  obtain ⟨-, hs, ha, hb, hp⟩ := h
  exact ⟨hV', hsub.trans hs, ha.mono hsub, hb.mono hsub, fun φ hφ => hp φ (hsub hφ)⟩

theorem roots_mono (m : ℤ) {V V' : Set PotPair} {a b rω : PotPair → ℂ} {rseg : PotPair → ℝ → ℂ}
    (h : AnalyticSegmentRoots m V a b rω rseg) (hsub : V' ⊆ V) :
    AnalyticSegmentRoots m V' a b rω rseg := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1.mono hsub, fun t ht => (h2 t ht).mono hsub, h3.mono (prod_mono hsub subset_rfl),
    fun φ hφ => h4 φ (hsub hφ)⟩

end
end G3015Aux
end NlsGge.GKDefinitionDesign
