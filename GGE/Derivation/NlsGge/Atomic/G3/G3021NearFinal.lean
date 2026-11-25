import Mathlib
import NlsGge.Atomic.G2.G2019
import NlsGge.Atomic.G2.G2022
import NlsGge.Atomic.G3.G3SegmentHost
import NlsGge.ThirdConsultation.G3.G3M12Support
import NlsGge.ThirdConsultation.G3.G3S1Support
import NlsGge.ThirdConsultation.G3.G3S23Support
import NlsGge.ThirdConsultation.G3.G3S4Support
import NlsGge.Atomic.G3.G3021NearBase
import NlsGge.Atomic.G3.G3021NearUnif

/- G3-021 supporting module NEARFINAL (proof development, AUTHOR; not self-reviewed; NOT the G3_021 head).
   Target NlsGge/Atomic/G3/G3021NearFinal.lean, namespace NlsGge.GKDefinitionDesign.
   Generic forms of landed G3S23 (eventual integrability on [eps,1]) and G3S4 (convergence of the final segment integral) for the
   segment from the NEARER endpoint.  Proofs are the landed proofs with betaSegmentPoint/betaOmega/betaRootRatioAlong/
   betaSegmentDensity replaced by nearSegPoint/nearOmega/nearRatio/nearDensity; G3_019 is replaced by near_key (same estimate,
   with gap := far - near).  The base-point-free landed lemmas g3s3_integrable, g3s2_betaZeta_contOn (at the collapsed limit,
   whose lower segment is the tau-segment), g3s1_norm_*, g3s4_bound are reused unchanged. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem near_zeta_contAt (n m : ℤ) (hmn : m ≠ n) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (ψ : PotPair) (hψ : ψ ∈ gkW)
    (hspec : IsolatingSpectral38 ψ C R) (t0 : ℝ) (ht0 : t0 ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun t : ℝ => betaZeta n m ψ (nearSegPoint m ψ t)) t0 := by
  have hw0 : nearSegPoint m ψ t0 ∈ ball (C m) (R m) := G3021N.seg_mem m ψ hspec t0 ht0
  have hZ : Continuous (fun t : ℝ => nearSegPoint m ψ t) := G3021N.seg_continuous m ψ
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = nearSegPoint m ψ t0 + 1 := ⟨_, rfl⟩
  have hdom : ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), nearSegPoint m ψ t0) ∈
      {p : (PotPair × Lib.L2Seq) × ℂ | (p.1.1, p.2) ∈ a5OmittedRootDomain38 m} :=
    g3m2_dom n m hmn C R c N hg ψ hψ hspec _ hw0
  have hAn : ContinuousAt (p2OmittedRatio38 m)
      ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), nearSegPoint m ψ t0) :=
    ((G2_022 m).1 _ hdom).continuousAt
  have hP : ContinuousAt (fun t : ℝ =>
      ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), nearSegPoint m ψ t)) t0 :=
    ContinuousAt.prodMk (ContinuousAt.prodMk continuousAt_const continuousAt_const) hZ.continuousAt
  have hR : ContinuousAt (fun t : ℝ => p2OmittedRatio38 m
      ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), nearSegPoint m ψ t)) t0 :=
    ContinuousAt.comp (g := p2OmittedRatio38 m)
      (f := fun t : ℝ => ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), nearSegPoint m ψ t))
      (x := t0) hAn hP
  have hden : ContinuousAt (fun t : ℝ => a - nearSegPoint m ψ t) t0 :=
    continuousAt_const.sub hZ.continuousAt
  have hne : a - nearSegPoint m ψ t0 ≠ 0 := by
    rw [ha]
    simp
  have hF : ContinuousAt (fun t : ℝ => Complex.I * p2OmittedRatio38 m
      ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), nearSegPoint m ψ t) /
      (a - nearSegPoint m ψ t)) t0 :=
    (ContinuousAt.mul continuousAt_const hR).div hden hne
  have hev : (fun t : ℝ => betaZeta n m ψ (nearSegPoint m ψ t)) =ᶠ[𝓝 t0]
      (fun t : ℝ => Complex.I * p2OmittedRatio38 m
        ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), nearSegPoint m ψ t) /
        (a - nearSegPoint m ψ t)) := by
    have hball : ∀ᶠ t in 𝓝 t0, nearSegPoint m ψ t ∈ ball (C m) (R m) :=
      hZ.continuousAt.eventually_mem (isOpen_ball.mem_nhds hw0)
    have hne' : ∀ᶠ t in 𝓝 t0, a - nearSegPoint m ψ t ≠ 0 := hden.eventually_ne hne
    filter_upwards [hball, hne'] with t ht1 ht2
    exact g3m2_identity n m hmn C R c N hg ψ hψ hspec a _ ht1 ht2
  exact hF.congr_of_eventuallyEq hev

theorem near_zeta_contOn (n m : ℤ) (hmn : m ≠ n) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (ψ : PotPair) (hψ : ψ ∈ gkW)
    (hspec : IsolatingSpectral38 ψ C R) (ε : ℝ) (hε : 0 < ε) :
    ContinuousOn (fun t : ℝ => betaZeta n m ψ (nearSegPoint m ψ t)) (Icc ε 1) :=
  fun t ht => (near_zeta_contAt n m hmn C R c N hg ψ hψ hspec t
    ⟨by linarith [ht.1], ht.2⟩).continuousWithinAt

theorem near_key (m : ℤ) (ψ : PotPair) (hψ : ψ ∈ sourceW) (ε : ℝ) (hε : 0 < ε)
    (hω : nearOmega m ψ ≠ 0) (hratio : ‖gap ψ m / nearOmega m ψ‖ ≤ ε / 2) (t : ℝ)
    (ht : t ∈ Icc ε 1) :
    tauN ψ m - nearSegPoint m ψ t ≠ 0 ∧
    (1 - gap ψ m ^ 2 / (4 * (tauN ψ m - nearSegPoint m ψ t) ^ 2)) ∈ Complex.slitPlane ∧
    standardRoot ψ m (nearSegPoint m ψ t) =
      (tauN ψ m - nearSegPoint m ψ t) *
        Complex.sqrt (1 - gap ψ m ^ 2 / (4 * (tauN ψ m - nearSegPoint m ψ t) ^ 2)) := by
  have hgk : ψ ∈ gkW := sourceFamily.W_gk hψ
  have h1 := G3021N.tauN_eq_near_far m ψ hgk
  have h2 : gamma2 ψ m = gap ψ m ^ 2 := gamma2_value38 ψ hgk m
  have hγn : ‖farEnd m ψ - nearEnd m ψ‖ = ‖gap ψ m‖ := G3021N.norm_far_sub_near m ψ
  have hdeq : tauN ψ m - nearSegPoint m ψ t =
      (farEnd m ψ - nearEnd m ψ) / 2 - (t : ℂ) * nearOmega m ψ := by
    unfold nearSegPoint
    rw [h1]
    ring
  have hωn : 0 < ‖nearOmega m ψ‖ := norm_pos_iff.2 hω
  have hγle : ‖gap ψ m‖ ≤ ε * ‖nearOmega m ψ‖ / 2 := by
    rw [norm_div, div_le_iff₀ hωn] at hratio
    nlinarith
  have hpos : 0 < t := lt_of_lt_of_le hε ht.1
  have htω : ‖(t : ℂ) * nearOmega m ψ‖ = t * ‖nearOmega m ψ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  have hlow : 3 * ε * ‖nearOmega m ψ‖ / 4 ≤ ‖tauN ψ m - nearSegPoint m ψ t‖ := by
    have h3 : ‖(t : ℂ) * nearOmega m ψ‖ ≤
        ‖(farEnd m ψ - nearEnd m ψ) / 2‖ + ‖tauN ψ m - nearSegPoint m ψ t‖ := by
      have : (t : ℂ) * nearOmega m ψ =
          (farEnd m ψ - nearEnd m ψ) / 2 - (tauN ψ m - nearSegPoint m ψ t) := by
        rw [hdeq]; ring
      rw [this]
      exact norm_sub_le _ _
    have h4 : ‖(farEnd m ψ - nearEnd m ψ) / 2‖ = ‖gap ψ m‖ / 2 := by
      rw [norm_div, hγn]; simp
    have h5 : ε * ‖nearOmega m ψ‖ ≤ t * ‖nearOmega m ψ‖ :=
      mul_le_mul_of_nonneg_right ht.1 hωn.le
    rw [htω, h4] at h3
    linarith
  have hεω : 0 < ε * ‖nearOmega m ψ‖ := mul_pos hε hωn
  have hdn : 0 < ‖tauN ψ m - nearSegPoint m ψ t‖ := by linarith
  have hdz : tauN ψ m - nearSegPoint m ψ t ≠ 0 := norm_pos_iff.1 hdn
  have hr13 : ‖gap ψ m / (2 * (tauN ψ m - nearSegPoint m ψ t))‖ ≤ 1 / 3 := by
    have h2n : ‖(2 : ℂ)‖ = 2 := by simp
    rw [norm_div, norm_mul, h2n, div_le_iff₀ (mul_pos two_pos hdn)]
    nlinarith
  refine ⟨hdz, ?_, ?_⟩
  · have hsq : gap ψ m ^ 2 / (4 * (tauN ψ m - nearSegPoint m ψ t) ^ 2) =
        (gap ψ m / (2 * (tauN ψ m - nearSegPoint m ψ t))) ^ 2 := by
      rw [div_pow, mul_pow]
      norm_num
    rw [hsq]
    generalize gap ψ m / (2 * (tauN ψ m - nearSegPoint m ψ t)) = w at hr13 ⊢
    have hw2 : ‖w ^ 2‖ ≤ 1 / 9 := by
      rw [norm_pow]
      have h0 := norm_nonneg w
      nlinarith
    have hre : 0 < (1 - w ^ 2).re := by
      have h1 : (w ^ 2).re ≤ ‖w ^ 2‖ := Complex.re_le_norm _
      rw [Complex.sub_re, Complex.one_re]
      linarith
    exact Complex.mem_slitPlane_iff.2 (Or.inl hre)
  · unfold standardRoot stdRoot38
    rw [h2, div_div]

theorem near_ratio_contOn (n m : ℤ) (ψ : PotPair) (hψ : ψ ∈ sourceW) (ε : ℝ) (hε : 0 < ε)
    (hω : nearOmega m ψ ≠ 0) (hratio : ‖gap ψ m / nearOmega m ψ‖ ≤ ε / 2) :
    ContinuousOn (fun t : ℝ => nearRatio n m ψ t) (Icc ε 1) := by
  have hZ : Continuous (fun t : ℝ => nearSegPoint m ψ t) := G3021N.seg_continuous m ψ
  have hDcont : ContinuousOn (fun t : ℝ => standardRoot ψ m (nearSegPoint m ψ t)) (Icc ε 1) := by
    intro t0 ht0
    obtain ⟨hd0, hslit0, _⟩ := near_key m ψ hψ ε hε hω hratio t0 ht0
    have hdc : ContinuousAt (fun t : ℝ => tauN ψ m - nearSegPoint m ψ t) t0 :=
      continuousAt_const.sub hZ.continuousAt
    have h4 : (4 : ℂ) * (tauN ψ m - nearSegPoint m ψ t0) ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hd0)
    have hbase : ContinuousAt (fun t : ℝ =>
        1 - gap ψ m ^ 2 / (4 * (tauN ψ m - nearSegPoint m ψ t) ^ 2)) t0 :=
      continuousAt_const.sub (ContinuousAt.div continuousAt_const
        (continuousAt_const.mul (hdc.pow 2)) h4)
    have hcond : 0 ≤ (1 - gap ψ m ^ 2 / (4 * (tauN ψ m - nearSegPoint m ψ t0) ^ 2)).re ∨
        (1 - gap ψ m ^ 2 / (4 * (tauN ψ m - nearSegPoint m ψ t0) ^ 2)).im ≠ 0 :=
      (Complex.mem_slitPlane_iff.1 hslit0).imp (fun h => le_of_lt h) (fun h => h)
    have hsqrt : ContinuousAt (fun t : ℝ =>
        Complex.sqrt (1 - gap ψ m ^ 2 / (4 * (tauN ψ m - nearSegPoint m ψ t) ^ 2))) t0 :=
      ContinuousAt.comp (g := Complex.sqrt) (Complex.continuousAt_sqrt hcond) hbase
    have hE : ContinuousAt (fun t : ℝ => (tauN ψ m - nearSegPoint m ψ t) *
        Complex.sqrt (1 - gap ψ m ^ 2 / (4 * (tauN ψ m - nearSegPoint m ψ t) ^ 2))) t0 :=
      hdc.mul hsqrt
    exact hE.continuousWithinAt.congr
      (fun t ht => (near_key m ψ hψ ε hε hω hratio t ht).2.2)
      (near_key m ψ hψ ε hε hω hratio t0 ht0).2.2
  have hDne : ∀ t ∈ Icc ε 1, standardRoot ψ m (nearSegPoint m ψ t) ≠ 0 := by
    intro t ht
    obtain ⟨hd0, hslit0, hid0⟩ := near_key m ψ hψ ε hε hω hratio t ht
    rw [hid0]
    exact mul_ne_zero hd0 (g3s2_sqrt_ne _ (Complex.slitPlane_ne_zero hslit0))
  unfold nearRatio
  exact ContinuousOn.div (continuousOn_const.sub hZ.continuousOn) hDcont hDne

theorem near_density_contOn (n m : ℤ) (hmn : m ≠ n) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (ψ : PotPair) (hψ : ψ ∈ sourceW) (hgk : ψ ∈ gkW)
    (hspec : IsolatingSpectral38 ψ C R) (ε : ℝ) (hε : 0 < ε)
    (hω : nearOmega m ψ ≠ 0) (hratio : ‖gap ψ m / nearOmega m ψ‖ ≤ ε / 2) :
    ContinuousOn (fun t : ℝ => nearDensity n m ψ t) (Icc ε 1) := by
  unfold nearDensity
  exact ((near_ratio_contOn n m ψ hψ ε hε hω hratio).mul
    (near_zeta_contOn n m hmn C R c N hg ψ hgk hspec ε hε)).mul continuousOn_const

theorem near_eventually_integrable (n m : ℤ) (hmn : m ≠ n) (v : ℕ → PotPair) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceW) (hgap : gamma2 φ0 m = 0) (hv : Tendsto v atTop (𝓝 φ0))
    (hnot : φ0 ∉ endpointSet m) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ j in atTop, IntervalIntegrable (nearDensity n m (v j)) volume ε 1 := by
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  obtain ⟨U, hUo, hφ0U, hUgk, C, R, c, N, hg, hspecU⟩ := g2019_leaf_family φ0 hgk0
  have hω0 : nearOmega m φ0 ≠ 0 := G3021N.omega_ne m φ0 hφ0 hnot
  have hωT := G3021N.omega_tendsto m v φ0 hφ0 hgap hv
  have hgT := g3s1_gap_tendsto v φ0 m hφ0 hgap hv
  have hωlim : muSeq φ0 m - tauN φ0 m ≠ 0 := by
    have h : nearOmega m φ0 = muSeq φ0 m - tauN φ0 m := by
      unfold nearOmega; rw [G3021N.near_collapsed_value m φ0 hφ0 hgap]
    rw [← h]; exact hω0
  have hq : Tendsto (fun j : ℕ => gap (v j) m / nearOmega m (v j)) atTop (𝓝 0) := by
    have h := hgT.div hωT hωlim
    rwa [zero_div] at h
  have hratio : ∀ᶠ j in atTop, ‖gap (v j) m / nearOmega m (v j)‖ ≤ ε / 2 := by
    have h := Metric.tendsto_nhds.1 hq (ε / 2) (by linarith [hε.1])
    filter_upwards [h] with j hj
    rw [dist_zero_right] at hj
    exact hj.le
  have hωne : ∀ᶠ j in atTop, nearOmega m (v j) ≠ 0 := hωT.eventually_ne hωlim
  have hvU : ∀ᶠ j in atTop, v j ∈ U := hv.eventually (hUo.mem_nhds hφ0U)
  have hvW : ∀ᶠ j in atTop, v j ∈ sourceW := hv.eventually (sourceFamily.W_open.mem_nhds hφ0)
  filter_upwards [hvU, hratio, hωne, hvW] with j hU hr hω hW
  have hc := near_density_contOn n m hmn C R c N hg (v j) hW (hUgk hU)
    (hspecU (v j) hU) ε hε.1 hω hr
  exact ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hε.2.le]; exact hc)

theorem near_final_tendsto (n m : ℤ) (hmn : m ≠ n) (v : ℕ → PotPair) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceW) (hgap : gamma2 φ0 m = 0) (hv : Tendsto v atTop (𝓝 φ0))
    (hnot : φ0 ∉ endpointSet m) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun j : ℕ => ∫ t in ε..(1 : ℝ), nearDensity n m (v j) t) atTop
      (𝓝 (collapsedBetaFinalSegment n m φ0 ε)) := by
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  have hlam := g3s1_lam_eq φ0 hgk0 m hgap
  have hunif := near_zeta_unif n m hmn v φ0 hφ0 hgap hv ε hε
  have hωT := G3021N.omega_tendsto m v φ0 hφ0 hgap hv
  obtain ⟨U, hUo, hφ0U, hUgk, Cr, Rr, c, N, hg, hspecU⟩ := g2019_leaf_family φ0 hgk0
  have hG0c : ContinuousOn (fun t : ℝ => betaZeta n m φ0
      (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m))) (Icc ε 1) := by
    have h := g3s2_betaZeta_contOn n m hmn Cr Rr c N hg φ0 hgk0 (hspecU φ0 hφ0U) ε hε.1
    have hfun : (fun t : ℝ => betaZeta n m φ0
        (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m))) =
        fun t : ℝ => betaZeta n m φ0 (betaSegmentPoint m φ0 t) := by
      funext t
      rw [g3s1_seg_eq φ0 m hlam.2 t]
    rw [hfun]
    exact h
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := ε) (b := 1)).exists_bound_of_continuousOn hG0c
  obtain ⟨C1, hC1pos, hC1⟩ : ∃ C1 : ℝ, 0 < C1 ∧ ∀ t ∈ Icc ε 1,
      ‖betaZeta n m φ0 (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m))‖ ≤ C1 :=
    ⟨max C0 0 + 1, by linarith [le_max_right C0 0],
      fun t ht => le_trans (hC0 t ht) (by linarith [le_max_left C0 0])⟩
  have hF : IntervalIntegrable (fun t : ℝ => betaZeta n m φ0
      (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m)) volume ε 1 :=
    g3s3_integrable n m hmn φ0 hφ0 hgap hnot ε hε
  have hE := near_eventually_integrable n m hmn v φ0 hφ0 hgap hv hnot ε hε
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (C1 + 1) * (‖muSeq φ0 m - tauN φ0 m‖ + 1) +
      (‖muSeq φ0 m - tauN φ0 m‖ + 1) + C1 := ⟨_, rfl⟩
  have hQpos : 0 ≤ Q := by
    rw [hQ]
    have := norm_nonneg (muSeq φ0 m - tauN φ0 m)
    nlinarith
  have hQ1 : Q + 1 ≠ 0 := ne_of_gt (by linarith)
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ1, hδ2, hδpos⟩ : ∃ δ : ℝ, δ ≤ 1 ∧ δ ≤ η / (2 * (Q + 1)) ∧ 0 < δ :=
    ⟨min 1 (η / (2 * (Q + 1))), min_le_left _ _, min_le_right _ _,
      lt_min one_pos (div_pos hη (by linarith))⟩
  have hδQ : δ * Q ≤ η / 2 := by
    have h1 : δ * (Q + 1) ≤ η / (2 * (Q + 1)) * (Q + 1) :=
      mul_le_mul_of_nonneg_right hδ2 (by linarith)
    have h2 : η / (2 * (Q + 1)) * (Q + 1) = η / 2 := by
      rw [div_mul_eq_mul_div, mul_div_mul_right η 2 hQ1]
    have h3 : δ * (Q + 1) = δ * Q + δ := by ring
    linarith
  have hA : ∀ᶠ j in atTop, ∀ t ∈ Icc ε 1,
      ‖nearRatio n m (v j) t - 1‖ < δ := by
    obtain ⟨J, hJ⟩ := near_ratio_uniform n m hmn v φ0 hφ0 hgap hv hnot ε hε δ hδpos
    exact eventually_atTop.2 ⟨J, fun j hj t ht => (hJ j hj t ht).2⟩
  have hB : ∀ᶠ j in atTop, ∀ t ∈ Icc ε 1, dist
      (betaZeta n m φ0 (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)))
      (betaZeta n m (v j) (nearSegPoint m (v j) t)) < δ :=
    Metric.tendstoUniformlyOn_iff.1 hunif δ hδpos
  have hC : ∀ᶠ j in atTop, dist (nearOmega m (v j)) (muSeq φ0 m - tauN φ0 m) < δ :=
    Metric.tendsto_nhds.1 hωT δ hδpos
  have hmain : ∀ᶠ j in atTop, ∀ t ∈ Icc ε 1,
      ‖nearDensity n m (v j) t - betaZeta n m φ0
        (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m)‖ ≤ η / 2 := by
    filter_upwards [hA, hB, hC] with j hAj hBj hCj t ht
    have hR : ‖nearRatio n m (v j) t - 1‖ ≤ δ := (hAj t ht).le
    have hdist : ‖betaZeta n m (v j) (nearSegPoint m (v j) t) -
        betaZeta n m φ0 (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m))‖ < δ := by
      have h := hBj t ht
      rw [dist_comm, dist_eq_norm] at h
      exact h
    have hωd : ‖nearOmega m (v j) - (muSeq φ0 m - tauN φ0 m)‖ < δ := by
      rw [dist_eq_norm] at hCj
      exact hCj
    have hGj : ‖betaZeta n m (v j) (nearSegPoint m (v j) t)‖ ≤ C1 + 1 := by
      have h1 := norm_sub_norm_le (betaZeta n m (v j) (nearSegPoint m (v j) t))
        (betaZeta n m φ0 (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)))
      have h0 := hC1 t ht
      linarith
    have hωW : ‖nearOmega m (v j)‖ ≤ ‖muSeq φ0 m - tauN φ0 m‖ + 1 := by
      have h1 := norm_sub_norm_le (nearOmega m (v j)) (muSeq φ0 m - tauN φ0 m)
      linarith
    have key := g3s4_bound (nearRatio n m (v j) t)
      (betaZeta n m (v j) (nearSegPoint m (v j) t))
      (betaZeta n m φ0 (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)))
      (nearOmega m (v j)) (muSeq φ0 m - tauN φ0 m) δ (C1 + 1) C1
      (‖muSeq φ0 m - tauN φ0 m‖ + 1) hδpos.le hR hGj hdist.le (hC1 t ht) hωW hωd.le
      (by linarith) (by positivity) hC1pos.le
    unfold nearDensity
    have hsub : δ * ((C1 + 1) * (‖muSeq φ0 m - tauN φ0 m‖ + 1) +
        (‖muSeq φ0 m - tauN φ0 m‖ + 1) + C1) = δ * Q := by rw [hQ]
    linarith
  filter_upwards [hE, hmain] with j hEj hmj
  rw [dist_eq_norm]
  unfold collapsedBetaFinalSegment
  rw [← intervalIntegral.integral_sub hEj hF]
  have hsub : Set.uIoc ε 1 ⊆ Icc ε 1 := by
    rw [uIoc_of_le hε.2.le]
    exact Ioc_subset_Icc_self
  have hbound : ‖∫ t in ε..1, (nearDensity n m (v j) t - betaZeta n m φ0
      (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m))‖ ≤
      η / 2 * |1 - ε| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => hmj t (hsub ht))
  have habs : |1 - ε| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hε.1, hε.2]
  have h4 : η / 2 * |1 - ε| ≤ η / 2 * 1 := mul_le_mul_of_nonneg_left habs (by linarith)
  exact lt_of_le_of_lt (le_trans hbound h4) (by linarith)

end
end NlsGge.GKDefinitionDesign
