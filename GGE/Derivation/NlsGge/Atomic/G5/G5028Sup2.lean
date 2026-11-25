import Mathlib
import NlsGge.GK38.GradEigenDirichlet
import NlsGge.GK38.DirichletCharDefs
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.PairRealBridge
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.TauGamma
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.GradEigenRealPeriodicLabels

/- G5-028 SUPPORT 2 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5028Sup2.lean, namespace NlsGge.Atomic.G5028.
   Real-analysis leaves (no new hypotheses): continuity of the spectral derivative of dirichletChar, a Lipschitz bound along a
   convergent sequence of potentials, a lower bound |P z| >= c |z - lam| at a simple zero, ordering of open-gap lower endpoints,
   and a squeeze lemma. -/
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.Atomic.G5028
noncomputable section

theorem continuous_deriv_dirichletChar :
    Continuous (fun p : PotPair × ℂ => deriv (dirichletChar p.1) p.2) := by
  have h : (fun p : PotPair × ℂ => deriv (dirichletChar p.1) p.2) =
      fun p => (fderiv ℂ (fun q : PotPair × ℂ => dirichletChar q.1 q.2) p) ((0 : PotPair), (1 : ℂ)) := by
    funext p
    exact (GradEigen38.dirichlet_joint_spectral_partial p.1 p.2).symm
  rw [h]
  have hc : Continuous (fderiv ℂ (fun q : PotPair × ℂ => dirichletChar q.1 q.2)) :=
    continuousOn_univ.mp (analyticOnNhd_dirichletChar.fderiv.continuousOn)
  exact (ContinuousLinearMap.apply ℂ ℂ ((0 : PotPair), (1 : ℂ))).continuous.comp hc

/-- Along a convergent sequence of potentials, a root `a j -> z0` of `dirichletChar (φ j)`:
`‖D_j(z0)‖ ≤ C ‖z0 - a j‖` eventually. -/
theorem dirichlet_lipschitz_along (φ : ℕ → PotPair) (φ₀ : PotPair) (a : ℕ → ℂ) (z₀ : ℂ)
    (hφ : Tendsto φ atTop (𝓝 φ₀)) (ha : Tendsto a atTop (𝓝 z₀))
    (hroot : ∀ j, dirichletChar (φ j) (a j) = 0) :
    ∃ C : ℝ, ∀ᶠ j in atTop, ‖dirichletChar (φ j) z₀‖ ≤ C * ‖z₀ - a j‖ := by
  set c₀ : ℝ := ‖deriv (dirichletChar φ₀) z₀‖ with hc₀
  have hcont : Continuous (fun p : PotPair × ℂ => ‖deriv (dirichletChar p.1) p.2‖) :=
    continuous_deriv_dirichletChar.norm
  have hn : ∀ᶠ p in 𝓝 (φ₀, z₀), ‖deriv (dirichletChar p.1) p.2‖ < c₀ + 1 :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simp only [hc₀]; linarith)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨c₀ + 1, ?_⟩
  have h1 : ∀ᶠ j in atTop, φ j ∈ ball φ₀ r := hφ.eventually (ball_mem_nhds φ₀ hr)
  have h2 : ∀ᶠ j in atTop, a j ∈ ball z₀ r := ha.eventually (ball_mem_nhds z₀ hr)
  filter_upwards [h1, h2] with j hj1 hj2
  have hb : ∀ x ∈ ball z₀ r, ‖deriv (dirichletChar (φ j)) x‖ ≤ c₀ + 1 := by
    intro x hx
    have : (φ j, x) ∈ ball (φ₀, z₀) r := by
      rw [← ball_prod_same]; exact ⟨hj1, hx⟩
    exact (hball this).le
  have hd : ∀ x ∈ ball z₀ r, DifferentiableAt ℂ (dirichletChar (φ j)) x :=
    fun x _ => (analyticOnNhd_dirichletChar_z (φ j) x (mem_univ _)).differentiableAt
  have := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_ball z₀ r) hj2 (mem_ball_self hr)
  rw [hroot j, sub_zero] at this
  exact this

/-- A simple zero gives a linear lower bound. -/
theorem simple_zero_lower (P : ℂ → ℂ) (lam : ℂ) (hP : P lam = 0) (hd : DifferentiableAt ℂ P lam)
    (hs : deriv P lam ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z in 𝓝 lam, c * ‖z - lam‖ ≤ ‖P z‖ := by
  have hpos : 0 < ‖deriv P lam‖ := norm_pos_iff.mpr hs
  refine ⟨‖deriv P lam‖ / 2, by positivity, ?_⟩
  have ho := (hasDerivAt_iff_isLittleO.mp hd.hasDerivAt)
  have hev := ho.def (half_pos hpos)
  filter_upwards [hev] with z hz
  rw [hP, sub_zero] at hz
  have hz2 : ‖(z - lam) • deriv P lam‖ = ‖z - lam‖ * ‖deriv P lam‖ := by
    rw [norm_smul]
  have hz' : ‖P z - (z - lam) • deriv P lam‖ ≤ ‖deriv P lam‖ / 2 * ‖z - lam‖ := hz
  have h4 : ‖(z - lam) • deriv P lam‖ ≤ ‖P z‖ + ‖P z - (z - lam) • deriv P lam‖ := by
    have e : (z - lam) • deriv P lam = P z - (P z - (z - lam) • deriv P lam) := by abel
    calc ‖(z - lam) • deriv P lam‖ = ‖P z - (P z - (z - lam) • deriv P lam)‖ := by rw [← e]
      _ ≤ ‖P z‖ + ‖P z - (z - lam) • deriv P lam‖ := norm_sub_le _ _
  rw [hz2] at h4
  nlinarith [norm_nonneg (z - lam)]

theorem squeeze_sqrt (Q : ℕ → ℂ) (e : ℕ → ℝ) (K : ℝ) (he : Tendsto e atTop (𝓝 0))
    (hQ : ∀ᶠ j in atTop, ‖Q j‖ ≤ K * Real.sqrt (e j)) : Tendsto Q atTop (𝓝 0) := by
  have h1 : Tendsto (fun j => K * Real.sqrt (e j)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp he
    simpa using this.const_mul K
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  exact squeeze_zero' (Eventually.of_forall fun j => norm_nonneg _) hQ h1

theorem open_gap_lt (u : PhysicalL2) (n : ℤ) (h : gamma2 (realSlice u) n ≠ 0) :
    actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n := by
  have hgk : realSlice u ∈ gkW := realSlice_mem_gkW u
  obtain ⟨hP, hM⟩ := lamPlus_real u n
  rw [gamma2_value38 _ hgk n, hP, hM, ← Complex.ofReal_sub] at h
  have hne : actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n ≠ 0 := by
    intro h0; apply h; rw [h0]; simp
  have hle := periodic_pair_re_order38 u n
  rw [hP, hM, Complex.ofReal_re, Complex.ofReal_re] at hle
  exact lt_of_le_of_ne hle (fun h' => hne (by rw [h']; ring))

theorem lamMinus_re_lt (u : PhysicalL2) (k l : ℤ) (hk : gamma2 (realSlice u) k ≠ 0) (hkl : k < l) :
    (lamMinus (realSlice u) k).re < (lamMinus (realSlice u) l).re := by
  obtain ⟨hP, hM⟩ := lamPlus_real u k
  have h1 : (lamMinus (realSlice u) k).re < (lamPlus (realSlice u) k).re := by
    rw [hP, hM, Complex.ofReal_re, Complex.ofReal_re]; exact open_gap_lt u k hk
  have h2 : complexLexLE38 (lamPlus (realSlice u) k) (lamMinus (realSlice u) l) := by
    have := lamSeq_mono38 (realSlice u) (i := 2 * k + 1) (j := 2 * l) (by omega)
    exact this
  have h3 : (lamPlus (realSlice u) k).re ≤ (lamMinus (realSlice u) l).re := by
    rcases (complexLexLE_iff38 _ _).mp h2 with h | h
    · exact h.le
    · exact h.1.le
  linarith

theorem lamMinus_ne_of_open (u : PhysicalL2) (k l : ℤ) (hkl : k ≠ l)
    (hk : gamma2 (realSlice u) k ≠ 0) (hl : gamma2 (realSlice u) l ≠ 0) :
    lamMinus (realSlice u) k ≠ lamMinus (realSlice u) l := by
  intro h
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have := lamMinus_re_lt u k l hk hlt
    rw [h] at this; exact lt_irrefl _ this
  · have := lamMinus_re_lt u l k hl hgt
    rw [h] at this; exact lt_irrefl _ this

theorem gamma2_ne_zero_of_lt (u : PhysicalL2) (n : ℤ)
    (h : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n) : gamma2 (realSlice u) n ≠ 0 := by
  obtain ⟨hP, hM⟩ := lamPlus_real u n
  rw [gamma2_value38 _ (realSlice_mem_gkW u) n, hP, hM, ← Complex.ofReal_sub]
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr h.ne'))

theorem lower_endpoint_simple (u : PhysicalL2) (n : ℤ) (h : gamma2 (realSlice u) n ≠ 0) :
    lamMinus (realSlice u) n = (actualGapLowerAllE02_38 u n : ℂ) ∧
    perChar (realSlice u) (lamMinus (realSlice u) n) = 0 ∧
    deriv (perChar (realSlice u)) (lamMinus (realSlice u) n) ≠ 0 := by
  have hgap := open_gap_lt u n h
  obtain ⟨hP, hM⟩ := lamPlus_real u n
  refine ⟨hM, (lamSeq_enumeration38 (realSlice u)).1 (2 * n), ?_⟩
  have := GradEigen38.endpoint_perChar_deriv_ne_zero u n false hgap
  simp only [GradEigen38.endpoint, Bool.false_eq_true, if_false] at this
  rw [hM]; exact this

theorem real_aux (e δ N m₀ C A c : ℝ) (he : 0 ≤ e) (hδ : 0 < δ) (hc : 0 < c) (hm : 0 < m₀) (hA : 0 < A)
    (hC : 0 ≤ C) (hN0 : 0 ≤ N) (hN : N ≤ C * e) (hδe : c * e ≤ δ ^ 2) :
    N / m₀ / (A * δ) ≤ (C / (m₀ * A * Real.sqrt c)) * Real.sqrt e := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  rcases he.eq_or_lt with h0 | hpos
  · subst h0
    have : N = 0 := le_antisymm (by simpa using hN) hN0
    simp [this]
  · have hse : 0 < Real.sqrt e := Real.sqrt_pos.mpr hpos
    have hδ' : Real.sqrt c * Real.sqrt e ≤ δ := by
      rw [← Real.sqrt_mul hc.le]
      exact Real.sqrt_le_iff.mpr ⟨hδ.le, hδe⟩
    have h1 : N / m₀ ≤ C * e / m₀ := div_le_div_of_nonneg_right hN hm.le
    have hden : 0 < A * δ := by positivity
    calc N / m₀ / (A * δ) ≤ C * e / m₀ / (A * δ) := div_le_div_of_nonneg_right h1 hden.le
      _ ≤ C * e / m₀ / (A * (Real.sqrt c * Real.sqrt e)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hδ' hA.le
      _ = (C / (m₀ * A * Real.sqrt c)) * Real.sqrt e := by
          have : e = Real.sqrt e * Real.sqrt e := (Real.mul_self_sqrt he).symm
          field_simp
          nth_rewrite 1 [this]
          ring

end
end NlsGge.Atomic.G5028
