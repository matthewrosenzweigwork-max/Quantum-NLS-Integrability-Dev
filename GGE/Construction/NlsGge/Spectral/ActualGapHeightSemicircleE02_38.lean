import NlsGge.Spectral.ActualGapsActionsE02_38
import NlsGge.Spectral.ActualQuasimomentumBoundaryLimitE02_38
import NlsGge.Spectral.ActualQuasimomentumEndpointSqrtE02_38
import NlsGge.Spectral.ActualQuasimomentumLocalContinuationE02_38
import NlsGge.Herglotz38.GapSqrtCutLimitE02_38
import NlsGge.Herglotz38.HalfPlaneMinPrincipleLimitsE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # NEW-E01.01 (campaign 38): semicircle lower bound for the gap height on labelled gaps

Proof-route departure (recorded in `NlsGge/Herglotz38/SCOPE.md`): instead of the cited
Herglotz representation `v = √((λ-λ⁻)(λ⁺-λ))(1+Y)`, `Y ≥ 0`, we prove the equivalent
pointwise bound `v ≥ √((λ-λ⁻)(λ⁺-λ))` by the half-plane minimum principle applied to
`Φ(z) = (G(z) - G(λ₀))/(z - λ₀)`, `G = (k - nπ)/√((z-λ⁻)(z-λ⁺))`. -/

theorem vertical_tendsto_upper_E02_38 (x : ℝ) :
    Tendsto (fun ε : ℝ => (x:ℂ) + Complex.I*(ε:ℂ)) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Continuous (fun ε : ℝ => (x:ℂ) + Complex.I*(ε:ℂ)) := by fun_prop
    have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa using hε

theorem boundaryLimit_im_E02_38 (u : PhysicalL2) (x : ℝ) (L : ℂ)
    (hL : Tendsto (actualQuasimomentumE02_38 u) (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ)) (𝓝 L)) :
    L.im = actualGapHeightE02_38 u x :=
  tendsto_nhds_unique ((Complex.continuous_im.tendsto L).comp
    (hL.comp (vertical_tendsto_upper_E02_38 x))) (tendsto_im_actualQuasimomentumE02_38 u x)

theorem boundaryLimit_re_gap_E02_38 (u : PhysicalL2) (n : ℤ) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/1000) (hbox : ActualHalfTraceBoxE02_38 u n δ)
    (hwin : ActualQuasimomentumWindowE02_38 u n) (x : ℝ) (hx : x ∈ actualGapE02_38 u n) (L : ℂ)
    (hL : Tendsto (actualQuasimomentumE02_38 u) (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ)) (𝓝 L)) :
    L.re = (n:ℝ)*Real.pi :=
  tendsto_nhds_unique ((Complex.continuous_re.tendsto L).comp
    (hL.comp (vertical_tendsto_upper_E02_38 x)))
    (tendsto_re_actualQuasimomentum_gap_E02_38 u n δ hδ0 hδ hbox hwin x hx)

theorem im_div_ofReal_sub_div_E02_38 (w : ℂ) (r t c : ℝ) (hr : r ≠ 0) (ht : t ≠ 0) :
    ((w / (r:ℂ) - (c:ℂ)) / (t:ℂ)).im = w.im / (r*t) := by
  rw [Complex.div_ofReal_im, Complex.sub_im, Complex.div_ofReal_im, Complex.ofReal_im, sub_zero]
  field_simp

/-- Large-`|z|` control of `G = (k - p₀)/s`. -/
theorem exists_G_sub_one_le_E02_38 (k : ℂ → ℂ)
    (hk : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ → ‖k z - z‖ < ε)
    (a b : ℝ) (p₀ : ℂ) :
    ∃ B R₀ : ℝ, 0 ≤ B ∧ 0 < R₀ ∧ ∀ z : ℂ, 0 < z.im → R₀ ≤ ‖z‖ →
      gapSqrt a b z ≠ 0 ∧ ‖(k z - p₀)/gapSqrt a b z - 1‖ ≤ B/‖z‖ := by
  set m : ℂ := -(((a:ℂ) + (b:ℂ))/2)
  have hev := (gapSqrt_sub_id_tendsto a b).eventually (Metric.ball_mem_nhds m one_pos)
  obtain ⟨K, hK, hKsub⟩ := mem_cocompact.mp hev
  obtain ⟨R₂, hR₂⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨R₁, hR₁, hk1⟩ := hk 1 one_pos
  set C₂ : ℝ := ‖m‖ + 1
  have hs : ∀ z : ℂ, R₂ < ‖z‖ → ‖gapSqrt a b z - z‖ ≤ C₂ := by
    intro z hz
    have hzK : z ∉ K := fun h => by
      have := hR₂ h; rw [Metric.mem_closedBall, dist_zero_right] at this; linarith
    have h : ‖gapSqrt a b z - z - m‖ < 1 := by
      have h0 := hKsub hzK
      simpa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using h0
    calc ‖gapSqrt a b z - z‖ = ‖(gapSqrt a b z - z - m) + m‖ := by ring_nf
      _ ≤ ‖gapSqrt a b z - z - m‖ + ‖m‖ := norm_add_le _ _
      _ ≤ C₂ := by simp only [C₂]; linarith
  set B₀ : ℝ := 1 + ‖p₀‖ + C₂
  refine ⟨2*B₀, max (max R₁ (|R₂| + 1)) (2*C₂ + 1), by positivity, by positivity, ?_⟩
  intro z hz hzR
  have hz1 : R₁ ≤ ‖z‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hzR
  have hz2 : R₂ < ‖z‖ := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hzR
    linarith [le_abs_self R₂]
  have hz3 : 2*C₂ + 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hzR
  have hsz := hs z hz2
  have hsnorm : ‖z‖/2 ≤ ‖gapSqrt a b z‖ := by
    have := norm_sub_norm_le z (z - gapSqrt a b z)
    rw [show z - (z - gapSqrt a b z) = gapSqrt a b z by ring, norm_sub_rev] at this
    have hC₂ : 0 ≤ C₂ := by positivity
    linarith
  have hzpos : 0 < ‖z‖ := by
    have : (0:ℝ) < 2*C₂ + 1 := by positivity
    linarith
  have hs0 : gapSqrt a b z ≠ 0 := by
    intro h; rw [h, norm_zero] at hsnorm; linarith
  refine ⟨hs0, ?_⟩
  have hnum : ‖k z - p₀ - gapSqrt a b z‖ ≤ B₀ := by
    calc ‖k z - p₀ - gapSqrt a b z‖ = ‖(k z - z) - p₀ - (gapSqrt a b z - z)‖ := by ring_nf
      _ ≤ ‖(k z - z) - p₀‖ + ‖gapSqrt a b z - z‖ := norm_sub_le _ _
      _ ≤ (‖k z - z‖ + ‖p₀‖) + ‖gapSqrt a b z - z‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ B₀ := by simp only [B₀]; linarith [(hk1 z hz hz1).le]
  rw [show (k z - p₀)/gapSqrt a b z - 1 = (k z - p₀ - gapSqrt a b z)/gapSqrt a b z by
    field_simp, norm_div]
  rw [div_le_div_iff₀ (by positivity) hzpos]
  calc ‖k z - p₀ - gapSqrt a b z‖ * ‖z‖ ≤ B₀ * ‖z‖ := by gcongr
    _ = 2 * B₀ * (‖z‖/2) := by ring
    _ ≤ 2 * B₀ * ‖gapSqrt a b z‖ := by gcongr


theorem le_one_add_of_sq_le_E02_38 (t K : ℝ) (ht : 0 ≤ t) (h : t^2 ≤ K) : t ≤ 1 + K := by
  rcases le_or_gt t 1 with h1 | h1
  · nlinarith [sq_nonneg t]
  · nlinarith

theorem norm_ofReal_sub_ofReal_E02_38 (x y : ℝ) : ‖(x:ℂ) - (y:ℂ)‖ = |x - y| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- Boundedness of `Φ` near a gap endpoint, from the square-root control of `k`. -/
theorem bounded_near_endpoint_E02_38 (k : ℂ → ℂ) (a b e e' x₀ : ℝ) (p₀ c : ℂ)
    (C r : ℝ) (hr : 0 < r)
    (hK6 : ∀ z : ℂ, 0 < z.im → ‖z - e‖ < r → ‖k z - p₀‖^2 ≤ C*‖z - e‖)
    (hsq : ∀ z : ℂ, ‖gapSqrt a b z‖^2 = ‖z - e‖*‖z - e'‖)
    (d : ℝ) (hd : 0 < d) (he' : d ≤ |e - e'|) (hx₀ : d ≤ |e - x₀|) :
    ∃ r' > 0, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖z - e‖ < r' →
      ‖((k z - p₀)/gapSqrt a b z - c)/(z - x₀)‖ ≤ M := by
  refine ⟨min r (d/2), lt_min hr (by linarith), (1 + 2 * |C|/d + ‖c‖)*(2/d), ?_⟩
  intro z hz hze
  have hze1 : ‖z - e‖ < r := lt_of_lt_of_le hze (min_le_left _ _)
  have hze2 : ‖z - e‖ < d/2 := lt_of_lt_of_le hze (min_le_right _ _)
  have hfar : ∀ y : ℝ, d ≤ |e - y| → d/2 ≤ ‖z - y‖ := by
    intro y hy
    have h1 : ‖(e:ℂ) - y‖ ≤ ‖z - y‖ + ‖z - e‖ := by
      calc ‖(e:ℂ) - y‖ = ‖(z - y) - (z - e)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [norm_ofReal_sub_ofReal_E02_38] at h1
    linarith
  have hze0 : 0 < ‖z - e‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro h; rw [h] at hz; simp at hz
  have he'd := hfar e' he'
  have hx₀d := hfar x₀ hx₀
  have hs2 : ‖z - e‖ * (d/2) ≤ ‖gapSqrt a b z‖^2 := by
    rw [hsq]; exact mul_le_mul_of_nonneg_left he'd hze0.le
  have hspos : 0 < ‖gapSqrt a b z‖ := by
    have : 0 < ‖gapSqrt a b z‖^2 := lt_of_lt_of_le (by positivity) hs2
    rcases (norm_nonneg (gapSqrt a b z)).lt_or_eq with h | h
    · exact h
    · rw [← h] at this; simp at this
  have hG2 : ‖(k z - p₀)/gapSqrt a b z‖^2 ≤ 2 * |C|/d := by
    rw [norm_div, div_pow, div_le_iff₀ (by positivity)]
    calc ‖k z - p₀‖^2 ≤ C*‖z - e‖ := hK6 z hz hze1
      _ ≤ |C| * ‖z - e‖ := by gcongr; exact le_abs_self C
      _ = 2 * |C|/d * (‖z - e‖ * (d/2)) := by field_simp
      _ ≤ 2 * |C|/d * ‖gapSqrt a b z‖^2 := by gcongr
  have hG := le_one_add_of_sq_le_E02_38 _ _ (norm_nonneg _) hG2
  rw [norm_div]
  rw [div_le_iff₀ (lt_of_lt_of_le (by linarith) hx₀d)]
  calc ‖(k z - p₀)/gapSqrt a b z - c‖ ≤ ‖(k z - p₀)/gapSqrt a b z‖ + ‖c‖ := norm_sub_le _ _
    _ ≤ 1 + 2 * |C|/d + ‖c‖ := by linarith
    _ = (1 + 2 * |C|/d + ‖c‖)*(2/d) * (d/2) := by field_simp
    _ ≤ (1 + 2 * |C|/d + ‖c‖)*(2/d) * ‖z - x₀‖ := by gcongr


/-- Final step: `Im[(G(iy) - c)/(iy - x₀)] ≥ 0` for all `y > 0` and `G(iy) → 1` force `c ≥ 1`. -/
theorem one_le_of_im_quotient_nonneg_E02_38 (G : ℂ → ℂ) (c x₀ B R₀ : ℝ) (hB : 0 ≤ B)
    (hR₀ : 0 < R₀)
    (hG : ∀ y : ℝ, R₀ ≤ y → ‖G (Complex.I*(y:ℂ)) - 1‖ ≤ B/y)
    (him : ∀ y : ℝ, 0 < y → 0 ≤ ((G (Complex.I*(y:ℂ)) - (c:ℂ))/(Complex.I*(y:ℂ) - (x₀:ℂ))).im) :
    1 ≤ c := by
  by_contra hc
  push Not at hc
  set η := 1 - c with hη
  have hη0 : 0 < η := by linarith
  set y : ℝ := max R₀ (max (|x₀| + 1) (4*B/η + 1)) with hy
  have hyR : R₀ ≤ y := le_max_left _ _
  have hyx : |x₀| + 1 ≤ y := le_trans (le_max_left _ _) (le_max_right _ _)
  have hyB : 4*B/η + 1 ≤ y := le_trans (le_max_right _ _) (le_max_right _ _)
  have hy0 : 0 < y := lt_of_lt_of_le hR₀ hyR
  set w := G (Complex.I*(y:ℂ))
  have he := hG y hyR
  set e := ‖w - 1‖
  have hN : 0 < Complex.normSq (Complex.I*(y:ℂ) - (x₀:ℂ)) := by
    rw [Complex.normSq_pos]; intro h
    have := congrArg Complex.im h; simp at this; linarith
  have h := him y hy0
  rw [Complex.div_im, ← sub_div] at h
  have hnum : 0 ≤ (w - (c:ℂ)).im * (Complex.I*(y:ℂ) - (x₀:ℂ)).re -
      (w - (c:ℂ)).re * (Complex.I*(y:ℂ) - (x₀:ℂ)).im := by
    rcases div_nonneg_iff.mp h with h1 | h1
    · exact h1.1
    · exact absurd h1.2 (not_le.mpr hN)
  simp only [Complex.sub_im, Complex.sub_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    sub_zero, zero_sub, mul_zero] at hnum
  have hwim : |w.im| ≤ e := by
    have := Complex.abs_im_le_norm (w - 1); simpa using this
  have hwre : 1 - e ≤ w.re := by
    have := Complex.abs_re_le_norm (w - 1)
    have h2 : (w - 1).re = w.re - 1 := by simp
    rw [h2] at this; linarith [(abs_le.mp this).1]
  have hx₀w : -(x₀ * w.im) ≤ |x₀| * e := by
    have := abs_mul x₀ w.im
    have h3 : |x₀ * w.im| ≤ |x₀| * e := by rw [abs_mul]; gcongr
    linarith [neg_abs_le (x₀ * w.im)]
  -- hnum : w.im * -x₀ - (w.re - c) * y ≥ 0
  have hmain : (η - e) * y ≤ |x₀| * e := by
    have : (w.re - c) * y ≥ (η - e) * y := by
      apply mul_le_mul_of_nonneg_right _ hy0.le; linarith
    nlinarith
  have hey : e * y ≤ B := by
    have := he; rw [le_div_iff₀ hy0] at this; linarith
  have h4 : η * y ≤ 2 * B := by
    have : |x₀| * e ≤ y * e := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    nlinarith
  have h5 : 4*B < η * y := by
    have : 4*B/η < y := by linarith
    rw [div_lt_iff₀ hη0] at this; linarith
  linarith


/-- Generic form of the semicircle bound on one gap interval `(a,b)`: its inputs are the
boundary value `nπ + i v` of `k` on the gap, square-root control at both endpoints, and
`|Δh(x₀)| > 1`. No labels, Box or Window hypotheses. -/
theorem gapHeight_ge_semicircle_generic_E02_38 (u : PhysicalL2) (n : ℤ) (a b x₀ : ℝ)
    (hx₀ : x₀ ∈ Set.Ioo a b)
    (hgapL : ∀ x ∈ Set.Ioo a b, ∀ L : ℂ,
      Tendsto (actualQuasimomentumE02_38 u) (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ)) (𝓝 L) →
        L - (n:ℂ) * (Real.pi:ℂ) = Complex.I * (actualGapHeightE02_38 u x : ℂ))
    (hKa : ∃ C r : ℝ, 0 < r ∧ ∀ z : ℂ, 0 < z.im → ‖z - a‖ < r →
      ‖actualQuasimomentumE02_38 u z - n*Real.pi‖^2 ≤ C * ‖z - a‖)
    (hKb : ∃ C r : ℝ, 0 < r ∧ ∀ z : ℂ, 0 < z.im → ‖z - b‖ < r →
      ‖actualQuasimomentumE02_38 u z - n*Real.pi‖^2 ≤ C * ‖z - b‖)
    (hD1 : 1 < ‖actualPhysicalUnitHalfTrace32 u (x₀:ℂ)‖) :
    gapSemicircle a b x₀ ≤ actualGapHeightE02_38 u x₀ := by
  have hab : a < b := lt_trans hx₀.1 hx₀.2
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hU
  set k := actualQuasimomentumE02_38 u with hk_def
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  set p₀ : ℂ := (n:ℂ) * (Real.pi:ℂ) with hp₀
  have hp₀' : p₀ = (((n:ℝ)*Real.pi : ℝ) : ℂ) := by rw [hp₀]; push_cast; ring
  set σ₀ := Real.sqrt ((x₀ - a)*(b - x₀)) with hσ₀
  have hσ₀pos : 0 < σ₀ := Real.sqrt_pos.mpr (mul_pos (by linarith [hx₀.1]) (by linarith [hx₀.2]))
  set v₀ := actualGapHeightE02_38 u x₀
  set c : ℝ := v₀/σ₀ with hc
  set s := gapSqrt a b with hs_def
  let G : ℂ → ℂ := fun z => (k z - p₀)/s z
  let Φ : ℂ → ℂ := fun z => (G z - (c:ℂ))/(z - (x₀:ℂ))
  have hcut : ∀ z ∈ U, z ∈ (((↑) : ℝ → ℂ) '' Set.Icc a b)ᶜ := by
    rintro z hz ⟨t, -, rfl⟩
    have : (0:ℝ) < ((t:ℂ)).im := hz
    simp at this
  have hs0 : ∀ z ∈ U, s z ≠ 0 := by
    intro z hz h
    have h1 : 0 < (s z).im := gapSqrt_im_pos hab.le hz
    rw [h] at h1; simp at h1
  have hzx : ∀ z ∈ U, z - (x₀:ℂ) ≠ 0 := by
    intro z hz h
    have h1 := congrArg Complex.im h
    have h2 : (0:ℝ) < z.im := hz
    simp at h1; linarith
  -- (a) differentiability
  have hΦd : DifferentiableOn ℂ Φ U := by
    intro z hz
    have hkd : DifferentiableAt ℂ k z := (hk.1 z hz).differentiableAt
    have hsd : DifferentiableAt ℂ s z :=
      (differentiableOn_gapSqrt hab.le).differentiableAt
        ((isOpen_gapCut_compl a b).mem_nhds (hcut z hz))
    exact ((((hkd.sub_const p₀).div hsd (hs0 z hz)).sub_const (c:ℂ)).div
      (differentiableAt_id.sub_const (x₀:ℂ)) (hzx z hz)).differentiableWithinAt
  -- (b) boundary limits off E
  have hlim : ∀ x : ℝ, x ∉ ({a, b, x₀} : Finset ℝ) →
      ∃ y : ℂ, Tendsto Φ (𝓝[U] (x:ℂ)) (𝓝 y) ∧ 0 ≤ y.im := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    obtain ⟨hxa, hxb, hxx₀⟩ := hx
    obtain ⟨L, hL, -, -⟩ := exists_tendsto_actualQuasimomentum_boundary_E02_38 u x
    have hLim := boundaryLimit_im_E02_38 u x L hL
    have hxne : ((x:ℂ) - (x₀:ℂ)) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hxx₀
    have hid : Tendsto (fun z : ℂ => z - (x₀:ℂ)) (𝓝[U] (x:ℂ)) (𝓝 ((x:ℂ) - (x₀:ℂ))) :=
      ((continuous_id.sub continuous_const).tendsto _).mono_left nhdsWithin_le_nhds
    by_cases hin : x ∈ Set.Ioo a b
    · have hxg : x ∈ Set.Ioo a b := hin
      have hsl := tendsto_gapSqrt_nhdsWithin_cut_E02_38 hin
      set σ := Real.sqrt ((x - a)*(b - x))
      have hσ : 0 < σ := Real.sqrt_pos.mpr (mul_pos (by linarith [hin.1]) (by linarith [hin.2]))
      have hne : Complex.I * (σ:ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hσ.ne')
      refine ⟨((L - p₀)/(Complex.I * (σ:ℂ)) - (c:ℂ))/((x:ℂ) - (x₀:ℂ)), ?_, ?_⟩
      · exact (((hL.sub_const p₀).div hsl hne).sub_const (c:ℂ)).div hid hxne
      · rw [hgapL x hxg L hL, mul_div_mul_left _ _ Complex.I_ne_zero]
        have : ((actualGapHeightE02_38 u x : ℂ)/(σ:ℂ) - (c:ℂ))/((x:ℂ) - (x₀:ℂ)) =
            (((actualGapHeightE02_38 u x/σ - c)/(x - x₀) : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_im]
    · have hout : x < a ∨ b < x := by
        simp only [Set.mem_Ioo, not_and_or, not_lt] at hin
        rcases hin with h | h
        · left; exact lt_of_le_of_ne h hxa
        · right; exact lt_of_le_of_ne h (Ne.symm hxb)
      obtain ⟨r, hr, hsx⟩ := gapSqrt_real hab.le x hout
      have hxcut : (x:ℂ) ∈ (((↑) : ℝ → ℂ) '' Set.Icc a b)ᶜ := by
        rintro ⟨t, ht, htx⟩
        have : t = x := by exact_mod_cast htx
        rcases hout with h | h <;> [linarith [ht.1, this]; linarith [ht.2, this]]
      have hsc : Tendsto s (𝓝[U] (x:ℂ)) (𝓝 (s x)) :=
        (((differentiableOn_gapSqrt hab.le).differentiableAt
          ((isOpen_gapCut_compl a b).mem_nhds hxcut)).continuousAt.tendsto).mono_left
          nhdsWithin_le_nhds
      have hrr : (x - b) * r ≠ 0 := by
        apply mul_ne_zero _ hr.ne'
        rcases hout with h | h <;> [linarith [hab]; linarith]
      have hsx0 : s x ≠ 0 := by rw [hs_def, hsx]; exact_mod_cast hrr
      refine ⟨((L - p₀)/(s x) - (c:ℂ))/((x:ℂ) - (x₀:ℂ)), ?_, ?_⟩
      · exact (((hL.sub_const p₀).div hsc hsx0).sub_const (c:ℂ)).div hid hxne
      · rw [show s x = (((x - b) * r : ℝ) : ℂ) from hsx,
          show (x:ℂ) - (x₀:ℂ) = ((x - x₀ : ℝ) : ℂ) by push_cast; ring,
          im_div_ofReal_sub_div_E02_38 _ _ _ _ hrr (by
            intro h; apply hxx₀; linarith)]
        have hLp : (L - p₀).im = actualGapHeightE02_38 u x := by
          rw [Complex.sub_im, hLim, hp₀', Complex.ofReal_im, sub_zero]
        rw [hLp]
        apply div_nonneg (actualGapHeightE02_38_nonneg u x)
        rcases hout with h | h
        · have h1 : x - b < 0 := by linarith
          have h2 : x - x₀ < 0 := by linarith [hx₀.1]
          nlinarith [mul_neg_of_neg_of_pos h1 hr]
        · have h1 : 0 < x - b := by linarith
          have h2 : 0 < x - x₀ := by linarith [hx₀.2]
          positivity
  -- (c) boundedness near the exceptional points
  have hbdd : ∀ e ∈ ({a, b, x₀} : Finset ℝ), ∃ r > 0, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im →
      ‖z - (e:ℂ)‖ < r → ‖Φ z‖ ≤ M := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    have hsqa : ∀ z : ℂ, ‖s z‖^2 = ‖z - a‖*‖z - b‖ := by
      intro z; rw [← norm_pow, hs_def, gapSqrt_sq, norm_mul]
    rcases he with he | he | he
    · rw [he]
      obtain ⟨C, r, hr, hK6⟩ := hKa
      exact bounded_near_endpoint_E02_38 k a b a b x₀ p₀ c C r hr hK6 hsqa
        (min (b - a) (x₀ - a)) (lt_min (by linarith) (by linarith [hx₀.1]))
        (by rw [abs_sub_comm, abs_of_pos (by linarith)]; exact min_le_left _ _)
        (by rw [abs_sub_comm, abs_of_pos (by linarith [hx₀.1])]; exact min_le_right _ _)
    · rw [he]
      obtain ⟨C, r, hr, hK6⟩ := hKb
      exact bounded_near_endpoint_E02_38 k a b b a x₀ p₀ c C r hr hK6
        (fun z => by rw [hsqa, mul_comm])
        (min (b - a) (b - x₀)) (lt_min (by linarith) (by linarith [hx₀.2]))
        (by rw [abs_of_pos (by linarith)]; exact min_le_left _ _)
        (by rw [abs_of_pos (by linarith [hx₀.2])]; exact min_le_right _ _)
    · rw [he]
      -- interior point x₀: analytic continuation
      have hD2 : actualPhysicalUnitHalfTrace32 u (x₀:ℂ) ^ 2 ≠ 1 := by
        intro h
        have := congrArg norm h
        rw [norm_pow, norm_one] at this
        nlinarith [norm_nonneg (actualPhysicalUnitHalfTrace32 u (x₀:ℂ))]
      obtain ⟨r₁, hr₁, K, hKan, hKeq⟩ :=
        exists_analytic_continuation_actualQuasimomentum_E02_38 u x₀ hD2
      obtain ⟨r₂, hr₂, hslit, hseq⟩ := gapSqrt_eq_I_mul_cpow_near_cut_E02_38 hx₀
      let S : ℂ → ℂ := fun z => Complex.I * (-((z - a) * (z - b))) ^ (2⁻¹ : ℂ)
      have hx₀b1 : (x₀:ℂ) ∈ Metric.ball (x₀:ℂ) r₁ := Metric.mem_ball_self hr₁
      have hx₀b2 : (x₀:ℂ) ∈ Metric.ball (x₀:ℂ) r₂ := Metric.mem_ball_self hr₂
      have hKd : DifferentiableAt ℂ K (x₀:ℂ) := (hKan _ hx₀b1).differentiableAt
      have hSd : DifferentiableAt ℂ S (x₀:ℂ) := by
        have hq : DifferentiableAt ℂ (fun z : ℂ => -((z - (a:ℂ)) * (z - (b:ℂ)))) (x₀:ℂ) := by
          fun_prop
        exact (differentiableAt_const _).mul (hq.cpow (differentiableAt_const _) (hslit _ hx₀b2))
      have hSx : S (x₀:ℂ) = Complex.I * (σ₀:ℂ) := I_mul_cpow_at_cut_E02_38 hx₀
      have hS0 : S (x₀:ℂ) ≠ 0 := by
        rw [hSx]; exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hσ₀pos.ne')
      -- value of K at x₀
      have hKlim : Tendsto k (𝓝[U] (x₀:ℂ)) (𝓝 (K x₀)) := by
        have h1 : Tendsto K (𝓝[U] (x₀:ℂ)) (𝓝 (K x₀)) :=
          hKd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        refine h1.congr' ?_
        have hb : U ∩ Metric.ball (x₀:ℂ) r₁ ∈ 𝓝[U] (x₀:ℂ) :=
          inter_mem_nhdsWithin U (Metric.ball_mem_nhds _ hr₁)
        filter_upwards [hb] with z hz
        exact hKeq z hz.2 hz.1
      have hKx : K (x₀:ℂ) - p₀ = Complex.I * (v₀:ℂ) := hgapL x₀ hx₀ _ hKlim
      let Gt : ℂ → ℂ := fun z => (K z - p₀)/S z
      have hGtd : DifferentiableAt ℂ Gt (x₀:ℂ) := (hKd.sub_const p₀).div hSd hS0
      have hGtx : Gt (x₀:ℂ) = (c:ℂ) := by
        show (K (x₀:ℂ) - p₀)/S (x₀:ℂ) = (c:ℂ)
        rw [hKx, hSx, mul_div_mul_left _ _ Complex.I_ne_zero, hc]; push_cast; ring
      obtain ⟨C', hC'⟩ := hGtd.hasDerivAt.isBigO_sub.bound
      obtain ⟨r₃, hr₃, hball3⟩ := Metric.eventually_nhds_iff.mp hC'
      refine ⟨min r₁ (min r₂ r₃), lt_min hr₁ (lt_min hr₂ hr₃), C', ?_⟩
      intro z hz hzr
      have hz1 : z ∈ Metric.ball (x₀:ℂ) r₁ := by
        rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hzr (min_le_left _ _)
      have hz2 : z ∈ Metric.ball (x₀:ℂ) r₂ := by
        rw [Metric.mem_ball, dist_eq_norm]
        exact lt_of_lt_of_le hzr (le_trans (min_le_right _ _) (min_le_left _ _))
      have hz3 : dist z (x₀:ℂ) < r₃ := by
        rw [dist_eq_norm]
        exact lt_of_lt_of_le hzr (le_trans (min_le_right _ _) (min_le_right _ _))
      have hGeq : G z = Gt z := by
        show (k z - p₀)/s z = (K z - p₀)/S z
        rw [hKeq z hz1 hz, hs_def, hseq z hz2 hz]
      have hb3 := hball3 hz3
      show ‖(G z - (c:ℂ))/(z - (x₀:ℂ))‖ ≤ C'
      rw [hGeq, ← hGtx, norm_div, div_le_iff₀ (norm_pos_iff.mpr (hzx z hz))]
      simpa using hb3
  -- (d) decay at infinity
  obtain ⟨B, R₀, hB, hR₀, hGinf⟩ := exists_G_sub_one_le_E02_38 k
    (actualQuasimomentumE02_38_sub_tendsto_zero u) a b p₀
  have hinf : ∀ ε > 0, ∃ R : ℝ, ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ → ‖Φ z‖ < ε := by
    intro ε hε
    set A : ℝ := 1 + B/R₀ + |c|
    refine ⟨max R₀ (|x₀| + 2*A/ε + 1), ?_⟩
    intro z hz hzR
    have hz1 : R₀ ≤ ‖z‖ := le_trans (le_max_left _ _) hzR
    have hz2 : |x₀| + 2*A/ε + 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hzR
    obtain ⟨-, hG1⟩ := hGinf z hz hz1
    have hGb : ‖G z‖ ≤ 1 + B/R₀ := by
      have h1 : ‖G z‖ ≤ ‖G z - 1‖ + 1 := by
        have := norm_le_insert' (G z) 1; simpa [add_comm] using this
      have h2 : B/‖z‖ ≤ B/R₀ := div_le_div_of_nonneg_left hB hR₀ hz1
      linarith
    have hA : 0 < A := by positivity
    have hden : 2*A/ε + 1 ≤ ‖z - (x₀:ℂ)‖ := by
      have := norm_sub_norm_le z (x₀:ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have hdpos : 0 < ‖z - (x₀:ℂ)‖ := lt_of_lt_of_le (by positivity) hden
    show ‖(G z - (c:ℂ))/(z - (x₀:ℂ))‖ < ε
    rw [norm_div, div_lt_iff₀ hdpos]
    have hnum : ‖G z - (c:ℂ)‖ ≤ A := by
      calc ‖G z - (c:ℂ)‖ ≤ ‖G z‖ + ‖(c:ℂ)‖ := norm_sub_le _ _
        _ ≤ A := by rw [Complex.norm_real, Real.norm_eq_abs]; simp only [A]; linarith
    have : A < ε * (2*A/ε + 1) := by
      rw [mul_add, mul_div_assoc', mul_comm ε (2*A), mul_div_assoc, div_self hε.ne', mul_one]
      linarith
    nlinarith
  -- (e) minimum principle and conclusion
  have hIm := halfPlane_im_nonneg_of_boundary_limits_E02_38 Φ {a, b, x₀} hΦd hlim hbdd hinf
  have hc1 : 1 ≤ c := by
    apply one_le_of_im_quotient_nonneg_E02_38 G c x₀ B R₀ hB hR₀
    · intro y hy
      have hz : 0 < (Complex.I*(y:ℂ)).im := by simp; linarith
      have hn : ‖Complex.I*(y:ℂ)‖ = y := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
      have := (hGinf _ hz (by rw [hn]; exact hy)).2
      rwa [hn] at this
    · intro y hy
      exact hIm (Complex.I*(y:ℂ)) (by simpa using hy)
  have : σ₀ ≤ v₀ := by
    rw [hc, le_div_iff₀ hσ₀pos, one_mul] at hc1; exact hc1
  simpa [gapSemicircle, hσ₀] using this

/-- NEW-E01.01 on an open labelled gap: `v(x₀) ≥ √((x₀-λ⁻)(λ⁺-x₀))`. -/
theorem actualGapHeight_ge_semicircle_open_E02_38 (u : PhysicalL2) (n : ℤ) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/1000) (hbox : ActualHalfTraceBoxE02_38 u n δ)
    (hwin : ActualQuasimomentumWindowE02_38 u n)
    (x₀ : ℝ) (hx₀ : x₀ ∈ actualGapE02_38 u n) :
    gapSemicircle (actualGapLowerE02_38 u n) (actualGapUpperE02_38 u n) x₀ ≤
      actualGapHeightE02_38 u x₀ := by
  obtain ⟨hlr, hla, hlb, hDa, hDb, hset, hone⟩ :=
    actualGapStructureE02_38 u n δ hδ0 hδ hbox hwin
  have hδ8 : 2*Real.sqrt δ ≤ 1/8 := by
    have : Real.sqrt δ ≤ Real.sqrt (1/256) := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (1/256) = 1/16 := by
      rw [show (1:ℝ)/256 = (1/16)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hp₀' : (n:ℂ) * (Real.pi:ℂ) = (((n:ℝ)*Real.pi : ℝ) : ℂ) := by push_cast; ring
  apply gapHeight_ge_semicircle_generic_E02_38 u n _ _ x₀ hx₀
  · intro x hx L hL
    have hre := boundaryLimit_re_gap_E02_38 u n δ hδ0 hδ hbox hwin x hx L hL
    have him := boundaryLimit_im_E02_38 u x L hL
    rw [hp₀']
    apply Complex.ext <;> simp [hre, him]
  · exact actualQuasimomentum_sub_sq_le_E02_38 u n _ hDa (le_trans hla hδ8) hwin
  · exact actualQuasimomentum_sub_sq_le_E02_38 u n _ hDb (le_trans hlb hδ8) hwin
  · have : x₀ ∈ {x : ℝ | x ∈ Set.Icc ((n:ℝ)*Real.pi - 1/2) ((n:ℝ)*Real.pi + 1/2) ∧
        1 < ‖actualPhysicalUnitHalfTrace32 u (x:ℂ)‖} := by rw [hset]; exact hx₀
    exact this.2

/-- NEW-E01.01 on the closed labelled gap (endpoints and closed gaps included). -/
theorem actualGapHeight_ge_semicircle_E02_38 (u : PhysicalL2) (n : ℤ) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/1000) (hbox : ActualHalfTraceBoxE02_38 u n δ)
    (hwin : ActualQuasimomentumWindowE02_38 u n) :
    ∀ x ∈ Set.Icc (actualGapLowerE02_38 u n) (actualGapUpperE02_38 u n),
      gapSemicircle (actualGapLowerE02_38 u n) (actualGapUpperE02_38 u n) x ≤
        actualGapHeightE02_38 u x := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h]; simp [gapSemicircle, actualGapHeightE02_38_nonneg]
  rcases eq_or_lt_of_le hx.2 with h' | h'
  · rw [h']; simp [gapSemicircle, actualGapHeightE02_38_nonneg]
  exact actualGapHeight_ge_semicircle_open_E02_38 u n δ hδ0 hδ hbox hwin x ⟨h, h'⟩

/-- NEW-E01 (exact constant, closed gaps included) for the labelled gaps under the box and
window hypotheses: `I_n ≥ |g_n|²/4` with `I_n = (2/π)∫_{g_n} v`. -/
theorem actualGapAction_ge_sq_div_four_E02_38 (u : PhysicalL2) (n : ℤ) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/1000) (hbox : ActualHalfTraceBoxE02_38 u n δ)
    (hwin : ActualQuasimomentumWindowE02_38 u n) :
    (actualGapUpperE02_38 u n - actualGapLowerE02_38 u n)^2 / 4 ≤
      actualGapActionE02_38 u n :=
  actualGapAction_lowerBound_of_semicircle_E02_38 u n
    (actualGapStructureE02_38 u n δ hδ0 hδ hbox hwin).1
    (actualGapHeight_ge_semicircle_E02_38 u n δ hδ0 hδ hbox hwin)

/-- Realized form: for every rough `u` there is `N(u)` such that all labelled gaps with
`|n| ≥ N(u)` satisfy `I_n ≥ |g_n|²/4`. -/
theorem exists_actualGapAction_ge_sq_div_four_E02_38 (u : PhysicalL2) :
    ∃ N : ℝ, ∀ n : ℤ, N ≤ |(n:ℝ)| →
      (actualGapUpperE02_38 u n - actualGapLowerE02_38 u n)^2 / 4 ≤
        actualGapActionE02_38 u n := by
  obtain ⟨N, hN⟩ := exists_actualHalfTraceBox_window_E02_38 u (1/1000) (by norm_num)
  exact ⟨N, fun n hn => actualGapAction_ge_sq_div_four_E02_38 u n (1/1000) (by norm_num) le_rfl
    (hN n hn).1 (hN n hn).2⟩

end NlsGge.SpectralFoundations
end
