import NlsGge.Spectral.ActualQuasimomentumE02_38
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot

/-- Complex sine is within `‖ζ‖²` of `ζ` for `‖ζ‖ ≤ 1`. -/
theorem complex_norm_sin_sub_self_le_E02_38 (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) :
    ‖Complex.sin ζ - ζ‖ ≤ ‖ζ‖ ^ 2 := by
  have h1 := Complex.norm_exp_sub_one_sub_id_le (x := ζ * Complex.I)
    (by simpa using hζ)
  have h2 := Complex.norm_exp_sub_one_sub_id_le (x := -ζ * Complex.I)
    (by simpa using hζ)
  have key : (2 : ℂ) * (Complex.sin ζ - ζ) =
      ((Complex.exp (-ζ * Complex.I) - 1 - (-ζ * Complex.I)) -
        (Complex.exp (ζ * Complex.I) - 1 - ζ * Complex.I)) * Complex.I := by
    rw [mul_sub, Complex.two_sin]
    have : (-ζ * Complex.I) = -(ζ * Complex.I) := by ring
    rw [this]
    ring_nf
    simp [Complex.I_sq]
  have hn : ‖(2 : ℂ)‖ * ‖Complex.sin ζ - ζ‖ ≤ 2 * ‖ζ‖ ^ 2 := by
    rw [← norm_mul, key, norm_mul, Complex.norm_I, mul_one]
    calc _ ≤ ‖Complex.exp (-ζ * Complex.I) - 1 - (-ζ * Complex.I)‖ +
          ‖Complex.exp (ζ * Complex.I) - 1 - ζ * Complex.I‖ := norm_sub_le _ _
      _ ≤ _ := by
        simp only [norm_mul, norm_neg, Complex.norm_I, mul_one] at h1 h2 ⊢
        linarith
  simp at hn
  linarith

theorem complex_norm_sin_ge_half_E02_38 (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1 / 2) :
    ‖ζ‖ / 2 ≤ ‖Complex.sin ζ‖ := by
  have h := complex_norm_sin_sub_self_le_E02_38 ζ (by linarith)
  have h2 : ‖ζ‖ - ‖Complex.sin ζ‖ ≤ ‖Complex.sin ζ - ζ‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le _ _
  have h0 := norm_nonneg ζ
  nlinarith

theorem complex_norm_sq_le_eight_norm_one_sub_cos_E02_38 (w : ℂ) (hw : ‖w‖ ≤ 1) :
    ‖w‖ ^ 2 ≤ 8 * ‖1 - Complex.cos w‖ := by
  have hc : 1 - Complex.cos w = 2 * Complex.sin (w / 2) ^ 2 := by
    have := Complex.cos_two_mul (w / 2)
    have h2 := Complex.sin_sq_add_cos_sq (w / 2)
    rw [show 2 * (w / 2) = w by ring] at this
    rw [this]; linear_combination (-2 : ℂ) * h2
  have hs := complex_norm_sin_ge_half_E02_38 (w / 2) (by
    rw [norm_div]; simp; linarith)
  rw [hc, norm_mul, norm_pow]
  rw [norm_div] at hs
  simp only [Complex.norm_ofNat] at hs ⊢
  have h0 := norm_nonneg w
  nlinarith

theorem actualQuasimomentum_sub_sq_le_E02_38 (u : PhysicalL2) (n : ℤ) (a : ℝ)
    (ha : actualPhysicalUnitHalfTrace32 u a = (Real.cos (n*Real.pi) : ℂ))
    (han : |a - n*Real.pi| ≤ 1/8)
    (hwin : ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re - n*Real.pi| ≤ 1/2 →
      ‖actualQuasimomentumE02_38 u z - z‖ < 1/4) :
    ∃ C r : ℝ, 0 < r ∧ ∀ z : ℂ, 0 < z.im → ‖z - a‖ < r →
      ‖actualQuasimomentumE02_38 u z - n*Real.pi‖^2 ≤ C * ‖z - a‖ := by
  have hdiff : AnalyticAt ℂ (actualPhysicalUnitHalfTrace32 u) (a : ℂ) :=
    analyticOnNhd_actualPhysicalUnitHalfTrace32 u _ (Set.mem_univ _)
  have hC1 : ContDiffAt ℝ 1 (actualPhysicalUnitHalfTrace32 u) (a : ℂ) :=
    ((hdiff.contDiffAt (n := 1)).restrict_scalars ℝ)
  obtain ⟨K, t, ht, hK⟩ := hC1.exists_lipschitzOnWith
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨8 * (K : ℝ), min ε (1/8), lt_min hε (by norm_num), ?_⟩
  intro z hz hza
  have hza1 : ‖z - a‖ < ε := lt_of_lt_of_le hza (min_le_left _ _)
  have hza2 : ‖z - a‖ < 1/8 := lt_of_lt_of_le hza (min_le_right _ _)
  have hzt : z ∈ t := hεt (by simpa [Metric.mem_ball, dist_eq_norm] using hza1)
  have hat : (a : ℂ) ∈ t := hεt (Metric.mem_ball_self hε)
  have hLip : ‖actualPhysicalUnitHalfTrace32 u z - actualPhysicalUnitHalfTrace32 u a‖ ≤
      K * ‖z - a‖ := by
    have := hK.norm_sub_le hzt hat
    simpa using this
  -- norms
  have him : |z.im| ≤ ‖z - a‖ := by
    have := Complex.abs_im_le_norm (z - (a : ℂ))
    simpa using this
  have hre : |z.re - a| ≤ ‖z - a‖ := by
    have := Complex.abs_re_le_norm (z - (a : ℂ))
    simpa using this
  have hz1 : z.im ≤ 1 := by
    have := le_abs_self z.im; linarith
  have hzre : |z.re - n * Real.pi| ≤ 1/2 := by
    have : |z.re - n * Real.pi| ≤ |z.re - a| + |a - n * Real.pi| := by
      have := abs_add_le (z.re - a) (a - n * Real.pi)
      simpa using this
    linarith
  have hk := hwin z hz hz1 hzre
  have hznp : ‖z - (n * Real.pi : ℝ)‖ ≤ 1/4 := by
    have h1 : ‖z - (n * Real.pi : ℝ)‖ ≤ ‖z - a‖ + ‖(a : ℂ) - (n * Real.pi : ℝ)‖ := by
      have := norm_add_le (z - (a : ℂ)) ((a : ℂ) - (n * Real.pi : ℝ))
      simpa using this
    have h2 : ‖(a : ℂ) - (n * Real.pi : ℝ)‖ = |a - n * Real.pi| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    linarith
  set k := actualQuasimomentumE02_38 u z with hkdef
  have hw : ‖k - ((n * Real.pi : ℝ) : ℂ)‖ ≤ 1 := by
    have : ‖k - ((n * Real.pi : ℝ) : ℂ)‖ ≤ ‖k - z‖ + ‖z - (n * Real.pi : ℝ)‖ := by
      have := norm_add_le (k - z) (z - ((n * Real.pi : ℝ) : ℂ))
      simpa using this
    linarith
  have hcos := (isActualQuasimomentumBranch_actualQuasimomentumE02_38 u).2.1 z hz
  have hsin : Complex.sin ((n * Real.pi : ℝ) : ℂ) = 0 := by
    rw [← Complex.ofReal_sin]
    have : Real.sin (n * Real.pi) = 0 := Real.sin_int_mul_pi n
    simp [this]
  have hcw : Complex.cos (k - ((n * Real.pi : ℝ) : ℂ)) =
      actualPhysicalUnitHalfTrace32 u z * (Real.cos (n * Real.pi) : ℂ) := by
    rw [Complex.cos_sub, hsin, mul_zero, add_zero]
    rw [show Complex.cos k = actualPhysicalUnitHalfTrace32 u z from hcos]
    rw [← Complex.ofReal_cos]
  have hcsq : (Real.cos (n * Real.pi) : ℂ) * (Real.cos (n * Real.pi) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← sq, Real.cos_sq', Real.sin_int_mul_pi]
    simp
  have h1c : 1 - Complex.cos (k - ((n * Real.pi : ℝ) : ℂ)) =
      (actualPhysicalUnitHalfTrace32 u a - actualPhysicalUnitHalfTrace32 u z) *
        (Real.cos (n * Real.pi) : ℂ) := by
    rw [hcw, ha]
    linear_combination (-1 : ℂ) * hcsq
  have hnc : ‖(Real.cos (n * Real.pi) : ℂ)‖ = 1 := by
    have : ‖(Real.cos (n * Real.pi) : ℂ)‖ ^ 2 = 1 := by
      rw [sq, ← norm_mul, hcsq]; simp
    nlinarith [norm_nonneg (Real.cos (n * Real.pi) : ℂ)]
  have hmain := complex_norm_sq_le_eight_norm_one_sub_cos_E02_38 _ hw
  rw [h1c, norm_mul, hnc, mul_one,
    norm_sub_rev (actualPhysicalUnitHalfTrace32 u (a : ℂ))] at hmain
  have e : ((n * Real.pi : ℝ) : ℂ) = (n : ℂ) * (Real.pi : ℂ) := by push_cast; ring
  rw [e] at hmain
  have hL : ‖actualPhysicalUnitHalfTrace32 u z - actualPhysicalUnitHalfTrace32 u (a : ℂ)‖ ≤
      (K : ℝ) * ‖z - (a : ℂ)‖ := hLip
  calc _ ≤ _ := hmain
    _ ≤ 8 * ((K : ℝ) * ‖z - (a : ℂ)‖) := by linarith
    _ = 8 * (K : ℝ) * ‖z - (a : ℂ)‖ := by ring

end NlsGge.SpectralFoundations
