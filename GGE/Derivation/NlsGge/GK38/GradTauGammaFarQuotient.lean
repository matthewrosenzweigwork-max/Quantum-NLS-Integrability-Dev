import NlsGge.GK38.TauGamma

/-! The far-circle quotient estimate uses the actual relative periodic
characteristic asymptotic and absolute sine separation, not small L2 tails. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem k4aPerChar_lower38 (φ : PotPair) (z : ℂ)
    (he : ‖perChar φ z - (-4 * Complex.sin z ^ 2)‖ ≤ ‖Complex.sin z‖ ^ 2) :
    3 * ‖Complex.sin z‖ ^ 2 ≤ ‖perChar φ z‖ := by
  have ht : ‖(-4 : ℂ) * Complex.sin z ^ 2‖ ≤
      ‖perChar φ z - (-4 * Complex.sin z ^ 2)‖ + ‖perChar φ z‖ := by
    calc
      _ = ‖((-4 : ℂ) * Complex.sin z ^ 2 - perChar φ z) + perChar φ z‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖(-4 : ℂ) * Complex.sin z ^ 2 - perChar φ z‖ + ‖perChar φ z‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  simp only [norm_mul, norm_neg, Complex.norm_ofNat, norm_pow] at ht
  linarith

theorem k4aDiscrim_norm38 (φ : PotPair) (z : ℂ) (R d : ℝ)
    (hφ : ‖φ‖ ≤ R) (hz : |z.im| ≤ d) :
    ‖discrim φ z‖ ≤ 2 * Real.exp (d + 2 * R) := by
  have he : Real.exp (|z.im| + potL1Norm38 φ) ≤ Real.exp (d + 2 * R) :=
    Real.exp_le_exp.mpr (add_le_add hz
      ((potL1Norm38_le_two_mul φ).trans (mul_le_mul_of_nonneg_left hφ (by norm_num))))
  rw [discrim_eq]
  exact (norm_add_le _ _).trans (by
    have h0 := (norm_monodromyPair_entry_le φ z 0 0).trans he
    have h1 := (norm_monodromyPair_entry_le φ z 1 1).trans he
    linarith)

theorem k4aQuotient_far_bound38 (φ₀ : PotPair) (R d : ℝ) :
    ∃ U : Set PotPair, U ∈ nhds φ₀ ∧ ∃ T B : ℝ, 0 ≤ B ∧
      ∀ φ ∈ U, ‖φ‖ ≤ R → ∀ z : ℂ, T ≤ ‖z‖ →
        (∀ n : ℤ, Real.pi / 4 ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖) →
        |z.im| ≤ d → perChar φ z ≠ 0 ∧ ‖discrim φ z / perChar φ z‖ ≤ B := by
  obtain ⟨U, hU, T, he⟩ := perChar_asymp φ₀ 1 zero_lt_one
  let A : ℝ := 2 * Real.exp (d + 2 * R)
  let C : ℝ := sineOffDiscsConstant38
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 < C := sineOffDiscsConstant38_pos
  refine ⟨U, hU, T, A * C ^ 2 / 3, by positivity, ?_⟩
  intro φ hφ hφR z hz hsep hzd
  have hden := k4aPerChar_lower38 φ z (by simpa only [one_mul] using he φ hφ z hz hsep)
  have hsin : 1 ≤ C * ‖Complex.sin z‖ :=
    (Real.one_le_exp (abs_nonneg z.im)).trans (sine_off_discs_lower_bound38 z hsep)
  have hsinpos : 0 < ‖Complex.sin z‖ := by nlinarith
  have hp : 0 < ‖perChar φ z‖ := lt_of_lt_of_le (by positivity) hden
  have hscaled : 3 ≤ C ^ 2 * ‖perChar φ z‖ := by
    have hsquare : 1 ≤ C ^ 2 * ‖Complex.sin z‖ ^ 2 := by
      simpa only [one_pow, mul_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hsin 2
    have hh := mul_le_mul_of_nonneg_left hden (sq_nonneg C)
    nlinarith
  refine ⟨norm_pos_iff.mp hp, ?_⟩
  rw [norm_div]
  apply (div_le_iff₀ hp).mpr
  have hnum : ‖discrim φ z‖ ≤ A := k4aDiscrim_norm38 φ z R d hφR hzd
  have hh := mul_le_mul_of_nonneg_left hscaled hA
  nlinarith

end
end NlsGge.GK38
