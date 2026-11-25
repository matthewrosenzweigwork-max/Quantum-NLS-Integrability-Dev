import NlsGge.GK38.TauGammaExterior
import NlsGge.GK38.Lib.EntireProductsC34h

/-! The squared removable sinc has a single translated entire profile and vanishing central derivative. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

def sincSquareProfile38 (z : ℂ) : ℂ := (Lib.omitProd 0 0 z) ^ 2

theorem sincSquareProfile_entire38 : AnalyticOnNhd ℂ sincSquareProfile38 univ :=
  fun z _ => (Lib.analyticAt_omitProd_line 0 0 z).pow 2

theorem sincSquareProfile_zero38 : sincSquareProfile38 0 = 1 := by
  have h := Lib.omitProd_zero_at_root 0
  norm_num at h
  simp [sincSquareProfile38, h]

theorem sincSquareProfile_even38 (z : ℂ) : sincSquareProfile38 (-z) = sincSquareProfile38 z := by
  unfold sincSquareProfile38
  rw [Lib.omitProd_zero_eq_sincAt, Lib.omitProd_zero_eq_sincAt]
  by_cases hz : z = 0
  · subst z
    simp
  · simp [Lib.sincAt, hz, Complex.sin_neg]

theorem sincSquareProfile_deriv_zero38 : deriv sincSquareProfile38 0 = 0 := by
  have h := (sincSquareProfile_entire38 0 (mem_univ _)).differentiableAt.hasDerivAt
  have houter : HasDerivAt sincSquareProfile38 (deriv sincSquareProfile38 0) (-(0 : ℂ)) := by
    simpa only [neg_zero] using h
  have hc : HasDerivAt (fun z : ℂ => sincSquareProfile38 (-z))
      (deriv sincSquareProfile38 0 * (-1)) 0 :=
    houter.comp 0 ((hasDerivAt_id (0 : ℂ)).neg)
  have he : (fun z => sincSquareProfile38 (-z)) = sincSquareProfile38 :=
    funext sincSquareProfile_even38
  rw [he] at hc
  have hd := hc.unique h
  linear_combination -1 / 2 * hd

theorem cos_lattice_square38 (n : ℤ) : (Complex.cos ((n : ℂ) * (Real.pi : ℂ))) ^ 2 = 1 := by
  have h := Complex.sin_sq_add_cos_sq ((n : ℂ) * (Real.pi : ℂ))
  simpa only [Complex.sin_int_mul_pi, zero_pow (by decide : 2 ≠ 0), zero_add] using h

theorem sincAt_square_translate38 (n : ℤ) (z : ℂ) :
    (Lib.sincAt n z) ^ 2 = sincSquareProfile38 (z - (n : ℂ) * (Real.pi : ℂ)) := by
  unfold sincSquareProfile38
  rw [Lib.omitProd_zero_eq_sincAt]
  have hcn : (((n : ℝ) * Real.pi : ℝ) : ℂ) = (n : ℂ) * (Real.pi : ℂ) := by simp
  have hcos : ((Real.cos ((n : ℝ) * Real.pi) : ℂ)) ^ 2 = 1 := by
    rw [Complex.ofReal_cos, hcn]
    exact cos_lattice_square38 n
  by_cases hz : z = (n : ℂ) * (Real.pi : ℂ)
  · subst z
    simpa only [Lib.sincAt, ite_true, sub_self, Int.cast_zero, zero_mul, Real.cos_zero,
      Complex.ofReal_one, one_pow] using hcos
  · have hη : z - (n : ℂ) * (Real.pi : ℂ) ≠ 0 := sub_ne_zero.mpr hz
    have hs : Complex.sin z = Complex.sin (z - (n : ℂ) * (Real.pi : ℂ)) *
        Complex.cos ((n : ℂ) * (Real.pi : ℂ)) := by
      have h := Complex.sin_add (z - (n : ℂ) * (Real.pi : ℂ)) ((n : ℂ) * (Real.pi : ℂ))
      simpa only [sub_add_cancel, Complex.sin_int_mul_pi, mul_zero, add_zero] using h
    simp only [Lib.sincAt, hz, hη, ite_false, Int.cast_zero, zero_mul, sub_zero, hs,
      div_pow, mul_pow, cos_lattice_square38, mul_one]

theorem sincSquareProfile_local_bounds38 : ∃ K : ℝ, 0 < K ∧ ∀ z ∈ ball (0 : ℂ) (Real.pi / 4),
    ‖sincSquareProfile38 z - 1‖ ≤ K * ‖z‖ ∧ ‖deriv sincSquareProfile38 z‖ ≤ K * ‖z‖ := by
  have hG := sincSquareProfile_entire38
  obtain ⟨B₁, hB₁⟩ := (isCompact_closedBall (0 : ℂ) (Real.pi / 4)).exists_bound_of_continuousOn
    (hG.deriv.continuousOn.mono (subset_univ _))
  obtain ⟨B₂, hB₂⟩ := (isCompact_closedBall (0 : ℂ) (Real.pi / 4)).exists_bound_of_continuousOn
    (hG.deriv.deriv.continuousOn.mono (subset_univ _))
  let K := max 0 (max B₁ B₂) + 1
  have hK : 0 < K := by dsimp [K]; linarith [le_max_left 0 (max B₁ B₂)]
  have h₁ : B₁ ≤ K := by dsimp [K]; linarith [le_max_left B₁ B₂, le_max_right 0 (max B₁ B₂)]
  have h₂ : B₂ ≤ K := by dsimp [K]; linarith [le_max_right B₁ B₂, le_max_right 0 (max B₁ B₂)]
  have h0 : (0 : ℂ) ∈ closedBall 0 (Real.pi / 4) := mem_closedBall_self (by positivity)
  refine ⟨K, hK, fun z hz => ?_⟩
  have hfirst := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun w _ => (hG w (mem_univ _)).differentiableAt) (fun w hw => (hB₁ w hw).trans h₁)
    (convex_closedBall (0 : ℂ) (Real.pi / 4)) h0 (ball_subset_closedBall hz)
  have hsecond := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun w _ => (hG.deriv w (mem_univ _)).differentiableAt) (fun w hw => (hB₂ w hw).trans h₂)
    (convex_closedBall (0 : ℂ) (Real.pi / 4)) h0 (ball_subset_closedBall hz)
  simpa only [sincSquareProfile_zero38, sincSquareProfile_deriv_zero38, sub_zero] using
    And.intro hfirst hsecond

theorem sinc_square_inner_bound38 : ∃ K : ℝ, 0 < K ∧ ∀ n : ℤ,
    ∀ z ∈ ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4),
      ‖(Lib.sincAt n z) ^ 2 - 1‖ ≤ K * ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ∧
      ‖deriv (fun w => (Lib.sincAt n w) ^ 2) z‖ ≤ K * ‖z - (n : ℂ) * (Real.pi : ℂ)‖ := by
  obtain ⟨K, hK, hb⟩ := sincSquareProfile_local_bounds38
  refine ⟨K, hK, fun n z hz => ?_⟩
  have hη : z - (n : ℂ) * (Real.pi : ℂ) ∈ ball (0 : ℂ) (Real.pi / 4) := by
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hz
  have h := hb _ hη
  have he : (fun w => (Lib.sincAt n w) ^ 2) =
      (fun w => sincSquareProfile38 (w - (n : ℂ) * (Real.pi : ℂ))) := funext (sincAt_square_translate38 n)
  have hd := (sincSquareProfile_entire38 _ (mem_univ _)).differentiableAt.hasDerivAt.comp z
    ((hasDerivAt_id z).sub_const ((n : ℂ) * (Real.pi : ℂ)))
  have heD : deriv (fun w => sincSquareProfile38 (w - (n : ℂ) * (Real.pi : ℂ))) z =
      deriv sincSquareProfile38 (z - (n : ℂ) * (Real.pi : ℂ)) := by
    simpa only [Function.comp_def, id_eq, mul_one] using hd.deriv
  rw [sincAt_square_translate38, he, heD]
  exact h

end
end NlsGge.GK38
