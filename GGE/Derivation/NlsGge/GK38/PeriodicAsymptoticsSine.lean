import NlsGge.GK38.PairAsymptoticsSine

/-! # S3: elementary sine estimates on a complex quarter disc

Local ingredients for book Lemma 6.5 and Proposition 6.7. The constant is
explicit and applies at zero and on the boundary, without a quotient. -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

/-- A uniform inverse-sine bound on the closed complex quarter disc. -/
theorem norm_le_quarter_sine38 (η : ℂ) (hη : ‖η‖ ≤ Real.pi / 4) :
    ‖η‖ ≤ (Real.pi / 2 + 1) * ‖Complex.sin η‖ := by
  have hre : |η.re| ≤ Real.pi / 2 :=
    (Complex.abs_re_le_norm η).trans (hη.trans (by linarith [Real.pi_pos]))
  have hc := (Real.mul_abs_le_abs_sin hre).trans (abs_real_sin_le_complex_sin38 η)
  have hr : |η.re| ≤ Real.pi / 2 * ‖Complex.sin η‖ := by
    have hp := Real.pi_pos
    have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ Real.pi / 2 by positivity)
    have he : Real.pi / 2 * (2 / Real.pi * |η.re|) = |η.re| := by field_simp
    rw [he] at hh
    exact hh
  have hi : |η.im| ≤ ‖Complex.sin η‖ :=
    (Lib.abs_le_abs_sinh η.im).trans (by
      simpa only [Real.abs_sinh] using sinh_abs_im_le_complex_sin38 η)
  calc ‖η‖ ≤ |η.re| + |η.im| := Complex.norm_le_abs_re_add_abs_im η
    _ ≤ Real.pi / 2 * ‖Complex.sin η‖ + ‖Complex.sin η‖ := add_le_add hr hi
    _ = _ := by ring

/-- Integer lattice translation preserves the complex sine norm, for either sign of index. -/
theorem norm_sin_sub_int_pi38 (z : ℂ) (n : ℤ) :
    ‖Complex.sin (z - (n : ℂ) * (Real.pi : ℂ))‖ = ‖Complex.sin z‖ := by
  have h := Lib.normSq_sin' (z - (n : ℂ) * (Real.pi : ℂ))
  have hz := Lib.normSq_sin' z
  rw [← Complex.sq_norm] at h hz
  have hre : (z - (n : ℂ) * (Real.pi : ℂ)).re = z.re - (n : ℝ) * Real.pi := by simp
  have him : (z - (n : ℂ) * (Real.pi : ℂ)).im = z.im := by simp
  rw [hre, him] at h
  have hs := abs_sin_sub_int_pi38 z.re n
  have hsq : Real.sin (z.re - (n : ℝ) * Real.pi) ^ 2 = Real.sin z.re ^ 2 := by
    calc _ = |Real.sin (z.re - (n : ℝ) * Real.pi)| ^ 2 := (sq_abs _).symm
      _ = |Real.sin z.re| ^ 2 := congrArg (fun x : ℝ => x ^ 2) hs
      _ = _ := sq_abs _
  rw [hsq] at h
  nlinarith [norm_nonneg (Complex.sin z),
    norm_nonneg (Complex.sin (z - (n : ℂ) * (Real.pi : ℂ)))]

end
end NlsGge.GK38
