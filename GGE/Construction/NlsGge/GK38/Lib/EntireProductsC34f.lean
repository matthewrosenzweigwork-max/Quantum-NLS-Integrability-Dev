import NlsGge.GK38.Lib.EntireProductsC34e

/-!
# L4c part 2b, module f: padded nodes for Lemma F.6

For the application of `hilbertGen_bdd` to `Σ_{m≠n} a_m/(ρ_m - λ_n)` one needs
`‖ρ_m - σ'_n‖ ≥ c' |m - n|` for **all** `n`, while (C.2) holds only for `|n| ≥ N`.  For `|n| < N` we use
`σ'_n = nπ + i (M + 1)`; since `‖ρ_m - mπ‖ ≤ M` this gives `‖ρ_m - σ'_n‖ ≥ max(1, π|m - n| - 2M - 1)`
and hence `‖ρ_m - σ'_n‖ ≥ (π/(2(2M+1))) |m - n|` for `m ≠ n`, a constant depending only on `M`.
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-- Padding node. -/
def padNode (M : ℝ) (n : ℤ) : ℂ := (n : ℂ) * (Real.pi : ℂ) + Complex.I * ((M + 1 : ℝ) : ℂ)

theorem sep_pad {ρ : ℤ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hρ : ∀ m : ℤ, ‖ρ m - (m : ℂ) * (Real.pi : ℂ)‖ ≤ M) (n m : ℤ) (hmn : m ≠ n) :
    Real.pi / (2 * (2 * M + 1)) * |(m : ℝ) - n| ≤ ‖ρ m - padNode M n‖ := by
  have hpi := Real.pi_pos
  set w : ℂ := ρ m - padNode M n with hw
  set j : ℝ := |(m : ℝ) - n| with hj
  have hj1 : 1 ≤ j := by
    have h1 : (1 : ℤ) ≤ |m - n| := Int.one_le_abs (sub_ne_zero.mpr hmn)
    have : (1 : ℝ) ≤ ((|m - n| : ℤ) : ℝ) := by exact_mod_cast h1
    simpa [hj, Int.cast_abs] using this
  have hr := hρ m
  -- first bound: imaginary part
  have him : 1 ≤ ‖w‖ := by
    have h1 : |(ρ m - (m : ℂ) * (Real.pi : ℂ)).im| ≤ M :=
      (Complex.abs_im_le_norm _).trans hr
    have h2 : (ρ m - (m : ℂ) * (Real.pi : ℂ)).im = (ρ m).im := by simp
    have h3 : w.im = (ρ m).im - (M + 1) := by
      simp [hw, padNode]
    have h4 : -(w.im) ≥ 1 := by
      have h5 := le_abs_self (ρ m - (m : ℂ) * (Real.pi : ℂ)).im
      rw [h2] at h1 h5
      rw [h3]; linarith
    exact (le_trans h4 (neg_le_abs _)).trans (Complex.abs_im_le_norm _)
  -- second bound: lattice distance
  have hlat : Real.pi * j ≤ ‖w‖ + (2 * M + 1) := by
    have e : ((m : ℂ) - n) * (Real.pi : ℂ)
        = w - (ρ m - (m : ℂ) * (Real.pi : ℂ)) + Complex.I * ((M + 1 : ℝ) : ℂ) := by
      simp only [hw, padNode]; ring
    have hn : ‖((m : ℂ) - n) * (Real.pi : ℂ)‖ = Real.pi * j := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
      have : ‖(m : ℂ) - n‖ = j := by
        rw [hj]; have := norm_int_sub_cast m n; simpa using this
      rw [this]; ring
    have hI : ‖Complex.I * ((M + 1 : ℝ) : ℂ)‖ = M + 1 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    calc Real.pi * j = ‖((m : ℂ) - n) * (Real.pi : ℂ)‖ := hn.symm
      _ = ‖w - (ρ m - (m : ℂ) * (Real.pi : ℂ)) + Complex.I * ((M + 1 : ℝ) : ℂ)‖ := by rw [e]
      _ ≤ ‖w - (ρ m - (m : ℂ) * (Real.pi : ℂ))‖ + ‖Complex.I * ((M + 1 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ (‖w‖ + ‖ρ m - (m : ℂ) * (Real.pi : ℂ)‖) + (M + 1) := by
          rw [hI]; gcongr; exact norm_sub_le _ _
      _ ≤ ‖w‖ + (2 * M + 1) := by linarith
  have hD : 0 < 2 * (2 * M + 1) := by positivity
  by_cases hcase : 2 * (2 * M + 1) ≤ Real.pi * j
  · -- `π j/2 ≤ π j - (2M+1) ≤ ‖w‖`
    have h1 : Real.pi * j / 2 ≤ ‖w‖ := by linarith
    have h2 : Real.pi / (2 * (2 * M + 1)) ≤ Real.pi / 2 := by
      apply div_le_div_of_nonneg_left hpi.le (by norm_num); nlinarith
    calc Real.pi / (2 * (2 * M + 1)) * j ≤ Real.pi / 2 * j := mul_le_mul_of_nonneg_right h2 (by linarith)
      _ = Real.pi * j / 2 := by ring
      _ ≤ ‖w‖ := h1
  · have hcase := (not_le.mp hcase)
    have : Real.pi / (2 * (2 * M + 1)) * j ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hD]; exact hcase.le
    exact this.trans him

end

end NlsGge.GK38.Lib
