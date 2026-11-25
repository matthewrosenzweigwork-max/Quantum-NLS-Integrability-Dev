import Mathlib

/-! # Trunk C (generic): rates are Lipschitz-stable under uniform closeness of characters

Author: Claude Opus 5.5 (trunk C preparation).  Not self-reviewed, not accepted.
Namespace `NlsGge.ALLS.TransC`.

`rate_close_of_uniform_close`: if `T > 0`, `ε < 2` and
`‖exp(-(t ω) i) - exp(-(t ω') i)‖ ≤ ε` for all `t ∈ [0, T]`, then `|ω - ω'| ≤ π ε / (2T)`.
This is the "compact-time character convergence avoids single-time aliasing" step (handoff C2,
independent lemmas §5): uniform convergence of the characters on a fixed compact time interval
gives convergence of the real rates. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.ALLS.TransC

/-- Jordan-type lower bound `(2/π)|x| ≤ ‖e^{ix} - 1‖` for `|x| ≤ π`. -/
theorem jordan_exp_sub_one {x : ℝ} (hx : |x| ≤ Real.pi) :
    2 / Real.pi * |x| ≤ ‖Complex.exp (Complex.I * x) - 1‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  have hpi := Real.pi_pos
  have h0 : 0 ≤ |x| / 2 := by positivity
  have h1 : |x| / 2 ≤ Real.pi / 2 := by linarith
  have hs := Real.mul_le_sin h0 h1
  have hsin : |Real.sin (x / 2)| = Real.sin (|x| / 2) := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by rw [abs_of_nonneg h] at h1; linarith))]
    · rw [abs_of_neg h, show x / 2 = -(-x / 2) by ring, Real.sin_neg, abs_neg,
        abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
          (by rw [abs_of_neg h] at h1; linarith))]
  rw [hsin]
  have : 2 / Real.pi * |x| = 2 * (2 / Real.pi * (|x| / 2)) := by ring
  rw [this]
  linarith

theorem norm_char_sub (t ω ω' : ℝ) :
    ‖Complex.exp (-((t * ω : ℝ) : ℂ) * Complex.I) - Complex.exp (-((t * ω' : ℝ) : ℂ) * Complex.I)‖ =
      ‖Complex.exp (Complex.I * ((t * (ω' - ω) : ℝ) : ℂ)) - 1‖ := by
  have e : Complex.exp (-((t * ω : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((t * ω' : ℝ) : ℂ) * Complex.I) * Complex.exp (Complex.I * ((t * (ω' - ω) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hu : ‖Complex.exp (-((t * ω' : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [← Complex.ofReal_neg]; exact Complex.norm_exp_ofReal_mul_I _
  rw [e, show Complex.exp (-((t * ω' : ℝ) : ℂ) * Complex.I) * Complex.exp (Complex.I * ((t * (ω' - ω) : ℝ) : ℂ)) -
      Complex.exp (-((t * ω' : ℝ) : ℂ) * Complex.I) = Complex.exp (-((t * ω' : ℝ) : ℂ) * Complex.I) *
      (Complex.exp (Complex.I * ((t * (ω' - ω) : ℝ) : ℂ)) - 1) by ring, norm_mul, hu, one_mul]

/-- **Rate stability**: uniform `ε`-closeness on `[0, T]` with `ε < 2` gives
`|ω - ω'| ≤ π ε / (2T)`. -/
theorem rate_close_of_uniform_close {T ε ω ω' : ℝ} (hT : 0 < T) (hε : ε < 2)
    (h : ∀ t ∈ Set.Icc 0 T,
      ‖Complex.exp (-((t * ω : ℝ) : ℂ) * Complex.I) - Complex.exp (-((t * ω' : ℝ) : ℂ) * Complex.I)‖ ≤ ε) :
    |ω - ω'| ≤ Real.pi * ε / (2 * T) := by
  have hpi := Real.pi_pos
  rw [abs_sub_comm]
  rcases le_or_gt (|ω' - ω| * T) Real.pi with hle | hgt
  · have hx : |T * (ω' - ω)| ≤ Real.pi := by rw [abs_mul, abs_of_pos hT, mul_comm]; exact hle
    have hj := jordan_exp_sub_one hx
    have hT' := h T ⟨hT.le, le_rfl⟩
    rw [norm_char_sub] at hT'
    rw [abs_mul, abs_of_pos hT] at hj
    have h1 : 2 / Real.pi * (T * |ω' - ω|) ≤ ε := hj.trans hT'
    rw [le_div_iff₀ (by positivity)]
    have h2 : 2 * (T * |ω' - ω|) ≤ Real.pi * ε := by
      have := mul_le_mul_of_nonneg_left h1 hpi.le
      rwa [← mul_assoc, mul_div_cancel₀ _ hpi.ne'] at this
    linarith
  · exfalso
    have hd0 : 0 < |ω' - ω| := by
      by_contra h0; rw [not_lt] at h0
      have : |ω' - ω| = 0 := le_antisymm h0 (abs_nonneg _)
      rw [this, zero_mul] at hgt; linarith
    have htT : Real.pi / |ω' - ω| ≤ T := by rw [div_le_iff₀ hd0]; linarith
    have ht0 : 0 ≤ Real.pi / |ω' - ω| := by positivity
    have hx : |Real.pi / |ω' - ω| * (ω' - ω)| = Real.pi := by
      rw [abs_mul, abs_of_nonneg ht0, div_mul_cancel₀ _ hd0.ne']
    have hj := jordan_exp_sub_one hx.le
    have h' := h _ ⟨ht0, htT⟩
    rw [norm_char_sub] at h'
    rw [hx, div_mul_cancel₀ _ hpi.ne'] at hj
    linarith

end NlsGge.ALLS.TransC
