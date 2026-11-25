import NlsGge.GK38.PairAsymptoticsSeq

                                                                                               
                                                                     
                                                                                                     
                                                                                                 
                                                                                         
                                                                                        
                                                         
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Matrix.Norms.Elementwise
open NlsGge.GK38
namespace NlsGge.ThirdConsultation.G1098M2B
noncomputable section

/-- Exponential difference on a half-plane where the real parts are bounded by `B`. -/
theorem norm_cexp_sub_cexp_le {x y : ℂ} {B : ℝ} (hx : x.re ≤ B) (hy : y.re ≤ B) :
    ‖Complex.exp x - Complex.exp y‖ ≤ 2 * Real.exp B * ‖x - y‖ := by
  by_cases h : ‖x - y‖ ≤ 1
  · have hx' : Complex.exp x = Complex.exp y * Complex.exp (x - y) := by
      rw [← Complex.exp_add]; congr 1; ring
    have hfac : Complex.exp x - Complex.exp y = Complex.exp y * (Complex.exp (x - y) - 1) := by
      rw [hx', mul_sub, mul_one]
    have h1 : ‖Complex.exp y‖ ≤ Real.exp B := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr hy
    have h2 : ‖Complex.exp (x - y) - 1‖ ≤ 2 * ‖x - y‖ := Complex.norm_exp_sub_one_le h
    rw [hfac, norm_mul]
    calc ‖Complex.exp y‖ * ‖Complex.exp (x - y) - 1‖ ≤ Real.exp B * (2 * ‖x - y‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
      _ = 2 * Real.exp B * ‖x - y‖ := by ring
  · have h' : 1 < ‖x - y‖ := not_le.mp h
    have hxB : ‖Complex.exp x‖ ≤ Real.exp B := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr hx
    have hyB : ‖Complex.exp y‖ ≤ Real.exp B := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr hy
    have h3 : ‖Complex.exp x - Complex.exp y‖ ≤ 2 * Real.exp B := by
      have := norm_sub_le (Complex.exp x) (Complex.exp y)
      linarith
    exact h3.trans (le_mul_of_one_le_right (by positivity) h'.le)

theorem norm_I_mul_sub_mul_le (z w : ℂ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖Complex.I * (z - w) * (t : ℂ)‖ ≤ ‖z - w‖ := by
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht0, one_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) ht1

/-- Real part of `-(i u t)` is `Im u · t`, bounded by `B` when `|Im u| ≤ B` and `t ∈ [0,1]`. -/
theorem re_neg_I_mul_le {u : ℂ} {t B : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu : |u.im| ≤ B) :
    (-(Complex.I * u * (t : ℂ))).re ≤ B := by
  have h1 : (-(Complex.I * u * (t : ℂ))).re = u.im * t := by
    simp
  rw [h1]
  calc u.im * t ≤ |u.im * t| := le_abs_self _
    _ = |u.im| * t := by rw [abs_mul, abs_of_nonneg ht0]
    _ ≤ |u.im| := mul_le_of_le_one_right (abs_nonneg _) ht1
    _ ≤ B := hu

/-- Real part of `i u t` is `-(Im u · t)`, bounded by `B` when `|Im u| ≤ B` and `t ∈ [0,1]`. -/
theorem re_I_mul_le {u : ℂ} {t B : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu : |u.im| ≤ B) :
    (Complex.I * u * (t : ℂ)).re ≤ B := by
  have h1 : (Complex.I * u * (t : ℂ)).re = -(u.im * t) := by
    simp
  rw [h1]
  calc -(u.im * t) ≤ |u.im * t| := neg_le_abs _
    _ = |u.im| * t := by rw [abs_mul, abs_of_nonneg ht0]
    _ ≤ |u.im| := mul_le_of_le_one_right (abs_nonneg _) ht1
    _ ≤ B := hu

/-- Entrywise Lipschitz bound for the free solution on `[0,1]` in a horizontal strip. -/
theorem freeE_entry_sub_le {z w : ℂ} {B : ℝ} (hz : |z.im| ≤ B) (hw : |w.im| ≤ B) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i j : Fin 2) :
    ‖freeE z t i j - freeE w t i j‖ ≤ 2 * Real.exp B * ‖z - w‖ := by
  have hzw0 : ‖Complex.I * (z - w) * (t : ℂ)‖ ≤ ‖z - w‖ := norm_I_mul_sub_mul_le z w ht0 ht1
  have hK : 0 ≤ 2 * Real.exp B := by positivity
  match i, j with
  | 0, 0 =>
    show ‖Complex.exp (-(Complex.I * z * (t : ℂ))) - Complex.exp (-(Complex.I * w * (t : ℂ)))‖ ≤ _
    have hxy : -(Complex.I * z * (t : ℂ)) - -(Complex.I * w * (t : ℂ)) =
        -(Complex.I * (z - w) * (t : ℂ)) := by ring
    calc ‖Complex.exp (-(Complex.I * z * (t : ℂ))) - Complex.exp (-(Complex.I * w * (t : ℂ)))‖
        ≤ 2 * Real.exp B * ‖-(Complex.I * z * (t : ℂ)) - -(Complex.I * w * (t : ℂ))‖ :=
          norm_cexp_sub_cexp_le (re_neg_I_mul_le ht0 ht1 hz) (re_neg_I_mul_le ht0 ht1 hw)
      _ = 2 * Real.exp B * ‖Complex.I * (z - w) * (t : ℂ)‖ := by rw [hxy, norm_neg]
      _ ≤ 2 * Real.exp B * ‖z - w‖ := mul_le_mul_of_nonneg_left hzw0 hK
  | 0, 1 =>
    show ‖(0 : ℂ) - 0‖ ≤ _
    rw [sub_self, norm_zero]
    positivity
  | 1, 0 =>
    show ‖(0 : ℂ) - 0‖ ≤ _
    rw [sub_self, norm_zero]
    positivity
  | 1, 1 =>
    show ‖Complex.exp (Complex.I * z * (t : ℂ)) - Complex.exp (Complex.I * w * (t : ℂ))‖ ≤ _
    have hxy : Complex.I * z * (t : ℂ) - Complex.I * w * (t : ℂ) =
        Complex.I * (z - w) * (t : ℂ) := by ring
    calc ‖Complex.exp (Complex.I * z * (t : ℂ)) - Complex.exp (Complex.I * w * (t : ℂ))‖
        ≤ 2 * Real.exp B * ‖Complex.I * z * (t : ℂ) - Complex.I * w * (t : ℂ)‖ :=
          norm_cexp_sub_cexp_le (re_I_mul_le ht0 ht1 hz) (re_I_mul_le ht0 ht1 hw)
      _ = 2 * Real.exp B * ‖Complex.I * (z - w) * (t : ℂ)‖ := by rw [hxy]
      _ ≤ 2 * Real.exp B * ‖z - w‖ := mul_le_mul_of_nonneg_left hzw0 hK

/-- Matrix form of the strip Lipschitz bound, in the elementwise maximum norm. -/
theorem freeFund_sub_norm_le {z w : ℂ} {B : ℝ} (hz : |z.im| ≤ B) (hw : |w.im| ≤ B)
    (t : Set.Icc (0 : ℝ) 1) :
    ‖freeFund z t - freeFund w t‖ ≤ 2 * Real.exp B * ‖z - w‖ := by
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  rw [Matrix.sub_apply]
  exact freeE_entry_sub_le hz hw t.2.1 t.2.2 i j

/-- Square-sum comparison: the squared free-shift errors at fixed `t ∈ [0,1]` are summable,
with total at most `(2e^c)^2` times the total of the squared shifts. -/
theorem freeFund_shift_l2 {μ : ℤ → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hμ : ∀ n : ℤ, ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c)
    (hs : Summable (fun n : ℤ => ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
    (t : Set.Icc (0 : ℝ) 1) :
    Summable (fun n : ℤ => ‖freeFund (μ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2) ∧
      ∑' n : ℤ, ‖freeFund (μ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2 ≤
        (2 * Real.exp c) ^ 2 * ∑' n : ℤ, ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 := by
  have him : ∀ n : ℤ, |(μ n).im| ≤ c := by
    intro n
    have h0 : (μ n).im = (μ n - (n : ℂ) * (Real.pi : ℂ)).im := by
      simp [Complex.mul_im]
    rw [h0]
    exact (Complex.abs_im_le_norm _).trans (hμ n)
  have him0 : ∀ n : ℤ, |((n : ℂ) * (Real.pi : ℂ)).im| ≤ c := by
    intro n
    simp [Complex.mul_im, hc]
  have hterm : ∀ n : ℤ, ‖freeFund (μ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2 ≤
      (2 * Real.exp c) ^ 2 * ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 := by
    intro n
    have h1 := freeFund_sub_norm_le (him n) (him0 n) t
    have h0 : 0 ≤ ‖freeFund (μ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ := norm_nonneg _
    calc ‖freeFund (μ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2
        ≤ (2 * Real.exp c * ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = (2 * Real.exp c) ^ 2 * ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 := by ring
  have hbig : Summable (fun n : ℤ => (2 * Real.exp c) ^ 2 * ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) :=
    hs.mul_left _
  have hsum : Summable (fun n : ℤ =>
      ‖freeFund (μ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hterm hbig
  refine ⟨hsum, ?_⟩
  calc ∑' n : ℤ, ‖freeFund (μ n) t - freeFund ((n : ℂ) * (Real.pi : ℂ)) t‖ ^ 2
      ≤ ∑' n : ℤ, (2 * Real.exp c) ^ 2 * ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 :=
        Summable.tsum_le_tsum hterm hsum hbig
    _ = (2 * Real.exp c) ^ 2 * ∑' n : ℤ, ‖μ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 := tsum_mul_left

end
end NlsGge.ThirdConsultation.G1098M2B
