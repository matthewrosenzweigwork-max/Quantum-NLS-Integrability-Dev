import NlsGge.GK38.PairAsymptoticsSmooth

/-! # F5: the smooth oscillatory estimate by integration by parts (GK Appendix D.1) -/

set_option autoImplicit false

open Filter Topology MeasureTheory Set
open scoped ContDiff

namespace NlsGge.GK38

noncomputable section

theorem norm_integral_osc_smooth_mul_le (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (A : ℝ) (hA : ∀ s ∈ Icc (0 : ℝ) 1, ‖g s‖ ≤ A)
    (z : ℂ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (2 * ‖z‖) * ‖∫ s : ℝ in 0..t,
      Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * g s‖ ≤
      (2 * A + ∫ s : ℝ in 0..1, ‖deriv g s‖) * Real.exp (|z.im| * t) := by
  let E : ℝ → ℂ := fun s => Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s))
  let K : ℂ := -2 * Complex.I * z
  have hEc : Continuous E := by dsimp [E]; fun_prop
  have hEd (s : ℝ) : HasDerivAt E (K * E s) s := by
    dsimp [E, K]
    have hd := (((hasDerivAt_const s (t : ℂ)).sub
      (Complex.ofRealCLM.hasDerivAt.const_mul (2 : ℂ))).const_mul
      (Complex.I * z)).cexp
    simp only [Pi.sub_apply, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] at hd
    convert hd using 1 <;> ring
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hgc' : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hiE : IntervalIntegrable E volume 0 t := hEc.intervalIntegrable _ _
  have hiK : IntervalIntegrable (fun s => K * E s) volume 0 t := hiE.const_mul K
  have hig : IntervalIntegrable g volume 0 t := hg.continuous.intervalIntegrable _ _
  have hig' : IntervalIntegrable (deriv g) volume 0 t := hgc'.intervalIntegrable _ _
  have hi1 : IntervalIntegrable (fun s => (K * E s) * g s) volume 0 t :=
    (hEc.const_mul K).mul hg.continuous |>.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun s => E s * deriv g s) volume 0 t :=
    hEc.mul hgc' |>.intervalIntegrable _ _
  have hp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    hEc.continuousOn hg.continuous.continuousOn (fun s _ => hEd s)
    (fun s _ => (hgd s).hasDerivAt) hiK hig'
  rw [intervalIntegral.integral_add hi1 hi2] at hp
  have hKI : (∫ s : ℝ in 0..t, (K * E s) * g s) =
      K * (∫ s : ℝ in 0..t, E s * g s) := by
    simp only [mul_assoc, intervalIntegral.integral_const_mul]
  rw [hKI] at hp
  have heq : K * (∫ s : ℝ in 0..t, E s * g s) =
      E t * g t - E 0 * g 0 - ∫ s : ℝ in 0..t, E s * deriv g s := by
    linear_combination hp
  have hKnorm : ‖K‖ = 2 * ‖z‖ := by simp [K, norm_mul]
  have htE := norm_osc_exp_le z ht.1 (show t ∈ Icc 0 t from ⟨ht.1, le_rfl⟩)
  have h0E := norm_osc_exp_le z ht.1 (show (0 : ℝ) ∈ Icc 0 t from ⟨le_rfl, ht.1⟩)
  change ‖E t‖ ≤ Real.exp (|z.im| * t) at htE
  change ‖E 0‖ ≤ Real.exp (|z.im| * t) at h0E
  have hJ := norm_integral_osc_le (deriv g) (hgc'.intervalIntegrable _ _) z ht
  change ‖∫ s : ℝ in 0..t, E s * deriv g s‖ ≤ _ at hJ
  change (2 * ‖z‖) * ‖∫ s : ℝ in 0..t, E s * g s‖ ≤ _
  calc (2 * ‖z‖) * ‖∫ s : ℝ in 0..t, E s * g s‖
      = ‖K * (∫ s : ℝ in 0..t, E s * g s)‖ := by rw [norm_mul, hKnorm]
    _ ≤ ‖E t‖ * ‖g t‖ + ‖E 0‖ * ‖g 0‖ + ‖∫ s : ℝ in 0..t, E s * deriv g s‖ := by
      rw [heq]
      calc ‖E t * g t - E 0 * g 0 - ∫ s : ℝ in 0..t, E s * deriv g s‖
          ≤ ‖E t * g t - E 0 * g 0‖ + ‖∫ s : ℝ in 0..t, E s * deriv g s‖ :=
            norm_sub_le _ _
        _ ≤ (‖E t * g t‖ + ‖E 0 * g 0‖) + ‖∫ s : ℝ in 0..t, E s * deriv g s‖ :=
            add_le_add (norm_sub_le _ _) (le_refl _)
        _ = _ := by rw [norm_mul, norm_mul]
    _ ≤ Real.exp (|z.im| * t) * A + Real.exp (|z.im| * t) * A +
        Real.exp (|z.im| * t) * (∫ s : ℝ in 0..1, ‖deriv g s‖) := by
      exact add_le_add (add_le_add
        (mul_le_mul htE (hA t ht) (norm_nonneg _) (Real.exp_nonneg _))
        (mul_le_mul h0E (hA 0 ⟨le_rfl, zero_le_one⟩) (norm_nonneg _)
          (Real.exp_nonneg _))) hJ
    _ = _ := by ring

end

end NlsGge.GK38
