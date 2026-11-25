import Mathlib

                                                                              
                                                                                                            
                                                                                     
                                                                                                    
                                                                                               
                                                                                         
                                                                    
                                                                                                               
                                                                                               
                                                                                                   
set_option autoImplicit false
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS031Analytic
noncomputable section

/-! ### §2 Scalar strip algebra -/

/-- Algebraic core: bounded remainders and the determinant factor give an order-N strip error. -/
theorem discriminant_error_bound
    (N : ℕ) (X M : ℝ) (D ε r₀ r₁ s₀ s₁ α β : ℂ)
    (hX : 1 ≤ X) (hM : 0 ≤ M) (hD : ‖D‖ ≤ 2)
    (hε : ‖ε‖ = ((2 * X) ^ N)⁻¹)
    (hr₀ : ‖r₀‖ ≤ M) (hr₁ : ‖r₁‖ ≤ M)
    (hs₀ : ‖s₀‖ ≤ M) (hs₁ : ‖s₁‖ ≤ M)
    (hα : ‖α‖ ≤ 1 / 2) (hβ : ‖β‖ ≤ 1 / 2) :
    ‖D * ε * (r₀ + r₁ - α * s₀ - β * s₁)‖ ≤ 6 * M / X ^ N := by
  have hαs : ‖α * s₀‖ ≤ M / 2 := by
    rw [norm_mul]
    calc ‖α‖ * ‖s₀‖ ≤ (1 / 2) * M := mul_le_mul hα hs₀ (norm_nonneg _) (by positivity)
      _ = M / 2 := by ring
  have hβs : ‖β * s₁‖ ≤ M / 2 := by
    rw [norm_mul]
    calc ‖β‖ * ‖s₁‖ ≤ (1 / 2) * M := mul_le_mul hβ hs₁ (norm_nonneg _) (by positivity)
      _ = M / 2 := by ring
  have hrem : ‖r₀ + r₁ - α * s₀ - β * s₁‖ ≤ 3 * M := by
    have hsum : ‖r₀ + r₁‖ ≤ M + M := by
      calc ‖r₀ + r₁‖ ≤ ‖r₀‖ + ‖r₁‖ := norm_add_le _ _
        _ ≤ M + M := add_le_add hr₀ hr₁
    have hsub : ‖α * s₀ + β * s₁‖ ≤ M / 2 + M / 2 := by
      calc ‖α * s₀ + β * s₁‖ ≤ ‖α * s₀‖ + ‖β * s₁‖ := norm_add_le _ _
        _ ≤ M / 2 + M / 2 := add_le_add hαs hβs
    calc ‖r₀ + r₁ - α * s₀ - β * s₁‖
        = ‖(r₀ + r₁) - (α * s₀ + β * s₁)‖ := by congr 1 <;> ring
      _ ≤ ‖r₀ + r₁‖ + ‖α * s₀ + β * s₁‖ := norm_sub_le _ _
      _ ≤ (M + M) + (M / 2 + M / 2) := add_le_add hsum hsub
      _ = 3 * M := by ring
  have hprod : ‖D * ε * (r₀ + r₁ - α * s₀ - β * s₁)‖ ≤ 2 * ‖ε‖ * (3 * M) := by
    rw [norm_mul, norm_mul]
    calc ‖D‖ * ‖ε‖ * ‖r₀ + r₁ - α * s₀ - β * s₁‖
        ≤ ‖D‖ * ‖ε‖ * (3 * M) := mul_le_mul_of_nonneg_left hrem (by positivity)
      _ ≤ 2 * ‖ε‖ * (3 * M) := by gcongr
  have hpow : X ^ N ≤ (2 * X) ^ N := by
    gcongr
    linarith
  calc ‖D * ε * (r₀ + r₁ - α * s₀ - β * s₁)‖
      ≤ 2 * ‖ε‖ * (3 * M) := hprod
    _ = 6 * M / (2 * X) ^ N := by rw [hε]; field_simp; ring
    _ ≤ 6 * M / X ^ N := by
      apply div_le_div_of_nonneg_left
      · positivity
      · positivity
      · exact hpow

/-! ### §3 Finite Laurent tail -/

/-- Finite Laurent tails decay by one inverse power once every exponent is negative. -/
theorem finite_laurent_sum_tail_bound {N : ℕ} (c : ℕ → ℂ) (z : ℂ)
    (hz : 1 ≤ ‖z‖) :
    ‖∑ k ∈ Finset.Icc 1 N, (2 * Complex.I * z) ^ (-(k : ℤ)) * c k‖ ≤
      (∑ k ∈ Finset.Icc 1 N, ‖c k‖) / ‖z‖ := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz
  have hx : ‖2 * Complex.I * z‖ = 2 * ‖z‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      ‖(2 * Complex.I * z) ^ (-(k : ℤ)) * c k‖ ≤ ‖c k‖ / ‖z‖ := by
    intro k hk
    have hk0 : k ≠ 0 := by
      simp only [Finset.mem_Icc] at hk
      omega
    have hbase : 1 ≤ 2 * ‖z‖ := by linarith
    have hpow : ‖z‖ ≤ (2 * ‖z‖) ^ k :=
      calc ‖z‖ ≤ 2 * ‖z‖ := by linarith
        _ ≤ (2 * ‖z‖) ^ k := le_self_pow₀ hbase hk0
    have hinv : ((2 * ‖z‖) ^ k)⁻¹ ≤ ‖z‖⁻¹ := inv_anti₀ hzpos hpow
    rw [norm_mul, norm_zpow, hx, zpow_neg, zpow_natCast]
    calc ((2 * ‖z‖) ^ k)⁻¹ * ‖c k‖ ≤ ‖z‖⁻¹ * ‖c k‖ :=
          mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
      _ = ‖c k‖ / ‖z‖ := by rw [div_eq_inv_mul]
  calc ‖∑ k ∈ Finset.Icc 1 N, (2 * Complex.I * z) ^ (-(k : ℤ)) * c k‖
      ≤ ∑ k ∈ Finset.Icc 1 N, ‖(2 * Complex.I * z) ^ (-(k : ℤ)) * c k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 N, ‖c k‖ / ‖z‖ := Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.Icc 1 N, ‖c k‖) / ‖z‖ := by rw [Finset.sum_div]

/-! ### §5a Half-node norms and trigonometry -/

theorem norm_halfNode_expr (j : ℤ) :
    ‖((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)‖ = |(j : ℝ) + 1 / 2| * Real.pi := by
  have e : ((j : ℂ) + (1 / 2 : ℂ)) = ((((j : ℝ) + 1 / 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [e, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_of_nonneg Real.pi_pos.le]

theorem one_le_norm_halfNode_expr (j : ℤ) :
    1 ≤ ‖((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)‖ := by
  rw [norm_halfNode_expr]
  have hpi := Real.pi_gt_three
  have h : (1 / 2 : ℝ) ≤ |(j : ℝ) + 1 / 2| := by
    rcases le_or_gt 0 j with hj | hj
    · have hj' : (0 : ℝ) ≤ j := by exact_mod_cast hj
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hj' : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
      rw [abs_of_neg (by linarith)]
      linarith
  nlinarith

theorem natAbs_le_norm_halfNode_expr (j : ℤ) :
    (j.natAbs : ℝ) ≤ ‖((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)‖ := by
  rw [norm_halfNode_expr]
  have hpi := Real.pi_gt_three
  have hcast : (j.natAbs : ℝ) = |(j : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hcast]
  rcases le_or_gt 0 j with hj | hj
  · have hj' : (0 : ℝ) ≤ j := by exact_mod_cast hj
    rw [abs_of_nonneg hj', abs_of_nonneg (by linarith)]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (j : ℝ) + 1 / 2 by linarith)
      (show (0 : ℝ) ≤ Real.pi - 3 by linarith)]
  · have hj' : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ -(j : ℝ) - 1 / 2 by linarith)
      (show (0 : ℝ) ≤ Real.pi - 3 by linarith)]

theorem cos_int_mul_pi_eq (j : ℤ) :
    Complex.cos ((j : ℂ) * (Real.pi : ℂ)) = (-1 : ℂ) ^ j := by
  induction j using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have e : (((n : ℤ) + 1 : ℤ) : ℂ) * (Real.pi : ℂ) =
        ((n : ℤ) : ℂ) * (Real.pi : ℂ) + (Real.pi : ℂ) := by push_cast; ring
    rw [e, Complex.cos_add_pi, ih, zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    ring
  | pred n ih =>
    have e : ((-(n : ℤ) - 1 : ℤ) : ℂ) * (Real.pi : ℂ) =
        ((-(n : ℤ) : ℤ) : ℂ) * (Real.pi : ℂ) - (Real.pi : ℂ) := by push_cast; ring
    rw [e, Complex.cos_sub_pi, ih, zpow_sub_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    ring

theorem neg_one_zpow_mul_self (j : ℤ) : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul, zpow_mul]
  norm_num

theorem norm_neg_one_zpow (j : ℤ) : ‖(-1 : ℂ) ^ j‖ = 1 := by
  rw [norm_zpow, norm_neg, norm_one, one_zpow]

theorem cos_halfNode_add (j : ℤ) (δ : ℂ) :
    Complex.cos (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ) =
      -((-1 : ℂ) ^ j * Complex.sin δ) := by
  have e : ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ =
      ((j : ℂ) * (Real.pi : ℂ) + δ) + (Real.pi : ℂ) / 2 := by ring
  rw [e, Complex.cos_add_pi_div_two, Complex.sin_add, Complex.sin_int_mul_pi, cos_int_mul_pi_eq]
  ring

theorem sin_halfNode_add (j : ℤ) (δ : ℂ) :
    Complex.sin (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ) =
      (-1 : ℂ) ^ j * Complex.cos δ := by
  have e : ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ =
      ((j : ℂ) * (Real.pi : ℂ) + δ) + (Real.pi : ℂ) / 2 := by ring
  rw [e, Complex.sin_add_pi_div_two, Complex.cos_add, Complex.sin_int_mul_pi, cos_int_mul_pi_eq]
  ring

/-! ### §5b Small-argument trigonometric bounds -/

theorem norm_sin_le_of_le_one {δ : ℂ} (h : ‖δ‖ ≤ 1) :
    ‖Complex.sin δ‖ ≤ ‖δ‖ + ‖δ‖ ^ 3 / 6 + ‖δ‖ ^ 5 / 100 := by
  have hb := Complex.sin_bound h
  have e : Complex.sin δ = ((Complex.sin δ - (δ - δ ^ 3 / 6)) + δ) - δ ^ 3 / 6 := by ring
  have h3 : ‖δ ^ 3 / 6‖ = ‖δ‖ ^ 3 / 6 := by rw [norm_div, norm_pow, Complex.norm_ofNat]
  rw [e]
  calc ‖((Complex.sin δ - (δ - δ ^ 3 / 6)) + δ) - δ ^ 3 / 6‖
      ≤ ‖(Complex.sin δ - (δ - δ ^ 3 / 6)) + δ‖ + ‖δ ^ 3 / 6‖ := norm_sub_le _ _
    _ ≤ (‖Complex.sin δ - (δ - δ ^ 3 / 6)‖ + ‖δ‖) + ‖δ ^ 3 / 6‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖δ‖ + ‖δ‖ ^ 3 / 6 + ‖δ‖ ^ 5 / 100 := by rw [h3]; linarith

theorem norm_cos_sub_one_le {δ : ℂ} (h : ‖δ‖ ≤ 1) :
    ‖Complex.cos δ - 1‖ ≤ ‖δ‖ ^ 2 / 2 + ‖δ‖ ^ 4 * (5 / 96) := by
  have hb := Complex.cos_bound h
  have e : Complex.cos δ - 1 = (Complex.cos δ - (1 - δ ^ 2 / 2)) - δ ^ 2 / 2 := by ring
  have h2 : ‖δ ^ 2 / 2‖ = ‖δ‖ ^ 2 / 2 := by rw [norm_div, norm_pow, Complex.norm_ofNat]
  rw [e]
  calc ‖(Complex.cos δ - (1 - δ ^ 2 / 2)) - δ ^ 2 / 2‖
      ≤ ‖Complex.cos δ - (1 - δ ^ 2 / 2)‖ + ‖δ ^ 2 / 2‖ := norm_sub_le _ _
    _ ≤ ‖δ‖ ^ 2 / 2 + ‖δ‖ ^ 4 * (5 / 96) := by rw [h2]; linarith

theorem pi_div_eight_lt : Real.pi / 8 < 2 / 5 := by
  have h := Real.pi_lt_d2
  norm_num at h
  linarith

theorem norm_sin_lt_half {δ : ℂ} (h : ‖δ‖ < Real.pi / 8) : ‖Complex.sin δ‖ < 1 / 2 := by
  have h25 : ‖δ‖ ≤ 2 / 5 := by linarith [pi_div_eight_lt]
  have hs := norm_sin_le_of_le_one (show ‖δ‖ ≤ 1 by linarith)
  have h3 : ‖δ‖ ^ 3 ≤ (2 / 5) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) h25 3
  have h5 : ‖δ‖ ^ 5 ≤ (2 / 5) ^ 5 := pow_le_pow_left₀ (norm_nonneg _) h25 5
  norm_num at h3 h5
  linarith

theorem re_cos_pos {δ : ℂ} (h : ‖δ‖ < Real.pi / 8) : 0 < (Complex.cos δ).re := by
  have h25 : ‖δ‖ ≤ 2 / 5 := by linarith [pi_div_eight_lt]
  have hc := norm_cos_sub_one_le (show ‖δ‖ ≤ 1 by linarith)
  have h2 : ‖δ‖ ^ 2 ≤ (2 / 5) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h25 2
  have h4 : ‖δ‖ ^ 4 ≤ (2 / 5) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h25 4
  norm_num at h2 h4
  have hre : |(Complex.cos δ - 1).re| ≤ ‖Complex.cos δ - 1‖ := Complex.abs_re_le_norm _
  have hre' := neg_abs_le (Complex.cos δ - 1).re
  rw [Complex.sub_re, Complex.one_re] at hre hre'
  linarith

/-- For |δ| ≤ 1/8: |sin δ| < 1/4 and |cos δ| ≥ 1/2. -/
theorem small_phase_bounds {δ : ℂ} (h : ‖δ‖ ≤ 1 / 8) :
    ‖Complex.sin δ‖ < 1 / 4 ∧ 1 / 2 ≤ ‖Complex.cos δ‖ := by
  have h1 : ‖δ‖ ≤ 1 := by linarith
  have hs := norm_sin_le_of_le_one h1
  have hc := norm_cos_sub_one_le h1
  have h2 : ‖δ‖ ^ 2 ≤ (1 / 8) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have h3 : ‖δ‖ ^ 3 ≤ (1 / 8) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) h 3
  have h4 : ‖δ‖ ^ 4 ≤ (1 / 8) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h 4
  have h5 : ‖δ‖ ^ 5 ≤ (1 / 8) ^ 5 := pow_le_pow_left₀ (norm_nonneg _) h 5
  norm_num at h2 h3 h4 h5
  refine ⟨by linarith, ?_⟩
  have htri := norm_sub_norm_le (1 : ℂ) (Complex.cos δ)
  rw [norm_one, norm_sub_rev] at htri
  linarith

/-! ### §4 The principal log/sqrt branch on |w| < 1/2 -/

theorem sqrt_sq_eq (a : ℂ) : Complex.sqrt a ^ 2 = a := by
  unfold Complex.sqrt
  exact Complex.cpow_ofNat_inv_pow a 2

theorem re_sqrt_nonneg (a : ℂ) : 0 ≤ (Complex.sqrt a).re := by
  unfold Complex.sqrt
  rw [Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

theorem sqrt_sq_of_re_pos (s : ℂ) (hs : 0 < s.re) : Complex.sqrt (s ^ 2) = s := by
  have h1 : Complex.sqrt (s ^ 2) ^ 2 = s ^ 2 := sqrt_sq_eq _
  have hre0 := re_sqrt_nonneg (s ^ 2)
  have hfac : (Complex.sqrt (s ^ 2) - s) * (Complex.sqrt (s ^ 2) + s) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 hfac with h2 | h2
  · exact sub_eq_zero.1 h2
  · exfalso
    have h3 : Complex.sqrt (s ^ 2) = -s := by linear_combination h2
    rw [h3] at hre0
    simp only [Complex.neg_re] at hre0
    linarith

theorem re_one_add_sq_gt {w : ℂ} (hw : ‖w‖ < 1 / 2) : 3 / 4 < (1 + w ^ 2).re := by
  have h1 : |(w ^ 2).re| ≤ ‖w ^ 2‖ := Complex.abs_re_le_norm _
  rw [norm_pow] at h1
  have h2 : ‖w‖ ^ 2 < 1 / 4 := by nlinarith [norm_nonneg w]
  have h3 := neg_abs_le (w ^ 2).re
  rw [Complex.add_re, Complex.one_re]
  linarith

theorem half_lt_re_sqrt {w : ℂ} (hw : ‖w‖ < 1 / 2) :
    1 / 2 < (Complex.sqrt (1 + w ^ 2)).re := by
  have hsq : Complex.sqrt (1 + w ^ 2) ^ 2 = 1 + w ^ 2 := sqrt_sq_eq _
  have hre : (Complex.sqrt (1 + w ^ 2) ^ 2).re =
      (Complex.sqrt (1 + w ^ 2)).re ^ 2 - (Complex.sqrt (1 + w ^ 2)).im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  have h1 := re_one_add_sq_gt hw
  rw [← hsq, hre] at h1
  have h0 : 0 ≤ (Complex.sqrt (1 + w ^ 2)).re := re_sqrt_nonneg _
  nlinarith [sq_nonneg (Complex.sqrt (1 + w ^ 2)).im]

theorem half_le_norm_sqrt {w : ℂ} (hw : ‖w‖ < 1 / 2) :
    1 / 2 ≤ ‖Complex.sqrt (1 + w ^ 2)‖ :=
  (half_lt_re_sqrt hw).le.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))

theorem re_add_sqrt_pos {w : ℂ} (hw : ‖w‖ < 1 / 2) :
    0 < (w + Complex.sqrt (1 + w ^ 2)).re := by
  have h1 := half_lt_re_sqrt hw
  have h2 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have h3 := neg_abs_le w.re
  rw [Complex.add_re]
  linarith

theorem hasDerivAt_branch {w : ℂ} (hw : ‖w‖ < 1 / 2) :
    HasDerivAt (fun x : ℂ => Complex.log (x + Complex.sqrt (1 + x ^ 2)))
      (Complex.sqrt (1 + w ^ 2))⁻¹ w := by
  have hu : (1 + w ^ 2) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inl (by linarith [re_one_add_sq_gt hw]))
  have hs0 : Complex.sqrt (1 + w ^ 2) ≠ 0 := by
    intro h
    have := half_lt_re_sqrt hw
    rw [h, Complex.zero_re] at this
    linarith
  have hsum0 : w + Complex.sqrt (1 + w ^ 2) ≠ 0 := by
    intro h
    have := re_add_sqrt_pos hw
    rw [h, Complex.zero_re] at this
    linarith
  have hslit : w + Complex.sqrt (1 + w ^ 2) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inl (re_add_sqrt_pos hw))
  have h0 := (Complex.hasDerivAt_sqrt hu).comp w ((hasDerivAt_pow 2 w).const_add 1)
  obtain ⟨e, hS⟩ : ∃ e : ℂ, HasDerivAt (fun x : ℂ => Complex.sqrt (1 + x ^ 2)) e w := ⟨_, h0⟩
  have hP : HasDerivAt (fun x : ℂ => Complex.sqrt (1 + x ^ 2) ^ 2) (2 * w) w := by
    have hf : (fun x : ℂ => Complex.sqrt (1 + x ^ 2) ^ 2) = fun x => 1 + x ^ 2 :=
      funext fun x => sqrt_sq_eq _
    rw [hf]
    simpa using (hasDerivAt_pow 2 w).const_add 1
  have hP' := (hasDerivAt_pow 2 (Complex.sqrt (1 + w ^ 2))).comp w hS
  have hu' := hP'.unique hP
  have he : 2 * Complex.sqrt (1 + w ^ 2) * e = 2 * w := by
    rw [← hu']
    norm_num
  have he' : e = w / Complex.sqrt (1 + w ^ 2) := by
    field_simp
    linear_combination he / 2
  have hlog := ((hasDerivAt_id' w).add hS).clog hslit
  convert hlog using 1
  show (Complex.sqrt (1 + w ^ 2))⁻¹ = (1 + e) / (w + Complex.sqrt (1 + w ^ 2))
  rw [he']
  field_simp
  ring

/-- Mean-value bound for the branch on the disc |w| < 1/2 (derivative norm ≤ 2). -/
theorem branch_lipschitz {w v : ℂ} (hw : ‖w‖ < 1 / 2) (hv : ‖v‖ < 1 / 2) :
    ‖Complex.log (w + Complex.sqrt (1 + w ^ 2)) - Complex.log (v + Complex.sqrt (1 + v ^ 2))‖ ≤
      2 * ‖w - v‖ := by
  have hball : ∀ x ∈ Metric.ball (0 : ℂ) (1 / 2), ‖x‖ < 1 / 2 := fun x hx => by
    simpa using hx
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x : ℂ => Complex.log (x + Complex.sqrt (1 + x ^ 2)))
    (f' := fun x => (Complex.sqrt (1 + x ^ 2))⁻¹) (s := Metric.ball (0 : ℂ) (1 / 2)) (C := 2)
    (fun x hx => (hasDerivAt_branch (hball x hx)).hasDerivWithinAt)
    (fun x hx => by
      have h := half_le_norm_sqrt (hball x hx)
      rw [norm_inv]
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith)
    (convex_ball (0 : ℂ) (1 / 2)) (x := v) (y := w) (by simpa using hv) (by simpa using hw)
  exact hmv

/-- The labelled branch at the exact cosine value: A(-i sin δ) = -i δ for |δ| < π/8. -/
theorem branch_at_neg_I_sin {δ : ℂ} (hδ : ‖δ‖ < Real.pi / 8) :
    Complex.log (-Complex.I * Complex.sin δ +
        Complex.sqrt (1 + (-Complex.I * Complex.sin δ) ^ 2)) = -Complex.I * δ := by
  have hc : 0 < (Complex.cos δ).re := re_cos_pos hδ
  have h1 : 1 + (-Complex.I * Complex.sin δ) ^ 2 = Complex.cos δ ^ 2 := by
    linear_combination (-1 : ℂ) * Complex.sin_sq_add_cos_sq δ +
      Complex.sin δ ^ 2 * Complex.I_sq
  have h2 : -Complex.I * Complex.sin δ + Complex.cos δ = Complex.exp (-Complex.I * δ) := by
    rw [show -Complex.I * δ = (-δ) * Complex.I by ring, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg]
    ring
  rw [h1, sqrt_sq_of_re_pos _ hc, h2]
  have him : (-Complex.I * δ).im = -δ.re := by simp
  have hre : |δ.re| ≤ ‖δ‖ := Complex.abs_re_le_norm δ
  have hpi := Real.pi_pos
  have hre1 := neg_abs_le δ.re
  have hre2 := le_abs_self δ.re
  apply Complex.log_exp
  · rw [him]; linarith
  · rw [him]; linarith

/-- Pure chart comparison: the labelled primitive at the half-node a_j against a phase θ. -/
theorem chart_core (j : ℤ) (D θ : ℂ)
    (hD : ‖D / 2‖ < 1 / 2)
    (hθ : ‖θ - ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)‖ < Real.pi / 8) :
    ‖-Complex.I * (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)) +
        Complex.log (Complex.I * (-1 : ℂ) ^ j * D / 2 +
          Complex.sqrt (1 + (Complex.I * (-1 : ℂ) ^ j * D / 2) ^ 2)) +
        Complex.I * θ‖ ≤
      2 * ‖D - 2 * Complex.cos θ‖ := by
  obtain ⟨δ, rfl⟩ : ∃ δ : ℂ, θ = ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ :=
    ⟨θ - ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ), by ring⟩
  have hδ : ‖δ‖ < Real.pi / 8 := by simpa using hθ
  have hw : ‖Complex.I * (-1 : ℂ) ^ j * D / 2‖ < 1 / 2 := by
    rw [show Complex.I * (-1 : ℂ) ^ j * D / 2 = Complex.I * (-1 : ℂ) ^ j * (D / 2) by ring,
      norm_mul, norm_mul, Complex.norm_I, norm_neg_one_zpow, one_mul, one_mul]
    exact hD
  have hv : ‖-Complex.I * Complex.sin δ‖ < 1 / 2 := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact norm_sin_lt_half hδ
  have hA := branch_at_neg_I_sin hδ
  have hcos : Complex.I * (-1 : ℂ) ^ j *
      Complex.cos (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ) =
      -Complex.I * Complex.sin δ := by
    rw [cos_halfNode_add]
    linear_combination (-Complex.I * Complex.sin δ) * neg_one_zpow_mul_self j
  have e : -Complex.I * (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)) +
        Complex.log (Complex.I * (-1 : ℂ) ^ j * D / 2 +
          Complex.sqrt (1 + (Complex.I * (-1 : ℂ) ^ j * D / 2) ^ 2)) +
        Complex.I * (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ) =
      Complex.log (Complex.I * (-1 : ℂ) ^ j * D / 2 +
          Complex.sqrt (1 + (Complex.I * (-1 : ℂ) ^ j * D / 2) ^ 2)) -
        Complex.log (-Complex.I * Complex.sin δ +
          Complex.sqrt (1 + (-Complex.I * Complex.sin δ) ^ 2)) := by
    rw [hA]
    ring
  have hwv : Complex.I * (-1 : ℂ) ^ j * D / 2 - -Complex.I * Complex.sin δ =
      Complex.I * (-1 : ℂ) ^ j *
        ((D - 2 * Complex.cos (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ)) / 2) := by
    rw [← hcos]
    ring
  have hnorm : ‖Complex.I * (-1 : ℂ) ^ j * D / 2 - -Complex.I * Complex.sin δ‖ =
      ‖D - 2 * Complex.cos (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ)‖ / 2 := by
    rw [hwv, norm_mul, norm_mul, Complex.norm_I, norm_neg_one_zpow, one_mul, one_mul, norm_div,
      Complex.norm_ofNat]
  rw [e]
  calc _ ≤ 2 * ‖Complex.I * (-1 : ℂ) ^ j * D / 2 - -Complex.I * Complex.sin δ‖ :=
        branch_lipschitz hw hv
    _ = ‖D - 2 * Complex.cos (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ)‖ := by
        rw [hnorm]; ring
    _ ≤ 2 * ‖D - 2 * Complex.cos (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ)‖ := by
        linarith [norm_nonneg (D - 2 * Complex.cos (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ))]

/-! ### §5c Assembly arithmetic at a half-node -/

/-- At a half-node with phase error ≤ 1/8 and discriminant error ≤ 1/2:
    the sine lower bound and the chart's discriminant condition. -/
theorem halfNode_phase_consequences (j : ℤ) (θ D : ℂ) (E : ℝ)
    (hθ : ‖θ - ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)‖ ≤ 1 / 8)
    (hE : ‖D - 2 * Complex.cos θ‖ ≤ E) (hE2 : E ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ ‖Complex.sin θ‖ ∧ ‖D / 2‖ < 1 / 2 := by
  obtain ⟨δ, rfl⟩ : ∃ δ : ℂ, θ = ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ :=
    ⟨θ - ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ), by ring⟩
  have hδ : ‖δ‖ ≤ 1 / 8 := by simpa using hθ
  obtain ⟨hs, hc⟩ := small_phase_bounds hδ
  refine ⟨?_, ?_⟩
  · rw [sin_halfNode_add, norm_mul, norm_neg_one_zpow, one_mul]
    exact hc
  · have hcos : ‖Complex.cos (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ)‖ < 1 / 4 := by
      rw [cos_halfNode_add, norm_neg, norm_mul, norm_neg_one_zpow, one_mul]
      exact hs
    have e : D / 2 = (D - 2 * Complex.cos (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ)) / 2 +
        Complex.cos (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ) := by ring
    rw [e]
    have h2 : ‖(D - 2 * Complex.cos (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ)) / 2‖ ≤ E / 2 := by
      rw [norm_div, Complex.norm_ofNat]
      linarith
    calc _ ≤ ‖(D - 2 * Complex.cos (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ)) / 2‖ +
          ‖Complex.cos (((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ)‖ := norm_add_le _ _
      _ < 1 / 2 := by linarith

/-- A single natural threshold beyond which the half-node norm dominates three given constants. -/
theorem halfNode_threshold (A B C : ℝ) :
    ∃ J : ℕ, ∀ j : ℤ, J ≤ j.natAbs →
      A ≤ ‖((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)‖ ∧
      B ≤ ‖((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)‖ ∧
      C ≤ ‖((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)‖ := by
  refine ⟨⌈A⌉₊ + ⌈B⌉₊ + ⌈C⌉₊, fun j hj => ?_⟩
  have hX := natAbs_le_norm_halfNode_expr j
  have hJ : ((⌈A⌉₊ + ⌈B⌉₊ + ⌈C⌉₊ : ℕ) : ℝ) ≤ (j.natAbs : ℝ) := by exact_mod_cast hj
  push_cast at hJ
  have hA := Nat.le_ceil A
  have hB := Nat.le_ceil B
  have hC := Nat.le_ceil C
  have h0 : (0 : ℝ) ≤ (⌈A⌉₊ : ℝ) := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ (⌈B⌉₊ : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (⌈C⌉₊ : ℝ) := Nat.cast_nonneg _
  refine ⟨by linarith, by linarith, by linarith⟩

theorem div_le_of_mul_le_self {C X : ℝ} (r : ℝ) (hX : 0 < X) (hr : 0 < r) (h : C / r ≤ X) :
    C / X ≤ r := by
  rw [div_le_iff₀ hX]
  rw [div_le_iff₀ hr] at h
  linarith

theorem div_pow_le_of_le {C X : ℝ} (N : ℕ) (hN : 1 ≤ N) (hX : 1 ≤ X) (h : 2 * C ≤ X) :
    C / X ^ N ≤ 1 / 2 := by
  have hXN : X ≤ X ^ N := le_self_pow₀ hX (by omega)
  rw [div_le_iff₀ (pow_pos (by linarith) N)]
  linarith

end
end NlsGge.ThirdConsultation.KSPS031Analytic
