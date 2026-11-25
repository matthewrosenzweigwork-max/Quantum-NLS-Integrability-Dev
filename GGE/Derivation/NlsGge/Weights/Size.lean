import NlsGge.Weights.TiltedMoments
set_option autoImplicit false
noncomputable section
namespace NlsGge.Weights

lemma weight_abs (c : ℕ → ℝ) (r : ℝ) : weight c |r| = weight c r := by
  by_cases hr : 0 ≤ r
  · rw [abs_of_nonneg hr]
  · rw [abs_of_neg (lt_of_not_ge hr), weight_even]

lemma weight_uniform_large_size (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ c : ℕ → ℝ,
      (∀ j : ℕ, lower ≤ c j) → (∀ j : ℕ, c j ≤ upper) →
      ∀ r : ℝ, 16 ≤ |r| →
        A*|r|^(-3/4 : ℝ)*Real.exp (4*Real.sqrt |r|) ≤ weight c r ∧
        weight c r ≤ B*|r|^(-3/4 : ℝ)*Real.exp (4*Real.sqrt |r|) := by
  obtain ⟨A, B, hA, hB, hweighted⟩ := weightedPoissonFourth_uniform_bounds lower upper hlower hlower_upper
  refine ⟨A, B, hA, hB, ?_⟩
  intro c hbound hupper r hr
  have ht : 4 ≤ Real.sqrt |r| := Real.le_sqrt_of_sq_le (by norm_num; exact hr)
  have hp : (Real.sqrt |r|)^(-3/2 : ℝ) = |r|^(-3/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg r)]
    congr 1
    norm_num
  have hi : weight c r = Real.exp (4*Real.sqrt |r|)*
      (∑' j : ℕ, c j*(poissonTerm (Real.sqrt |r|) j)^4) := by
    calc
      weight c r = weight c |r| := (weight_abs c r).symm
      _ = weight c ((Real.sqrt |r|)^2) := congrArg (weight c) (Real.sq_sqrt (abs_nonneg r)).symm
      _ = _ := weight_poissonFourth_identity lower upper c hlower hbound hupper _ (Real.sqrt_nonneg _)
  have hb := hweighted c hbound hupper (Real.sqrt |r|) ht
  rw [hp] at hb
  constructor
  · rw [hi]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hb.1 (Real.exp_nonneg (4*Real.sqrt |r|))
  · rw [hi]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hb.2 (Real.exp_nonneg (4*Real.sqrt |r|))

lemma weight_two_sided_size (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ c : ℕ → ℝ,
      (∀ j : ℕ, lower ≤ c j) → (∀ j : ℕ, c j ≤ upper) →
      ∀ r : ℝ,
        A*(1+|r|)^(-3/4 : ℝ)*Real.exp (4*Real.sqrt |r|) ≤ weight c r ∧
        weight c r ≤ B*(1+|r|)^(-3/4 : ℝ)*Real.exp (4*Real.sqrt |r|) := by
  obtain ⟨A₀, B₀, hA₀, hB₀, hlarge⟩ := weight_uniform_large_size lower upper hlower hlower_upper
  let A := min A₀ (lower*Real.exp (-16))
  let B := max (B₀*(2 : ℝ)^(3/4 : ℝ)) (upper*(17 : ℝ)^(3/4 : ℝ))
  have hu : 0 < upper := hlower.trans_le hlower_upper
  have hA : 0 < A := lt_min_iff.mpr ⟨hA₀, mul_pos hlower (Real.exp_pos _)⟩
  have hB : 0 < B := lt_of_lt_of_le (mul_pos hB₀ (Real.rpow_pos_of_pos (by norm_num) _)) (le_max_left _ _)
  refine ⟨A, B, hA, hB, ?_⟩
  intro c hbound hupper r
  have hp0 : 0 < (1+|r|)^(-3/4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have he0 : 0 < Real.exp (4*Real.sqrt |r|) := Real.exp_pos _
  by_cases hr : 16 ≤ |r|
  · have habs : 0 < |r| := by linarith
    have hp1 : (1+|r|)^(-3/4 : ℝ) ≤ |r|^(-3/4 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos habs (by linarith) (by norm_num)
    have hp2 : |r|^(-3/4 : ℝ) ≤ (2 : ℝ)^(3/4 : ℝ)*(1+|r|)^(-3/4 : ℝ) := by
      have hm := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1+|r|)
        (by linarith : 1+|r| ≤ 2*|r|) (by norm_num : (-3/4 : ℝ) ≤ 0)
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) habs.le] at hm
      have hc : (2 : ℝ)^(3/4 : ℝ)*(2 : ℝ)^(-3/4 : ℝ) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
      simpa only [← mul_assoc, hc, one_mul] using
        mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (3/4 : ℝ))
    constructor
    · calc
        A*(1+|r|)^(-3/4 : ℝ)*Real.exp (4*Real.sqrt |r|) ≤
          A₀*|r|^(-3/4 : ℝ)*Real.exp (4*Real.sqrt |r|) :=
            mul_le_mul_of_nonneg_right (mul_le_mul (min_le_left _ _) hp1 hp0.le hA₀.le) he0.le
        _ ≤ weight c r := (hlarge c hbound hupper r hr).1
    · calc
        weight c r ≤ B₀*|r|^(-3/4 : ℝ)*Real.exp (4*Real.sqrt |r|) := (hlarge c hbound hupper r hr).2
        _ ≤ (B₀*(2 : ℝ)^(3/4 : ℝ))*(1+|r|)^(-3/4 : ℝ)*Real.exp (4*Real.sqrt |r|) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hp2 hB₀.le) he0.le
        _ ≤ B*(1+|r|)^(-3/4 : ℝ)*Real.exp (4*Real.sqrt |r|) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hp0.le) he0.le
  · have hrsmall : |r| ≤ 16 := (lt_of_not_ge hr).le
    have hsqrt : Real.sqrt |r| ≤ 4 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; exact hrsmall⟩
    have he : Real.exp (4*Real.sqrt |r|) ≤ Real.exp 16 := Real.exp_le_exp.mpr (by linarith)
    have hp1 : (1+|r|)^(-3/4 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg r]) (by norm_num)
    have hp2 : (17 : ℝ)^(-3/4 : ℝ) ≤ (1+|r|)^(-3/4 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    have hcancel : (17 : ℝ)^(3/4 : ℝ)*(17 : ℝ)^(-3/4 : ℝ) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 17)]
      norm_num
    have hupperconstant : upper ≤ B*(1+|r|)^(-3/4 : ℝ) := by
      calc
        upper = (upper*(17 : ℝ)^(3/4 : ℝ))*(17 : ℝ)^(-3/4 : ℝ) := by rw [mul_assoc, hcancel, mul_one]
        _ ≤ B*(1+|r|)^(-3/4 : ℝ) := mul_le_mul (le_max_right _ _) hp2
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 17) _) hB.le
    constructor
    · calc
        A*(1+|r|)^(-3/4 : ℝ)*Real.exp (4*Real.sqrt |r|) ≤
          (lower*Real.exp (-16))*Real.exp 16 :=
            mul_le_mul ((mul_le_mul_of_nonneg_left hp1 hA.le).trans
              (by simpa only [mul_one] using min_le_right A₀ (lower*Real.exp (-16)))) he he0.le
              (mul_nonneg hlower.le (Real.exp_nonneg _))
        _ = lower := by
          rw [mul_assoc, ← Real.exp_add]
          norm_num
        _ ≤ weight c r := weight_lower lower upper c hlower hbound hupper r
    · exact (weight_upper lower upper c hlower hbound hupper r).trans
        (mul_le_mul_of_nonneg_right hupperconstant he0.le)

end NlsGge.Weights
