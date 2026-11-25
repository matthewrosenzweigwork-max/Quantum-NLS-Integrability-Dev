import NlsGge.Weights.TiltedMoments
import NlsGge.Weights.SecondDerivative
set_option autoImplicit false
noncomputable section
namespace NlsGge.Weights

lemma weight_secondDerivative_normalized_eq (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) (hr : 0 < r) :
    deriv (deriv (weight c)) r / weight c r =
      (4*(∑' j : ℕ, (j : ℝ)^2*probabilityTerm c r j) -
        2*(∑' j : ℕ, (j : ℝ)*probabilityTerm c r j)) / r^2 := by
  have hW := (weight_pos lower upper c hlower hbound hupper r).ne'
  have hs2 : Summable (fun j : ℕ => (j : ℝ)^2*weightTerm c r j) := by
    have hs := (probabilityTerm_secondMoment_summable lower upper c hlower hbound hupper r).mul_right (weight c r)
    simpa only [probabilityTerm, mul_assoc, div_mul_cancel₀ _ hW] using hs
  have hs1 := firstMoment_summable lower upper c hlower hbound hupper r
  have hp2 : (∑' j : ℕ, (j : ℝ)^2*probabilityTerm c r j) =
      (∑' j : ℕ, (j : ℝ)^2*weightTerm c r j)/weight c r := by
    simp only [probabilityTerm, ← mul_div_assoc]
    exact (hs2.hasSum.div_const (weight c r)).tsum_eq
  have hp : (∑' j : ℕ, (2*(j : ℝ))*(2*(j : ℝ)-1)*weightTerm c r j) =
      4*(∑' j : ℕ, (j : ℝ)^2*weightTerm c r j)-
        2*(∑' j : ℕ, (j : ℝ)*weightTerm c r j) :=
    (((hs2.hasSum.mul_left 4).sub (hs1.hasSum.mul_left 2)).congr_fun (fun j => by ring)).tsum_eq
  have hm := weight_secondDerivative_mul lower upper c hlower hbound hupper r
  rw [hp] at hm
  rw [hp2, probabilityTerm_firstMoment_tsum lower upper c hlower hbound hupper r]
  field_simp [hr.ne', hW]
  nlinarith [hm]

lemma weight_uniform_derivative_asymptotics (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℕ → ℝ,
      (∀ j : ℕ, lower ≤ c j) → (∀ j : ℕ, c j ≤ upper) →
      ∀ r : ℝ, 16 ≤ r →
        |deriv (weight c) r / weight c r - 2*r^(-1/2 : ℝ)| ≤ C*r^(-3/4 : ℝ) ∧
        |deriv (deriv (weight c)) r / weight c r - 4/r| ≤ C*r^(-5/4 : ℝ) := by
  obtain ⟨M, hM, hmom⟩ := probabilityTerm_uniform_firstSecondMoments lower upper hlower hlower_upper
  refine ⟨6*M+2, by positivity, ?_⟩
  intro c hbound hupper r hr
  have hr0 : 0 < r := by linarith
  have ht : 4 ≤ Real.sqrt r := Real.le_sqrt_of_sq_le (by norm_num; exact hr)
  have hsq := Real.sq_sqrt hr0.le
  have hm := hmom c hbound hupper (Real.sqrt r) ht
  rw [hsq] at hm
  have hp1 : Real.sqrt r/r = r^(-1/2 : ℝ) := by
    rw [div_eq_mul_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add hr0]
    congr 1
    norm_num
  have hp3 : (2/r)*(M*Real.sqrt (Real.sqrt r)) = 2*M*r^(-3/4 : ℝ) := by
    rw [div_eq_mul_inv, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hr0.le, ← Real.rpow_neg_one]
    calc
      2*r^(-1 : ℝ)*(M*r^((1/2 : ℝ)*(1/2))) =
        (2*M)*(r^(-1 : ℝ)*r^((1/2 : ℝ)*(1/2))) := by ring
      _ = _ := by rw [← Real.rpow_add hr0]; norm_num
  have hp5 : (4/r^2)*(M*(Real.sqrt r)^(3/2 : ℝ)) = 4*M*r^(-5/4 : ℝ) := by
    rw [div_eq_mul_inv, Real.sqrt_eq_rpow, ← Real.rpow_mul hr0.le]
    have hi : (r^2)⁻¹ = r^(-2 : ℝ) := by
      rw [Real.rpow_neg hr0.le, Real.rpow_ofNat]
    rw [hi]
    calc
      4*r^(-2 : ℝ)*(M*r^((1/2 : ℝ)*(3/2))) =
        (4*M)*(r^(-2 : ℝ)*r^((1/2 : ℝ)*(3/2))) := by ring
      _ = _ := by rw [← Real.rpow_add hr0]; norm_num
  have hsmall1 : (2/r^2)*Real.sqrt r ≤ 2*r^(-5/4 : ℝ) := by
    have he : (2/r^2)*Real.sqrt r = 2*r^(-3/2 : ℝ) := by
      rw [div_eq_mul_inv, Real.sqrt_eq_rpow]
      have hi : (r^2)⁻¹ = r^(-2 : ℝ) := by rw [Real.rpow_neg hr0.le, Real.rpow_ofNat]
      rw [hi]
      calc
        2*r^(-2 : ℝ)*r^(1/2 : ℝ) = 2*(r^(-2 : ℝ)*r^(1/2 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hr0]; norm_num
    rw [he]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)) (by norm_num)
  have hsmall2 : (2/r^2)*(M*Real.sqrt (Real.sqrt r)) ≤ 2*M*r^(-5/4 : ℝ) := by
    have he : (2/r^2)*(M*Real.sqrt (Real.sqrt r)) = 2*M*r^(-7/4 : ℝ) := by
      rw [div_eq_mul_inv, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hr0.le]
      have hi : (r^2)⁻¹ = r^(-2 : ℝ) := by rw [Real.rpow_neg hr0.le, Real.rpow_ofNat]
      rw [hi]
      calc
        2*r^(-2 : ℝ)*(M*r^((1/2 : ℝ)*(1/2))) = (2*M)*(r^(-2 : ℝ)*r^((1/2 : ℝ)*(1/2))) := by ring
        _ = _ := by rw [← Real.rpow_add hr0]; norm_num
    rw [he]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)) (by positivity)
  constructor
  · have he : deriv (weight c) r / weight c r - 2*r^(-1/2 : ℝ) =
        (2/r)*((∑' j : ℕ, (j : ℝ)*probabilityTerm c r j)-Real.sqrt r) := by
      rw [weight_logDerivative_eq lower upper c hlower hbound hupper r hr0]
      rw [← hp1]
      ring
    rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2/r)]
    calc
      _ ≤ (2/r)*(M*Real.sqrt (Real.sqrt r)) := mul_le_mul_of_nonneg_left hm.1 (by positivity)
      _ = 2*M*r^(-3/4 : ℝ) := hp3
      _ ≤ (6*M+2)*r^(-3/4 : ℝ) := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hr0.le _)
  · have he : deriv (deriv (weight c)) r / weight c r - 4/r =
        (4/r^2)*((∑' j : ℕ, (j : ℝ)^2*probabilityTerm c r j)-r) -
          (2/r^2)*(∑' j : ℕ, (j : ℝ)*probabilityTerm c r j) := by
      rw [weight_secondDerivative_normalized_eq lower upper c hlower hbound hupper r hr0]
      field_simp [hr0.ne']
      <;> ring
    have hmean : (∑' j : ℕ, (j : ℝ)*probabilityTerm c r j) ≤
        Real.sqrt r+M*Real.sqrt (Real.sqrt r) := by
      have hi := le_abs_self ((∑' j : ℕ, (j : ℝ)*probabilityTerm c r j)-Real.sqrt r)
      linarith [hm.1]
    have hmean0 : 0 ≤ (∑' j : ℕ, (j : ℝ)*probabilityTerm c r j) :=
      tsum_nonneg (fun j => mul_nonneg (Nat.cast_nonneg j) (probabilityTerm_nonneg lower upper c hlower hbound hupper r j))
    rw [he]
    calc
      _ ≤ |(4/r^2)*((∑' j : ℕ, (j : ℝ)^2*probabilityTerm c r j)-r)| +
        |(2/r^2)*(∑' j : ℕ, (j : ℝ)*probabilityTerm c r j)| :=
          abs_sub ((4/r^2)*((∑' j : ℕ, (j : ℝ)^2*probabilityTerm c r j)-r))
            ((2/r^2)*(∑' j : ℕ, (j : ℝ)*probabilityTerm c r j))
      _ ≤ (4/r^2)*(M*(Real.sqrt r)^(3/2 : ℝ))+
        (2/r^2)*(Real.sqrt r+M*Real.sqrt (Real.sqrt r)) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4/r^2),
            abs_of_nonneg (by positivity : 0 ≤ 2/r^2), abs_of_nonneg hmean0]
          exact add_le_add (mul_le_mul_of_nonneg_left hm.2 (by positivity))
            (mul_le_mul_of_nonneg_left hmean (by positivity))
      _ ≤ 4*M*r^(-5/4 : ℝ)+2*r^(-5/4 : ℝ)+2*M*r^(-5/4 : ℝ) := by
        rw [hp5, mul_add]
        linarith [hsmall1, hsmall2]
      _ = (6*M+2)*r^(-5/4 : ℝ) := by ring

end NlsGge.Weights
