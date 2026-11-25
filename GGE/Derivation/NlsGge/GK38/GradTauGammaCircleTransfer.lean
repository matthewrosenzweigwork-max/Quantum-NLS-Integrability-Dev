import NlsGge.GK38.GradFundamentalGradientSeq
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! K4a: compact-circle maxima transfer genuine arbitrary shifted-sequence
estimates to contour estimates. No uniform tail assertion is used. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

/-- A scalar contour square bound from a bound valid for every choice of one
point on each circle. The radii have one common bound. -/
theorem k4aScalarCircleSequence38 (c : ℤ → ℂ) (r : ℤ → ℝ)
    (F : ℤ → ℂ → ℂ) (A B : ℝ)
    (hr : ∀ n, 0 < r n) (hA : 0 ≤ A) (hrA : ∀ n, r n ≤ A)
    (hF : ∀ n, ContinuousOn (F n) (sphere (c n) (r n)))
    (hseq : ∀ υ : ℤ → ℂ, (∀ n, υ n ∈ sphere (c n) (r n)) →
      k1SquareBound38 (fun n => ‖F n (υ n)‖ ^ 2) B) :
    (∀ n, CircleIntegrable (F n) (c n) (r n)) ∧
      k1SquareBound38 (fun n =>
        ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * circleIntegral (F n) (c n) (r n)‖ ^ 2)
        (A ^ 2 * B) := by
  classical
  have hm (n : ℤ) : ∃ z ∈ sphere (c n) (r n),
      ∀ w ∈ sphere (c n) (r n), ‖F n w‖ ≤ ‖F n z‖ :=
    (isCompact_sphere (c n) (r n)).exists_isMaxOn
      (NormedSpace.sphere_nonempty.mpr (hr n).le) (hF n).norm
  choose υ hυ hmax using hm
  have hs := hseq υ hυ
  refine ⟨fun n => (hF n).circleIntegrable (hr n).le,
    k1SquareBound38_of_finite (fun n => sq_nonneg _) ?_⟩
  intro T
  have hp (n : ℤ) :
      ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * circleIntegral (F n) (c n) (r n)‖ ^ 2 ≤
        A ^ 2 * ‖F n (υ n)‖ ^ 2 := by
    have hi :
        ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * circleIntegral (F n) (c n) (r n)‖ ≤
          A * ‖F n (υ n)‖ := by
      exact (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
        (hr n).le (hmax n)).trans
          (mul_le_mul_of_nonneg_right (hrA n) (norm_nonneg _))
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hi 2
  calc
    _ ≤ ∑ n ∈ T, A ^ 2 * ‖F n (υ n)‖ ^ 2 :=
      Finset.sum_le_sum fun n _ => hp n
    _ = A ^ 2 * ∑ n ∈ T, ‖F n (υ n)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ A ^ 2 * B := mul_le_mul_of_nonneg_left (hs.1 T) (sq_nonneg A)

/-- A common scalar weight does not change the quantifier order of a genuine
all-selections square estimate. -/
theorem k4aWeightedSequence38 (S : ℤ → Set ℂ) (F a : ℤ → ℂ → ℂ)
    (A B : ℝ) (hA : 0 ≤ A)
    (ha : ∀ n z, z ∈ S n → ‖a n z‖ ≤ A)
    (hseq : ∀ υ : ℤ → ℂ, (∀ n, υ n ∈ S n) →
      k1SquareBound38 (fun n => ‖F n (υ n)‖ ^ 2) B) :
    ∀ υ : ℤ → ℂ, (∀ n, υ n ∈ S n) →
      k1SquareBound38 (fun n => ‖a n (υ n) * F n (υ n)‖ ^ 2) (A ^ 2 * B) := by
  intro υ hυ
  have hs := hseq υ hυ
  apply k1SquareBound38_of_finite (fun n => sq_nonneg _)
  intro T
  calc
    _ ≤ ∑ n ∈ T, A ^ 2 * ‖F n (υ n)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (ha n (υ n) (hυ n)) 2) (sq_nonneg _)
    _ = A ^ 2 * ∑ n ∈ T, ‖F n (υ n)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ A ^ 2 * B := mul_le_mul_of_nonneg_left (hs.1 T) (sq_nonneg A)

/-- The actual K1 bound controls either unscaled component, still for every
bounded complex shift sequence and every closed-unit time. -/
theorem k4aDiscrimComponentSequence38 (R c : ℝ) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ φ : PotPair, ‖φ‖ ≤ R → ∀ υ : ℤ → ℂ,
      (∀ n, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
      ∀ t : Icc (0 : ℝ) 1, ∀ i : Fin 2,
        k1SquareBound38 (fun n => ‖gradDiscrim38 φ (υ n) t i‖ ^ 2) B := by
  obtain ⟨B, hB, hs⟩ := gradDiscrim_l2 R c
  refine ⟨B, hB, fun φ hφ υ hυ t i => ?_⟩
  have h := hs φ hφ υ hυ t
  apply k1SquareBound38_of_finite (fun n => sq_nonneg _)
  intro T
  apply le_trans (Finset.sum_le_sum (fun n _ => ?_)) (h.1 T)
  simp only [Pi.smul_apply, norm_smul, Complex.norm_I, one_mul]
  fin_cases i
  · exact le_add_of_nonneg_right (sq_nonneg _)
  · exact le_add_of_nonneg_left (sq_nonneg _)

end
end NlsGge.GK38
