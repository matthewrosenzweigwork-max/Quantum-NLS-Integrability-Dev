import NlsGge.Weights.Entire
import NlsGge.Weights.ComplexEntire
import Mathlib.Analysis.Complex.RealDeriv

/-! Source NEW-F01 full normalization, actual infinite Hölder and finite derivative leaves.
The positive coefficient interval precedes the sequence; zero modes are retained. -/
set_option autoImplicit false
noncomputable section
namespace NlsGge.Weights

def probabilityTerm (c : ℕ → ℝ) (r : ℝ) (j : ℕ) : ℝ :=
  weightTerm c r j / weight c r

lemma probabilityTerm_nonneg (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) (j : ℕ) :
    0 ≤ probabilityTerm c r j :=
  div_nonneg (weightTerm_nonneg lower c hlower hbound r j)
    (weight_pos lower upper c hlower hbound hupper r).le

lemma probabilityTerm_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) : Summable (probabilityTerm c r) :=
  (weightTerm_summable lower upper c hlower hbound hupper r).div_const (weight c r)

lemma probabilityTerm_hasSum (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) : HasSum (probabilityTerm c r) 1 := by
  have hs := (weightTerm_summable lower upper c hlower hbound hupper r).hasSum.div_const (weight c r)
  change HasSum (probabilityTerm c r) (weight c r / weight c r) at hs
  simpa only [div_self (weight_pos lower upper c hlower hbound hupper r).ne'] using hs

lemma probabilityTerm_fourthMoment_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    Summable (fun j : ℕ => (j : ℝ) ^ 4 * probabilityTerm c r j) := by
  simpa only [probabilityTerm, mul_div_assoc] using
    (fourthMoment_summable lower upper c hlower hbound hupper r).div_const (weight c r)

lemma probabilityTerm_fourthMoment_le (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    (∑' j : ℕ, (j : ℝ) ^ 4 * probabilityTerm c r j) ≤ (upper / lower) * r ^ 2 := by
  simp only [probabilityTerm, ← mul_div_assoc]
  rw [((fourthMoment_summable lower upper c hlower hbound hupper r).hasSum.div_const (weight c r)).tsum_eq]
  apply (div_le_iff₀ (weight_pos lower upper c hlower hbound hupper r)).2
  exact fourthMoment_le lower upper c hlower hbound hupper r

lemma probabilityTerm_firstMoment_holder (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    Summable (fun j : ℕ => (j : ℝ) * probabilityTerm c r j) ∧
    (∑' j : ℕ, (j : ℝ) * probabilityTerm c r j) ≤
      ((upper / lower) * r ^ 2) ^ (1 / 4 : ℝ) := by
  let b := probabilityTerm c r
  let f := fun j : ℕ => (j : ℝ) * b j ^ (1 / 4 : ℝ)
  let g := fun j : ℕ => b j ^ (3 / 4 : ℝ)
  have hb (j : ℕ) : 0 ≤ b j := probabilityTerm_nonneg lower upper c hlower hbound hupper r j
  have hf (j : ℕ) : 0 ≤ f j := mul_nonneg (Nat.cast_nonneg j) (Real.rpow_nonneg (hb j) _)
  have hg (j : ℕ) : 0 ≤ g j := Real.rpow_nonneg (hb j) _
  have hF (j : ℕ) : f j ^ (4 : ℝ) = (j : ℝ) ^ (4 : ℕ) * b j := by
    dsimp [f]
    rw [Real.mul_rpow (Nat.cast_nonneg j) (Real.rpow_nonneg (hb j) _),
      ← Real.rpow_mul (hb j), show (1 / 4 : ℝ) * 4 = 1 by norm_num, Real.rpow_one]
    simp only [Real.rpow_ofNat]
  have hG (j : ℕ) : g j ^ (4 / 3 : ℝ) = b j := by
    dsimp [g]
    rw [← Real.rpow_mul (hb j), show (3 / 4 : ℝ) * (4 / 3) = 1 by norm_num, Real.rpow_one]
  have hprod (j : ℕ) : f j * g j = (j : ℝ) * b j := by
    dsimp [f, g]
    rw [mul_assoc, ← Real.rpow_add' (hb j) (by norm_num : (1 / 4 : ℝ) + 3 / 4 ≠ 0),
      show (1 / 4 : ℝ) + 3 / 4 = 1 by norm_num, Real.rpow_one]
  have hFsum : Summable (fun j : ℕ => f j ^ (4 : ℝ)) := by
    simp only [hF]
    exact probabilityTerm_fourthMoment_summable lower upper c hlower hbound hupper r
  have hGsum : Summable (fun j : ℕ => g j ^ (4 / 3 : ℝ)) := by
    simp only [hG]
    exact probabilityTerm_summable lower upper c hlower hbound hupper r
  have hpq : Real.HolderConjugate (4 : ℝ) (4 / 3) :=
    Real.holderConjugate_iff.mpr (by norm_num)
  have hbsum : (∑' j : ℕ, b j) = 1 :=
    (probabilityTerm_hasSum lower upper c hlower hbound hupper r).tsum_eq
  have hholder := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hFsum hGsum
  constructor
  · simpa only [hprod] using hholder.1
  · have hfirst : (∑' j : ℕ, (j : ℝ) * b j) ≤
        (∑' j : ℕ, (j : ℝ) ^ 4 * b j) ^ (1 / 4 : ℝ) := by
      simpa only [hprod, hF, hG, hbsum,
        Real.one_rpow, mul_one] using hholder.2
    exact hfirst.trans (Real.rpow_le_rpow (tsum_nonneg (fun j => mul_nonneg (by positivity) (hb j)))
      (probabilityTerm_fourthMoment_le lower upper c hlower hbound hupper r) (by norm_num))

end NlsGge.Weights

namespace NlsGge.Weights

lemma weightTerm_norm_le (lower : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (R : ℝ) (hR : 0 ≤ R) (r : ℝ) (hr : |r| ≤ R) (j : ℕ) :
    ‖weightTerm c r j‖ ≤ weightTerm c R j := by
  simp only [weightTerm, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_of_pos (coefficient_pos lower c hlower hbound j)]
  apply mul_le_mul_of_nonneg_left _ (coefficient_pos lower c hlower hbound j).le
  exact pow_le_pow_left₀ (abs_nonneg r) hr (2 * j)

lemma weightSeries_tendstoUniformlyOn (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun N : ℕ => fun r : ℝ => ∑ j ∈ Finset.range N, weightTerm c r j)
      (weight c) Filter.atTop (Set.Icc (-R) R) := by
  apply tendstoUniformlyOn_tsum_nat (weightTerm_summable lower upper c hlower hbound hupper R)
  intro j r hr
  apply weightTerm_norm_le lower c hlower hbound R hR r
  exact abs_le.mpr ⟨hr.1, hr.2⟩

end NlsGge.Weights

namespace NlsGge.Weights

def weightTermDerivative (c : ℕ → ℝ) (r : ℝ) (j : ℕ) : ℝ :=
  coefficient c j * ((2 * j : ℕ) : ℝ) * r ^ (2 * j - 1)

lemma weightTerm_hasDerivAt (c : ℕ → ℝ) (r : ℝ) (j : ℕ) :
    HasDerivAt (fun x : ℝ => weightTerm c x j) (weightTermDerivative c r j) r := by
  convert (hasDerivAt_pow (2 * j) r).const_mul (coefficient c j) using 1
  · rfl
  · unfold weightTermDerivative
    ring

lemma partialWeight_hasDerivAt (c : ℕ → ℝ) (m : ℕ) (r : ℝ) :
    HasDerivAt (partialWeight c m)
      (∑ j ∈ Finset.range (m + 1), weightTermDerivative c r j) r := by
  exact HasDerivAt.fun_sum (u := Finset.range (m + 1)) (fun j hj => weightTerm_hasDerivAt c r j)

lemma weightTermDerivative_mul (c : ℕ → ℝ) (r : ℝ) (j : ℕ) :
    r * weightTermDerivative c r j = 2 * (j : ℝ) * weightTerm c r j := by
  cases j with
  | zero => simp [weightTermDerivative]
  | succ j =>
    unfold weightTermDerivative weightTerm
    rw [show 2 * (j + 1) = 2 * j + 2 by omega]
    have hp : r * r ^ (2 * j + 2 - 1) = r ^ (2 * j + 2) := by
      rw [← pow_succ']
      congr 1
    calc
      r * (coefficient c (j + 1) * ((2 * j + 2 : ℕ) : ℝ) * r ^ (2 * j + 2 - 1)) =
        coefficient c (j + 1) * ((2 * j + 2 : ℕ) : ℝ) *
          (r * r ^ (2 * j + 2 - 1)) := by ring
      _ = _ := by rw [hp]; push_cast; ring

lemma partialWeight_deriv_mul (c : ℕ → ℝ) (m : ℕ) (r : ℝ) :
    r * deriv (partialWeight c m) r =
      2 * ∑ j ∈ Finset.range (m + 1), (j : ℝ) * weightTerm c r j := by
  rw [(partialWeight_hasDerivAt c m r).deriv, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [mul_assoc] using weightTermDerivative_mul c r j

end NlsGge.Weights

namespace NlsGge.Weights

lemma partialWeight_logDerivative_eq (lower : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (m : ℕ) (r : ℝ) (hr : 0 < r) :
    deriv (partialWeight c m) r / partialWeight c m r =
      (2 / r) * ∑ j ∈ Finset.range (m + 1), partialProbabilityTerm c m r j * (j : ℝ) := by
  have hW := (partialWeight_pos lower c hlower hbound m r).ne'
  have hsum : (∑ j ∈ Finset.range (m + 1), partialProbabilityTerm c m r j * (j : ℝ)) =
      (∑ j ∈ Finset.range (m + 1), (j : ℝ) * weightTerm c r j) / partialWeight c m r := by
    simp only [partialProbabilityTerm, div_mul_eq_mul_div, ← Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  field_simp [hr.ne', hW]
  nlinarith [partialWeight_deriv_mul c m r]

lemma partialWeight_logDerivative_nonneg (lower : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (m : ℕ) (r : ℝ) (hr : 0 < r) :
    0 ≤ deriv (partialWeight c m) r / partialWeight c m r := by
  rw [partialWeight_logDerivative_eq lower c hlower hbound m r hr]
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun j hj =>
    mul_nonneg (partialProbabilityTerm_nonneg lower c hlower hbound m r j) (Nat.cast_nonneg j))

lemma partialWeight_logDerivative_le_momentBound (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (m : ℕ) (r : ℝ) (hr : 0 < r) :
    deriv (partialWeight c m) r / partialWeight c m r ≤
      (2 / r) * (((upper / lower) * r ^ 2) ^ (1 / 4 : ℝ)) := by
  rw [partialWeight_logDerivative_eq lower c hlower hbound m r hr]
  exact mul_le_mul_of_nonneg_left
    (partialProbabilityTerm_firstMoment_le lower upper c hlower hbound hupper m r) (by positivity)

end NlsGge.Weights

namespace NlsGge.Weights

lemma partialWeight_logDerivative_le (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (m : ℕ) (r : ℝ) (hr : 0 < r) :
    deriv (partialWeight c m) r / partialWeight c m r ≤
      (2 * (upper / lower) ^ (1 / 4 : ℝ)) * r ^ (-1 / 2 : ℝ) := by
  have hu : 0 ≤ upper := (hlower.trans_le ((hbound 0).trans (hupper 0))).le
  have hp : (r ^ (2 : ℕ)) ^ (1 / 4 : ℝ) = r ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    norm_num
  have hinv : r ^ (-1 : ℝ) * r ^ (1 / 2 : ℝ) = r ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_add hr]
    norm_num
  calc
    deriv (partialWeight c m) r / partialWeight c m r ≤
      (2 / r) * (((upper / lower) * r ^ 2) ^ (1 / 4 : ℝ)) :=
        partialWeight_logDerivative_le_momentBound lower upper c hlower hbound hupper m r hr
    _ = (2 / r) * ((upper / lower) ^ (1 / 4 : ℝ) * r ^ (1 / 2 : ℝ)) := by
      rw [Real.mul_rpow (div_nonneg hu hlower.le) (sq_nonneg r), hp]
    _ = (2 * (upper / lower) ^ (1 / 4 : ℝ)) *
      (r ^ (-1 : ℝ) * r ^ (1 / 2 : ℝ)) := by
      rw [Real.rpow_neg_one]
      ring
    _ = _ := by rw [hinv]

@[simp] lemma partialWeight_deriv_order_zero (c : ℕ → ℝ) (r : ℝ) :
    deriv (partialWeight c 0) r = 0 := by
  rw [(partialWeight_hasDerivAt c 0 r).deriv]
  simp [weightTermDerivative]

end NlsGge.Weights

namespace NlsGge.Weights

lemma complexWeightTermDerivative_ofReal (c : ℕ → ℝ) (r : ℝ) (j : ℕ) :
    complexWeightTermDerivative c (r : ℂ) j = (weightTermDerivative c r j : ℂ) := by
  simp [complexWeightTermDerivative, weightTermDerivative]

lemma weightTermDerivative_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) : Summable (weightTermDerivative c r) := by
  apply Complex.summable_ofReal.mp
  exact (complexWeightTermDerivative_summable lower upper c hlower hbound hupper (r : ℂ)).congr
    (fun j => complexWeightTermDerivative_ofReal c r j)

lemma weight_hasDerivAt (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    HasDerivAt (weight c) (∑' j, weightTermDerivative c r j) r := by
  have hc := complexWeightTermDerivative_summable lower upper c hlower hbound hupper (r : ℂ)
  have hr := (complexWeight_hasDerivAt lower upper c hlower hbound hupper (r : ℂ)).real_of_complex
  have hsum : (∑' j, complexWeightTermDerivative c (r : ℂ) j).re = ∑' j, weightTermDerivative c r j := by
    rw [Complex.re_tsum hc]
    apply tsum_congr
    intro j
    simp only [complexWeightTermDerivative_ofReal, Complex.ofReal_re]
  simpa only [complexWeight_ofReal lower upper c hlower hbound hupper, Complex.ofReal_re, hsum] using hr

lemma firstMoment_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    Summable (fun j : ℕ => (j : ℝ) * weightTerm c r j) := by
  have hW := (weight_pos lower upper c hlower hbound hupper r).ne'
  have hs := (probabilityTerm_firstMoment_holder lower upper c hlower hbound hupper r).1.mul_right (weight c r)
  simpa only [probabilityTerm, mul_assoc, div_mul_cancel₀ _ hW] using hs

lemma probabilityTerm_firstMoment_tsum (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    (∑' j : ℕ, (j : ℝ) * probabilityTerm c r j) =
      (∑' j : ℕ, (j : ℝ) * weightTerm c r j) / weight c r := by
  simp only [probabilityTerm, ← mul_div_assoc]
  exact ((firstMoment_summable lower upper c hlower hbound hupper r).hasSum.div_const (weight c r)).tsum_eq

lemma weight_deriv_mul (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    r * deriv (weight c) r = 2 * ∑' j : ℕ, (j : ℝ) * weightTerm c r j := by
  rw [(weight_hasDerivAt lower upper c hlower hbound hupper r).deriv,
    ← (weightTermDerivative_summable lower upper c hlower hbound hupper r).tsum_mul_left]
  calc
    (∑' j : ℕ, r * weightTermDerivative c r j) =
      ∑' j : ℕ, 2 * ((j : ℝ) * weightTerm c r j) := by
        apply tsum_congr
        intro j
        rw [weightTermDerivative_mul]
        ring
    _ = _ := (firstMoment_summable lower upper c hlower hbound hupper r).tsum_mul_left 2

lemma weight_logDerivative_eq (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) (hr : 0 < r) :
    deriv (weight c) r / weight c r = (2 / r) * ∑' j : ℕ, (j : ℝ) * probabilityTerm c r j := by
  have hW := (weight_pos lower upper c hlower hbound hupper r).ne'
  rw [probabilityTerm_firstMoment_tsum lower upper c hlower hbound hupper r]
  field_simp [hr.ne', hW]
  nlinarith [weight_deriv_mul lower upper c hlower hbound hupper r]

lemma weight_logDerivative_nonneg (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) (hr : 0 < r) :
    0 ≤ deriv (weight c) r / weight c r := by
  rw [weight_logDerivative_eq lower upper c hlower hbound hupper r hr]
  apply mul_nonneg (by positivity)
  exact tsum_nonneg (fun j => mul_nonneg (Nat.cast_nonneg j)
    (probabilityTerm_nonneg lower upper c hlower hbound hupper r j))

lemma weight_logDerivative_le (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) (hr : 0 < r) :
    deriv (weight c) r / weight c r ≤
      (2 * (upper / lower) ^ (1 / 4 : ℝ)) * r ^ (-1 / 2 : ℝ) := by
  have hu : 0 ≤ upper := (hlower.trans_le ((hbound 0).trans (hupper 0))).le
  have hp : (r ^ (2 : ℕ)) ^ (1 / 4 : ℝ) = r ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    norm_num
  have hinv : r ^ (-1 : ℝ) * r ^ (1 / 2 : ℝ) = r ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_add hr]
    norm_num
  calc
    deriv (weight c) r / weight c r = (2 / r) * ∑' j : ℕ, (j : ℝ) * probabilityTerm c r j :=
      weight_logDerivative_eq lower upper c hlower hbound hupper r hr
    _ ≤ (2 / r) * (((upper / lower) * r ^ 2) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (probabilityTerm_firstMoment_holder lower upper c hlower hbound hupper r).2
        (by positivity)
    _ = (2 / r) * ((upper / lower) ^ (1 / 4 : ℝ) * r ^ (1 / 2 : ℝ)) := by
      rw [Real.mul_rpow (div_nonneg hu hlower.le) (sq_nonneg r), hp]
    _ = (2 * (upper / lower) ^ (1 / 4 : ℝ)) * (r ^ (-1 : ℝ) * r ^ (1 / 2 : ℝ)) := by
      rw [Real.rpow_neg_one]
      ring
    _ = _ := by rw [hinv]

end NlsGge.Weights

namespace NlsGge.Weights

lemma weight_at_zero (c : ℕ → ℝ) : weight c 0 = c 0 := by
  have hs : HasSum (weightTerm c 0) (weightTerm c 0 0) :=
    hasSum_single 0 (fun j hj => by simp [weightTerm, hj])
  simpa only [weight, weightTerm_zero_index] using hs.tsum_eq

lemma weight_deriv_at_zero (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) : deriv (weight c) 0 = 0 := by
  rw [(weight_hasDerivAt lower upper c hlower hbound hupper 0).deriv]
  have hz (j : ℕ) : weightTermDerivative c 0 j = 0 := by
    by_cases hj : j = 0
    · simp [weightTermDerivative, hj]
    · have he : 2 * j - 1 ≠ 0 := by omega
      simp [weightTermDerivative, he]
  simp only [hz, tsum_zero]

end NlsGge.Weights

namespace NlsGge.Weights

lemma one_two_logDerivative_constant :
    (2 : ℝ) * (2 / 1 : ℝ) ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (5 / 4 : ℝ) := by
  calc
    (2 : ℝ) * (2 / 1 : ℝ) ^ (1 / 4 : ℝ) =
      (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (1 / 4 : ℝ) := by rw [div_one, Real.rpow_one]
    _ = (2 : ℝ) ^ ((1 : ℝ) + 1 / 4) := (Real.rpow_add (by norm_num) 1 (1 / 4)).symm
    _ = (2 : ℝ) ^ (5 / 4 : ℝ) := by congr 1; norm_num

lemma partialWeight_logDerivative_le_one_two (c : ℕ → ℝ)
    (hbound : ∀ j : ℕ, 1 ≤ c j) (hupper : ∀ j : ℕ, c j ≤ 2)
    (m : ℕ) (r : ℝ) (hr : 0 < r) :
    deriv (partialWeight c m) r / partialWeight c m r ≤
      (2 : ℝ) ^ (5 / 4 : ℝ) * r ^ (-1 / 2 : ℝ) := by
  simpa only [one_two_logDerivative_constant] using
    partialWeight_logDerivative_le 1 2 c (by norm_num) hbound hupper m r hr

lemma weight_logDerivative_le_one_two (c : ℕ → ℝ)
    (hbound : ∀ j : ℕ, 1 ≤ c j) (hupper : ∀ j : ℕ, c j ≤ 2)
    (r : ℝ) (hr : 0 < r) :
    deriv (weight c) r / weight c r ≤
      (2 : ℝ) ^ (5 / 4 : ℝ) * r ^ (-1 / 2 : ℝ) := by
  simpa only [one_two_logDerivative_constant] using
    weight_logDerivative_le 1 2 c (by norm_num) hbound hupper r hr

end NlsGge.Weights

namespace NlsGge.Weights

lemma weight_uniform_logDerivative_constant (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) :
    ∃ C : ℝ, C = 2 * (upper / lower) ^ (1 / 4 : ℝ) ∧ 0 < C ∧
      ∀ c : ℕ → ℝ,
        (∀ j : ℕ, lower ≤ c j) → (∀ j : ℕ, c j ≤ upper) →
        ∀ r : ℝ, 0 < r →
          (0 ≤ deriv (weight c) r / weight c r ∧
            deriv (weight c) r / weight c r ≤ C * r ^ (-1 / 2 : ℝ)) ∧
          ∀ m : ℕ,
            0 ≤ deriv (partialWeight c m) r / partialWeight c m r ∧
            deriv (partialWeight c m) r / partialWeight c m r ≤ C * r ^ (-1 / 2 : ℝ) := by
  have hratio : 0 < upper / lower := div_pos (hlower.trans_le hlower_upper) hlower
  refine ⟨2 * (upper / lower) ^ (1 / 4 : ℝ), rfl,
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hratio _), ?_⟩
  intro c hbound hupper r hr
  constructor
  · exact ⟨weight_logDerivative_nonneg lower upper c hlower hbound hupper r hr,
      weight_logDerivative_le lower upper c hlower hbound hupper r hr⟩
  · intro m
    exact ⟨partialWeight_logDerivative_nonneg lower c hlower hbound m r hr,
      partialWeight_logDerivative_le lower upper c hlower hbound hupper m r hr⟩

end NlsGge.Weights
