import NlsGge.Bootstrap

/-! Concrete scalar leaves for NEW-F01. Bounds precede the coefficient sequence.
The truncation order is inclusive and the zero term is retained. -/
set_option autoImplicit false

noncomputable section

namespace NlsGge.Weights

lemma coefficient_pos (lower : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (j : ℕ) :
    0 < coefficient c j := by
  unfold coefficient
  exact div_pos (hlower.trans_le (hbound j)) (pow_pos (by positivity) 4)

@[simp] lemma coefficient_zero (c : ℕ → ℝ) : coefficient c 0 = c 0 := by
  simp [coefficient]

lemma weightTerm_nonneg (lower : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (r : ℝ) (j : ℕ) :
    0 ≤ weightTerm c r j := by
  unfold weightTerm
  exact mul_nonneg (le_of_lt (coefficient_pos lower c hlower hbound j))
    (by rw [pow_mul]; positivity)

@[simp] lemma weightTerm_zero_index (c : ℕ → ℝ) (r : ℝ) :
    weightTerm c r 0 = c 0 := by
  simp [weightTerm]

@[simp] lemma weightTerm_even (c : ℕ → ℝ) (r : ℝ) (j : ℕ) :
    weightTerm c (-r) j = weightTerm c r j := by
  simp [weightTerm, pow_mul]

/-- The source partial symbol W_m; m is the final included index. -/
def partialWeight (c : ℕ → ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), weightTerm c r j

@[simp] lemma partialWeight_order_zero (c : ℕ → ℝ) (r : ℝ) :
    partialWeight c 0 r = c 0 := by
  simp [partialWeight]

@[simp] lemma partialWeight_at_zero (c : ℕ → ℝ) (m : ℕ) :
    partialWeight c m 0 = c 0 := by
  unfold partialWeight
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hjzero
    simp [weightTerm, hjzero]
  · simp

lemma partialWeight_lower (lower : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (m : ℕ) (r : ℝ) :
    lower ≤ partialWeight c m r := by
  calc
    lower ≤ weightTerm c r 0 := by simpa using hbound 0
    _ ≤ partialWeight c m r := by
      apply Finset.single_le_sum
      · intro j hj
        exact weightTerm_nonneg lower c hlower hbound r j
      · simp

lemma partialWeight_pos (lower : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (m : ℕ) (r : ℝ) :
    0 < partialWeight c m r :=
  hlower.trans_le (partialWeight_lower lower c hlower hbound m r)

@[simp] lemma partialWeight_even (c : ℕ → ℝ) (m : ℕ) (r : ℝ) :
    partialWeight c m (-r) = partialWeight c m r := by
  simp [partialWeight]

lemma partialWeight_mono_order (lower : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (m n : ℕ) (hmn : m ≤ n) (r : ℝ) :
    partialWeight c m r ≤ partialWeight c n r := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.add_le_add_right hmn 1)
  · intro j hj hjnot
    exact weightTerm_nonneg lower c hlower hbound r j

/-- Cancellation of the shifted factorial in the fourth index moment. -/
lemma fourthMomentTerm_succ (c : ℕ → ℝ) (r : ℝ) (j : ℕ) :
    ((j + 1 : ℕ) : ℝ) ^ 4 * weightTerm c r (j + 1) =
      r ^ 2 * (c (j + 1) / (Nat.factorial j : ℝ) ^ 4 * r ^ (2 * j)) := by
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [weightTerm, coefficient, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, mul_pow]
  rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
  field_simp
  <;> ring

lemma coefficient_shift_le (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (j : ℕ) :
    c (j + 1) ≤ (upper / lower) * c j := by
  have hu : 0 ≤ upper := (hlower.trans_le ((hbound 0).trans (hupper 0))).le
  calc
    c (j + 1) ≤ upper := hupper _
    _ = (upper / lower) * lower := (div_mul_cancel₀ upper hlower.ne').symm
    _ ≤ (upper / lower) * c j :=
      mul_le_mul_of_nonneg_left (hbound j) (div_nonneg hu hlower.le)

lemma fourthMomentTerm_succ_le (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) (j : ℕ) :
    ((j + 1 : ℕ) : ℝ) ^ 4 * weightTerm c r (j + 1) ≤
      (upper / lower) * r ^ 2 * weightTerm c r j := by
  rw [fourthMomentTerm_succ]
  have hp : 0 ≤ r ^ (2 * j) := by rw [pow_mul]; positivity
  calc
    r ^ 2 * (c (j + 1) / (Nat.factorial j : ℝ) ^ 4 * r ^ (2 * j)) ≤
      r ^ 2 * (((upper / lower) * c j) / (Nat.factorial j : ℝ) ^ 4 *
      r ^ (2 * j)) := by
        gcongr
        exact coefficient_shift_le lower upper c hlower hbound hupper j
    _ = _ := by unfold weightTerm coefficient; ring

/-- The unnormalized fourth moment of the inclusive finite symbol. -/
def partialFourthMoment (c : ℕ → ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (j : ℝ) ^ 4 * weightTerm c r j

@[simp] lemma partialFourthMoment_order_zero (c : ℕ → ℝ) (r : ℝ) :
    partialFourthMoment c 0 r = 0 := by
  simp [partialFourthMoment]

lemma partialFourthMoment_le (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (m : ℕ) (r : ℝ) :
    partialFourthMoment c m r ≤
      (upper / lower) * r ^ 2 * partialWeight c m r := by
  have hu : 0 ≤ upper := (hlower.trans_le ((hbound 0).trans (hupper 0))).le
  have hfactor : 0 ≤ (upper / lower) * r ^ 2 := by positivity
  unfold partialFourthMoment
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_pow (by omega : 4 ≠ 0), zero_mul, add_zero]
  calc
    ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) ^ 4 * weightTerm c r (j + 1) ≤
      ∑ j ∈ Finset.range m, (upper / lower) * r ^ 2 * weightTerm c r j := by
        apply Finset.sum_le_sum
        intro j hj
        exact fourthMomentTerm_succ_le lower upper c hlower hbound hupper r j
    _ = (upper / lower) * r ^ 2 * ∑ j ∈ Finset.range m, weightTerm c r j := by
      rw [Finset.mul_sum]
    _ ≤ (upper / lower) * r ^ 2 * partialWeight c m r := by
      apply mul_le_mul_of_nonneg_left _ hfactor
      unfold partialWeight
      rw [Finset.sum_range_succ]
      exact le_add_of_nonneg_right (weightTerm_nonneg lower c hlower hbound r m)

end NlsGge.Weights
