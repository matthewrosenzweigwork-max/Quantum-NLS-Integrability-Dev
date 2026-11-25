import NlsGge.Weights.Basic

/-! Summability is proved before the totalized real sum is used. This file does
not yet assert complex analyticity of the symbol. -/
set_option autoImplicit false

noncomputable section

namespace NlsGge.Weights

lemma expSeries_hasSum (t : ℝ) :
    HasSum (fun j : ℕ => t ^ j / (Nat.factorial j : ℝ)) (Real.exp t) := by
  simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp t

lemma expSeries_term_le (t : ℝ) (ht : 0 ≤ t) (j : ℕ) :
    t ^ j / (Nat.factorial j : ℝ) ≤ Real.exp t := by
  rw [← (expSeries_hasSum t).tsum_eq]
  exact (expSeries_hasSum t).summable.le_tsum j (fun k hk => by positivity)

lemma weightTerm_eq_fourth_power (c : ℕ → ℝ) (r : ℝ) (j : ℕ) :
    weightTerm c r j = c j *
      (Real.sqrt |r| ^ j / (Nat.factorial j : ℝ)) ^ 4 := by
  have hs : (Real.sqrt |r|) ^ 4 = r ^ 2 := by
    calc
      (Real.sqrt |r|) ^ 4 = ((Real.sqrt |r|) ^ 2) ^ 2 := by ring
      _ = |r| ^ 2 := by rw [Real.sq_sqrt (abs_nonneg r)]
      _ = r ^ 2 := sq_abs r
  unfold weightTerm coefficient
  have hp : r ^ (2 * j) = (Real.sqrt |r| ^ j) ^ 4 := by
    calc
      r ^ (2 * j) = (r ^ 2) ^ j := pow_mul r 2 j
      _ = ((Real.sqrt |r|) ^ 4) ^ j := by rw [hs]
      _ = (Real.sqrt |r| ^ j) ^ 4 := by simp only [← pow_mul, Nat.mul_comm]
  rw [hp, div_pow]
  ring

lemma fourth_power_le_exp_majorant (t : ℝ) (ht : 0 ≤ t) (j : ℕ) :
    (t ^ j / (Nat.factorial j : ℝ)) ^ 4 ≤
      Real.exp t ^ 3 * (t ^ j / (Nat.factorial j : ℝ)) := by
  have hx : 0 ≤ t ^ j / (Nat.factorial j : ℝ) := by positivity
  calc
    (t ^ j / (Nat.factorial j : ℝ)) ^ 4 =
      (t ^ j / (Nat.factorial j : ℝ)) ^ 3 *
      (t ^ j / (Nat.factorial j : ℝ)) := by ring
    _ ≤ Real.exp t ^ 3 * (t ^ j / (Nat.factorial j : ℝ)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx (expSeries_term_le t ht j) 3) hx

lemma weightTerm_le_exp_majorant (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) (j : ℕ) :
    weightTerm c r j ≤ (upper * Real.exp (Real.sqrt |r|) ^ 3) *
      (Real.sqrt |r| ^ j / (Nat.factorial j : ℝ)) := by
  have hu : 0 ≤ upper := (hlower.trans_le ((hbound 0).trans (hupper 0))).le
  rw [weightTerm_eq_fourth_power]
  calc
    c j * (Real.sqrt |r| ^ j / (Nat.factorial j : ℝ)) ^ 4 ≤
      upper * (Real.sqrt |r| ^ j / (Nat.factorial j : ℝ)) ^ 4 :=
        mul_le_mul_of_nonneg_right (hupper j) (by positivity)
    _ ≤ upper * (Real.exp (Real.sqrt |r|) ^ 3 *
      (Real.sqrt |r| ^ j / (Nat.factorial j : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (fourth_power_le_exp_majorant _ (Real.sqrt_nonneg _) j) hu
    _ = _ := by ring

lemma weightTerm_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    Summable (weightTerm c r) := by
  exact ((expSeries_hasSum (Real.sqrt |r|)).summable.mul_left
    (upper * Real.exp (Real.sqrt |r|) ^ 3)).of_nonneg_of_le
      (weightTerm_nonneg lower c hlower hbound r)
      (weightTerm_le_exp_majorant lower upper c hlower hbound hupper r)

/-- Use only with a separately proved summability result. -/
def weight (c : ℕ → ℝ) (r : ℝ) : ℝ := ∑' j, weightTerm c r j

lemma weight_upper (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    weight c r ≤ upper * Real.exp (4 * Real.sqrt |r|) := by
  have hm := (expSeries_hasSum (Real.sqrt |r|)).summable.mul_left
    (upper * Real.exp (Real.sqrt |r|) ^ 3)
  calc
    weight c r ≤ ∑' j : ℕ, (upper * Real.exp (Real.sqrt |r|) ^ 3) *
      (Real.sqrt |r| ^ j / (Nat.factorial j : ℝ)) :=
        (weightTerm_summable lower upper c hlower hbound hupper r).tsum_le_tsum
          (weightTerm_le_exp_majorant lower upper c hlower hbound hupper r) hm
    _ = (upper * Real.exp (Real.sqrt |r|) ^ 3) * Real.exp (Real.sqrt |r|) := by
      rw [(expSeries_hasSum (Real.sqrt |r|)).summable.tsum_mul_left,
        (expSeries_hasSum (Real.sqrt |r|)).tsum_eq]
    _ = upper * Real.exp (4 * Real.sqrt |r|) := by
      rw [show Real.exp (4 * Real.sqrt |r|) = Real.exp (Real.sqrt |r|) ^ 4 from
        Real.exp_nat_mul (Real.sqrt |r|) 4]
      ring

lemma weight_lower (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) : lower ≤ weight c r := by
  calc
    lower ≤ weightTerm c r 0 := by simpa using hbound 0
    _ ≤ weight c r := (weightTerm_summable lower upper c hlower hbound hupper r).le_tsum 0
      (fun j hj => weightTerm_nonneg lower c hlower hbound r j)

lemma weight_pos (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) : 0 < weight c r :=
  hlower.trans_le (weight_lower lower upper c hlower hbound hupper r)

@[simp] lemma weight_even (c : ℕ → ℝ) (r : ℝ) : weight c (-r) = weight c r := by
  simp [weight]

lemma partialWeight_le_weight (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (m : ℕ) (r : ℝ) :
    partialWeight c m r ≤ weight c r := by
  exact (weightTerm_summable lower upper c hlower hbound hupper r).sum_le_tsum
    (Finset.range (m + 1)) (fun j hj => weightTerm_nonneg lower c hlower hbound r j)

lemma partialWeight_upper (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (m : ℕ) (r : ℝ) :
    partialWeight c m r ≤ upper * Real.exp (4 * Real.sqrt |r|) :=
  (partialWeight_le_weight lower upper c hlower hbound hupper m r).trans
    (weight_upper lower upper c hlower hbound hupper r)


/-- Normalized on indices 0 through m only; terms outside that range need not vanish. -/
def partialProbabilityTerm (c : ℕ → ℝ) (m : ℕ) (r : ℝ) (j : ℕ) : ℝ :=
  weightTerm c r j / partialWeight c m r

lemma partialProbabilityTerm_nonneg (lower : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (m : ℕ) (r : ℝ) (j : ℕ) : 0 ≤ partialProbabilityTerm c m r j := by
  exact div_nonneg (weightTerm_nonneg lower c hlower hbound r j)
    (partialWeight_pos lower c hlower hbound m r).le

lemma partialProbabilityTerm_sum (lower : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (m : ℕ) (r : ℝ) :
    ∑ j ∈ Finset.range (m + 1), partialProbabilityTerm c m r j = 1 := by
  simp only [partialProbabilityTerm, ← Finset.sum_div]
  change partialWeight c m r / partialWeight c m r = 1
  exact div_self (partialWeight_pos lower c hlower hbound m r).ne'

lemma partialProbabilityTerm_fourthMoment (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (m : ℕ) (r : ℝ) :
    ∑ j ∈ Finset.range (m + 1), (j : ℝ) ^ 4 * partialProbabilityTerm c m r j ≤
      (upper / lower) * r ^ 2 := by
  simp only [partialProbabilityTerm, ← mul_div_assoc, ← Finset.sum_div]
  change partialFourthMoment c m r / partialWeight c m r ≤ (upper / lower) * r ^ 2
  apply (div_le_iff₀ (partialWeight_pos lower c hlower hbound m r)).2
  exact partialFourthMoment_le lower upper c hlower hbound hupper m r

lemma fourthMoment_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    Summable (fun j : ℕ => (j : ℝ) ^ 4 * weightTerm c r j) := by
  apply (summable_nat_add_iff 1).1
  have hs := (weightTerm_summable lower upper (fun j => c (j + 1))
    hlower (fun j => hbound (j + 1)) (fun j => hupper (j + 1)) r).mul_left (r ^ 2)
  convert hs using 1
  ext j
  exact fourthMomentTerm_succ c r j

lemma fourthMoment_le (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    (∑' j : ℕ, (j : ℝ) ^ 4 * weightTerm c r j) ≤
      (upper / lower) * r ^ 2 * weight c r := by
  have hs := fourthMoment_summable lower upper c hlower hbound hupper r
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_pow (by omega : 4 ≠ 0), zero_mul, zero_add]
  have hm := (weightTerm_summable lower upper c hlower hbound hupper r).mul_left
    ((upper / lower) * r ^ 2)
  calc
    ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ 4 * weightTerm c r (j + 1) ≤
      ∑' j : ℕ, (upper / lower) * r ^ 2 * weightTerm c r j := by
        exact ((summable_nat_add_iff 1).2 hs).tsum_le_tsum
          (fourthMomentTerm_succ_le lower upper c hlower hbound hupper r) hm
    _ = _ := by
      rw [(weightTerm_summable lower upper c hlower hbound hupper r).tsum_mul_left]
      rfl

lemma partialProbabilityTerm_firstMoment_le (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (m : ℕ) (r : ℝ) :
    ∑ j ∈ Finset.range (m + 1), partialProbabilityTerm c m r j * (j : ℝ) ≤
      ((upper / lower) * r ^ 2) ^ (1 / 4 : ℝ) := by
  have hh := Real.inner_le_weight_mul_Lp_of_nonneg (Finset.range (m + 1))
    (p := 4) (by norm_num) (partialProbabilityTerm c m r) (fun j => (j : ℝ))
    (partialProbabilityTerm_nonneg lower c hlower hbound m r)
    (fun j => Nat.cast_nonneg j)
  simp only [partialProbabilityTerm_sum lower c hlower hbound m r,
    Real.one_rpow, one_mul] at hh
  have hpow (j : ℕ) : (j : ℝ) ^ (4 : ℝ) = (j : ℝ) ^ (4 : ℕ) :=
    Real.rpow_natCast (j : ℝ) 4
  have hmoment : ∑ j ∈ Finset.range (m + 1),
      partialProbabilityTerm c m r j * (j : ℝ) ^ (4 : ℝ) ≤
      (upper / lower) * r ^ 2 := by
    simpa only [hpow, mul_comm]
      using partialProbabilityTerm_fourthMoment lower upper c hlower hbound hupper m r
  have hnonneg : 0 ≤ ∑ j ∈ Finset.range (m + 1),
      partialProbabilityTerm c m r j * (j : ℝ) ^ (4 : ℝ) := by
    exact Finset.sum_nonneg (fun j hj => by
      have hp := partialProbabilityTerm_nonneg lower c hlower hbound m r j
      positivity)
  simpa only [one_div] using
    hh.trans (Real.rpow_le_rpow (z := (4 : ℝ)⁻¹) hnonneg hmoment (by norm_num))


end NlsGge.Weights
