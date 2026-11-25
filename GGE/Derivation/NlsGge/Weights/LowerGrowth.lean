import NlsGge.Weights.Entire
set_option autoImplicit false
noncomputable section
namespace NlsGge.Weights

lemma weightTerm_lower_geometric (lower : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (r : ℝ) (hr : 0 ≤ r) (j : ℕ) (hj : 4 * (j : ℝ) ^ 2 ≤ r) :
    lower * (16 : ℝ) ^ j ≤ weightTerm c r j := by
  have hfact : (Nat.factorial j : ℝ) ≤ (j : ℝ) ^ j := by
    exact_mod_cast Nat.factorial_le_pow j
  have hfact4 : (Nat.factorial j : ℝ) ^ 4 ≤ ((j : ℝ) ^ j) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hfact 4
  have hrad : (16 : ℝ) * (j : ℝ) ^ 4 ≤ r ^ 2 := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * (j : ℝ) ^ 2) hj 2
    nlinarith [hs]
  have hgeom : (16 : ℝ) ^ j * (Nat.factorial j : ℝ) ^ 4 ≤ r ^ (2 * j) := by
    calc
      (16 : ℝ) ^ j * (Nat.factorial j : ℝ) ^ 4 ≤
        (16 : ℝ) ^ j * ((j : ℝ) ^ j) ^ 4 :=
          mul_le_mul_of_nonneg_left hfact4 (by positivity)
      _ = ((16 : ℝ) * (j : ℝ) ^ 4) ^ j := by
        simp only [mul_pow, ← pow_mul, Nat.mul_comm]
      _ ≤ (r ^ 2) ^ j := pow_le_pow_left₀ (by positivity) hrad j
      _ = r ^ (2 * j) := (pow_mul r 2 j).symm
  have hnum : lower * ((16 : ℝ) ^ j * (Nat.factorial j : ℝ) ^ 4) ≤
      c j * r ^ (2 * j) :=
    mul_le_mul (hbound j) hgeom (by positivity) (hlower.trans_le (hbound j)).le
  rw [weightTerm, coefficient, div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < (Nat.factorial j : ℝ) ^ 4)).2
  nlinarith [hnum]

def lowerGrowthIndex (r : ℝ) : ℕ := Nat.floor (Real.sqrt r / 2)

lemma lowerGrowthIndex_bounds (r : ℝ) (hr : 16 ≤ r) :
    Real.sqrt r / 4 ≤ (lowerGrowthIndex r : ℝ) ∧
      (lowerGrowthIndex r : ℝ) ≤ Real.sqrt r / 2 := by
  have hs : 4 ≤ Real.sqrt r := Real.le_sqrt_of_sq_le (by norm_num; exact hr)
  have hlo := Nat.lt_floor_add_one (Real.sqrt r / 2)
  have hhi := Nat.floor_le (by positivity : 0 ≤ Real.sqrt r / 2)
  unfold lowerGrowthIndex
  constructor
  · linarith
  · exact hhi

lemma lowerGrowthIndex_geom (r : ℝ) (hr : 16 ≤ r) :
    4 * (lowerGrowthIndex r : ℝ) ^ 2 ≤ r := by
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (lowerGrowthIndex r))
    (lowerGrowthIndex_bounds r hr).2 2
  have hsqrt := Real.sq_sqrt (by linarith : 0 ≤ r)
  nlinarith [hsq, hsqrt]

lemma weight_lower_growth_explicit (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) (hr : 16 ≤ r) :
    lower * Real.exp ((Real.log 16 / 4) * Real.sqrt r) ≤ weight c r := by
  have hlog : 0 ≤ Real.log (16 : ℝ) := (Real.log_pos (by norm_num : (1 : ℝ) < 16)).le
  have hpow : Real.exp ((lowerGrowthIndex r : ℝ) * Real.log 16) = (16 : ℝ) ^ lowerGrowthIndex r := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
  calc
    lower * Real.exp ((Real.log 16 / 4) * Real.sqrt r) ≤
      lower * Real.exp ((lowerGrowthIndex r : ℝ) * Real.log 16) := by
        apply mul_le_mul_of_nonneg_left _ hlower.le
        apply Real.exp_le_exp.mpr
        nlinarith [(lowerGrowthIndex_bounds r hr).1]
    _ = lower * (16 : ℝ) ^ lowerGrowthIndex r := by rw [hpow]
    _ ≤ weightTerm c r (lowerGrowthIndex r) :=
      weightTerm_lower_geometric lower c hlower hbound r (by linarith)
        (lowerGrowthIndex r) (lowerGrowthIndex_geom r hr)
    _ ≤ weight c r :=
      (weightTerm_summable lower upper c hlower hbound hupper r).le_tsum
        (lowerGrowthIndex r) (fun j hj => weightTerm_nonneg lower c hlower hbound r j)

end NlsGge.Weights

namespace NlsGge.Weights

lemma weight_uniform_lower_growth (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) :
    ∃ growth : ℝ, 0 < growth ∧
      ∀ c : ℕ → ℝ,
        (∀ j : ℕ, lower ≤ c j) → (∀ j : ℕ, c j ≤ upper) →
        ∀ r : ℝ, 16 ≤ r → growth * Real.exp (growth * Real.sqrt r) ≤ weight c r := by
  have hk : 0 < Real.log (16 : ℝ) / 4 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  refine ⟨min lower (Real.log 16 / 4), lt_min_iff.mpr ⟨hlower, hk⟩, ?_⟩
  intro c hbound hupper r hr
  have he : Real.exp (min lower (Real.log 16 / 4) * Real.sqrt r) ≤
      Real.exp ((Real.log 16 / 4) * Real.sqrt r) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg r))
  calc
    min lower (Real.log 16 / 4) * Real.exp (min lower (Real.log 16 / 4) * Real.sqrt r) ≤
      lower * Real.exp ((Real.log 16 / 4) * Real.sqrt r) :=
        mul_le_mul (min_le_left _ _) he (Real.exp_nonneg _) hlower.le
    _ ≤ weight c r := weight_lower_growth_explicit lower upper c hlower hbound hupper r hr

end NlsGge.Weights
