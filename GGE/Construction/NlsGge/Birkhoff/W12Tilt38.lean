import NlsGge.Birkhoff.W05ChargeSeries38
import NlsGge.Birkhoff.S04Moments38c

/-! # W12 (`D:prop:tilt`), part 1 (Birkhoff-free): the reserved weight `B`, the tilted weight
`W̃ = W - δ B`, the rates `b_n`, the determinant `D_δ`

Source: `paper/v2.tex` l.1320-1325 (`F:eq:B`) and l.1836-1863 (`D:prop:tilt`).

Nothing in this file mentions `BirkhoffInput38`.

* `bCoef38 c j = c_{j+1}/(j+1)^4`: the coefficient numerators of `B`, so that
  `coefficient (bCoef38 c) j = β_{j+1}` and `B(r) = weight (bCoef38 c) r = ∑_j β_{j+1} r^{2j}`
  (W12.01: `B(0) = β_1` and `B(r) = (W(r) - β_0)/r²` for `r ≠ 0`).
* `tiltCoef38 c δ = c - δ * bCoef38 c`: the numerators of `W̃ = W - δ B`
  (`weight_tiltCoef38`: `W̃ = W - δ B` pointwise).
* W12.03: for `0 < δ` and `δ * upper < lower` the numerators `c̃_j` lie in `[lower - δ upper, upper]`
  (`tiltBounded38`).  This contains v2's ranges `0 < δ < c_minus / (4 c_plus)` and (for `1 ≤ c_j ≤ 2`)
  `0 < δ < 1/4`.
* W12.04 (determinant): `b_n = B(2πn)`, `a_n = W(2πn)`, `ã_n = a_n - δ b_n`,
  `D_δ = ∏_n (1 - δ b_n / a_n) > 0` (`HasProd`, so the product is the unconditional one over `ℤ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Weights Filter Topology
open scoped ENNReal Real

/-! ## W12.01 and W12.03: the algebra of `B` and `W̃ = W - δ B` -/

section Algebra

variable {lower upper : ℝ}

/-- Coefficient numerators of the reserved weight `B(r) = (W(r) - β_0)/r² = ∑_j β_{j+1} r^{2j}`
(v2 `F:eq:B`): `β_{j+1} = c_{j+1}/((j+1)!)^4 = (c_{j+1}/(j+1)^4)/(j!)^4`. -/
def bCoef38 (c : ℕ → ℝ) (j : ℕ) : ℝ := c (j + 1) / ((j + 1 : ℕ) : ℝ) ^ 4

theorem coefficient_bCoef38 (c : ℕ → ℝ) (j : ℕ) :
    NlsGge.coefficient (bCoef38 c) j = NlsGge.coefficient c (j + 1) := by
  unfold NlsGge.coefficient bCoef38
  rw [Nat.factorial_succ]
  push_cast
  have h1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((Nat.factorial j : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem weightTerm_succ38 (c : ℕ → ℝ) (r : ℝ) (j : ℕ) :
    NlsGge.weightTerm c r (j + 1) = r ^ 2 * NlsGge.weightTerm (bCoef38 c) r j := by
  unfold NlsGge.weightTerm
  rw [coefficient_bCoef38, show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
  ring

theorem coefficient_nonneg38' (c : BoundedCoefficients lower upper) (j : ℕ) :
    0 ≤ NlsGge.coefficient c.val j :=
  div_nonneg ((coef_lower38 c).le.trans (coef_bound38 c j)) (by positivity)

theorem coefficient_bCoef_le38 (c : BoundedCoefficients lower upper) (j : ℕ) :
    NlsGge.coefficient (bCoef38 c.val) j ≤ (upper / lower) * NlsGge.coefficient c.val j := by
  have hl := coef_lower38 c
  rw [coefficient_bCoef38]
  unfold NlsGge.coefficient
  have hf : (0 : ℝ) < (Nat.factorial j : ℝ) ^ 4 := by positivity
  have hf1 : (Nat.factorial j : ℝ) ≤ (Nat.factorial (j + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ j)
  have hf14 : (Nat.factorial j : ℝ) ^ 4 ≤ (Nat.factorial (j + 1) : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hf1 4
  have hu := coef_upper38 c (j + 1)
  have hb := coef_bound38 c j
  have hup : 0 ≤ upper := by linarith [coef_bound38 c 0, coef_upper38 c 0]
  calc c.val (j + 1) / (Nat.factorial (j + 1) : ℝ) ^ 4
      ≤ upper / (Nat.factorial j : ℝ) ^ 4 := by
        calc c.val (j + 1) / (Nat.factorial (j + 1) : ℝ) ^ 4
            ≤ upper / (Nat.factorial (j + 1) : ℝ) ^ 4 :=
              div_le_div_of_nonneg_right hu (by positivity)
          _ ≤ upper / (Nat.factorial j : ℝ) ^ 4 :=
              div_le_div_of_nonneg_left hup hf hf14
    _ ≤ (upper / lower) * (c.val j / (Nat.factorial j : ℝ) ^ 4) := by
        rw [div_mul_div_comm, div_le_div_iff₀ hf (by positivity)]
        have : 0 ≤ upper * (Nat.factorial j : ℝ) ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hb this]

theorem coefficient_bCoef_nonneg38 (c : BoundedCoefficients lower upper) (j : ℕ) :
    0 ≤ NlsGge.coefficient (bCoef38 c.val) j := by
  rw [coefficient_bCoef38]; exact coefficient_nonneg38' c (j + 1)

theorem weightTerm_bCoef_nonneg38 (c : BoundedCoefficients lower upper) (r : ℝ) (j : ℕ) :
    0 ≤ NlsGge.weightTerm (bCoef38 c.val) r j :=
  mul_nonneg (coefficient_bCoef_nonneg38 c j) (by rw [pow_mul]; positivity)

theorem weightTerm_bCoef_le38 (c : BoundedCoefficients lower upper) (r : ℝ) (j : ℕ) :
    NlsGge.weightTerm (bCoef38 c.val) r j ≤ (upper / lower) * NlsGge.weightTerm c.val r j := by
  unfold NlsGge.weightTerm
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (coefficient_bCoef_le38 c j) (by rw [pow_mul]; positivity)

theorem summable_weightTerm_bCoef38 (c : BoundedCoefficients lower upper) (r : ℝ) :
    Summable (NlsGge.weightTerm (bCoef38 c.val) r) := by
  have hs := (weightTerm_summable lower upper c.val (coef_lower38 c) (coef_bound38 c)
    (coef_upper38 c) r).mul_left (upper / lower)
  exact hs.of_nonneg_of_le (weightTerm_bCoef_nonneg38 c r) (weightTerm_bCoef_le38 c r)

theorem weight_bCoef_nonneg38 (c : BoundedCoefficients lower upper) (r : ℝ) :
    0 ≤ weight (bCoef38 c.val) r :=
  tsum_nonneg (weightTerm_bCoef_nonneg38 c r)

/-- `B ≤ (c_+/c_-) W` (the ratio `β_{j+1}/β_j ≤ (c_+/c_-)/(j+1)^4 ≤ c_+/c_-`). -/
theorem weight_bCoef_le38 (c : BoundedCoefficients lower upper) (r : ℝ) :
    weight (bCoef38 c.val) r ≤ (upper / lower) * weight c.val r := by
  have hs := (weightTerm_summable lower upper c.val (coef_lower38 c) (coef_bound38 c)
    (coef_upper38 c) r)
  unfold weight
  rw [← tsum_mul_left]
  exact (summable_weightTerm_bCoef38 c r).tsum_le_tsum (weightTerm_bCoef_le38 c r) (hs.mul_left _)

/-- **W12.01, the shifted series.** `W(r) = β_0 + r² B(r)` for every real `r`. -/
theorem weight_eq_bWeight38 (c : BoundedCoefficients lower upper) (r : ℝ) :
    weight c.val r = NlsGge.coefficient c.val 0 + r ^ 2 * weight (bCoef38 c.val) r := by
  have hs := (weightTerm_summable lower upper c.val (coef_lower38 c) (coef_bound38 c)
    (coef_upper38 c) r)
  unfold weight
  rw [hs.tsum_eq_zero_add]
  have h0 : NlsGge.weightTerm c.val r 0 = NlsGge.coefficient c.val 0 := by
    simp [NlsGge.weightTerm]
  rw [h0]
  congr 1
  rw [← tsum_mul_left]
  exact tsum_congr (fun j => weightTerm_succ38 c.val r j)

/-- **W12.01, the value at zero.** `B(0) = β_1`. -/
theorem weight_bCoef_zero38 (c : BoundedCoefficients lower upper) :
    weight (bCoef38 c.val) 0 = NlsGge.coefficient c.val 1 := by
  have hs := summable_weightTerm_bCoef38 c 0
  unfold weight
  rw [hs.tsum_eq_zero_add]
  have h0 : NlsGge.weightTerm (bCoef38 c.val) 0 0 = NlsGge.coefficient (bCoef38 c.val) 0 := by
    simp [NlsGge.weightTerm]
  have h1 : ∑' j : ℕ, NlsGge.weightTerm (bCoef38 c.val) 0 (j + 1) = 0 := by
    have : ∀ j : ℕ, NlsGge.weightTerm (bCoef38 c.val) 0 (j + 1) = 0 := fun j => by
      simp [NlsGge.weightTerm]
    simp only [this, tsum_zero]
  rw [h0, h1, add_zero, coefficient_bCoef38]

/-- Coefficient numerators of `W̃ = W - δ B`: `c̃_j = c_j - δ c_{j+1}/(j+1)^4`, i.e.
`β̃_j = β_j - δ β_{j+1}`. -/
def tiltCoef38 (c : ℕ → ℝ) (δ : ℝ) (j : ℕ) : ℝ := c j - δ * bCoef38 c j

theorem coefficient_tiltCoef38 (c : ℕ → ℝ) (δ : ℝ) (j : ℕ) :
    NlsGge.coefficient (tiltCoef38 c δ) j =
      NlsGge.coefficient c j - δ * NlsGge.coefficient (bCoef38 c) j := by
  unfold NlsGge.coefficient tiltCoef38
  ring

/-- **W12.03 (positivity of every shifted coefficient).** For `0 < δ` with `δ c_+ < c_-`, the
numerators `c̃_j = c_j - δ c_{j+1}/(j+1)^4` of `W - δ B` lie in `[c_- - δ c_+, c_+]`. -/
theorem tiltCoef38_bounds (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) :
    AdmittedCoefficients (lower - δ * upper) upper (tiltCoef38 c.val δ) := by
  have hl := coef_lower38 c
  have hlu : lower ≤ upper := c.property.2.1
  refine ⟨by linarith, by nlinarith, fun j => ⟨?_, ?_⟩⟩
  · unfold tiltCoef38 bCoef38
    have h1 : c.val (j + 1) / ((j + 1 : ℕ) : ℝ) ^ 4 ≤ upper := by
      have hp : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast Nat.succ_pos j)
      calc c.val (j + 1) / ((j + 1 : ℕ) : ℝ) ^ 4 ≤ c.val (j + 1) :=
            div_le_self (hl.le.trans (coef_bound38 c _)) hp
        _ ≤ upper := coef_upper38 c _
    have := coef_bound38 c j
    nlinarith
  · unfold tiltCoef38 bCoef38
    have h0 : 0 ≤ c.val (j + 1) / ((j + 1 : ℕ) : ℝ) ^ 4 :=
      div_nonneg (hl.le.trans (coef_bound38 c _)) (by positivity)
    have := coef_upper38 c j
    nlinarith

/-- The class of `W̃` (W12.03). -/
def tiltBounded38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) : BoundedCoefficients (lower - δ * upper) upper :=
  ⟨tiltCoef38 c.val δ, tiltCoef38_bounds c hδ0 hδ⟩

theorem tiltBounded38_val (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) : (tiltBounded38 c hδ0 hδ).val = tiltCoef38 c.val δ := rfl

/-- v2's range `0 < δ < c_minus / (4 c_plus)` is inside the range of `tiltBounded38`. -/
theorem delta_mul_upper_lt_of_lt_quarter38 (c : BoundedCoefficients lower upper) {δ : ℝ}
    (hδ : δ < lower / (4 * upper)) : δ * upper < lower := by
  have hl := coef_lower38 c
  have hup : 0 < upper := lt_of_lt_of_le hl c.property.2.1
  have h := (lt_div_iff₀ (by positivity : 0 < 4 * upper)).1 hδ
  linarith

/-- v2's range `0 < δ < 1/4` for `1 ≤ c_j ≤ 2`. -/
theorem delta_mul_upper_lt_of_lt_quarter_one_two38 {δ : ℝ} (hδ : δ < 1 / 4) :
    δ * 2 < 1 := by linarith

/-- **`W̃ = W - δ B` pointwise.** -/
theorem weight_tiltCoef38 (c : BoundedCoefficients lower upper) (δ r : ℝ) :
    weight (tiltCoef38 c.val δ) r = weight c.val r - δ * weight (bCoef38 c.val) r := by
  have h1 := (weightTerm_summable lower upper c.val (coef_lower38 c) (coef_bound38 c)
    (coef_upper38 c) r)
  have h2 := (summable_weightTerm_bCoef38 c r).mul_left δ
  unfold weight
  rw [← tsum_mul_left, ← h1.tsum_sub h2]
  refine tsum_congr (fun j => ?_)
  unfold NlsGge.weightTerm
  rw [coefficient_tiltCoef38]
  ring

/-- `B` is continuous (`B = (W - W̃)/δ` for an admissible `δ`). -/
theorem continuous_weight_bCoef38 (c : BoundedCoefficients lower upper) :
    Continuous (weight (bCoef38 c.val)) := by
  have hl := coef_lower38 c
  have hup : 0 < upper := lt_of_lt_of_le hl c.property.2.1
  set δ : ℝ := lower / (2 * upper) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδu : δ * upper < lower := by
    rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hW := weight_continuous38 hl (coef_bound38 c) (coef_upper38 c)
  have hT : Continuous (weight (tiltCoef38 c.val δ)) :=
    weight_continuous38 (tiltCoef38_bounds c hδ0 hδu).1
      (fun j => ((tiltCoef38_bounds c hδ0 hδu).2.2 j).1)
      (fun j => ((tiltCoef38_bounds c hδ0 hδu).2.2 j).2)
  have : weight (bCoef38 c.val) = fun r => (weight c.val r - weight (tiltCoef38 c.val δ) r) / δ := by
    funext r
    rw [weight_tiltCoef38]
    field_simp
    ring
  rw [this]
  exact (hW.sub hT).div_const _

/-- `a_n = W(2πn)`. -/
theorem fullWeightRate_eq_weight38 (c : ℕ → ℝ) (n : ℤ) :
    fullWeightRate c n = weight c (2 * Real.pi * n) := rfl

end Algebra

section Rates

variable {lower upper : ℝ}

/-- `b_n = B(2πn)` (v2: `b_n = B(2πn)`), with `B` the reserved weight of `F:eq:B`. -/
def bRate38 (c : ℕ → ℝ) (n : ℤ) : ℝ := fullWeightRate (bCoef38 c) n

theorem bRate38_nonneg (c : BoundedCoefficients lower upper) (n : ℤ) : 0 ≤ bRate38 c.val n :=
  weight_bCoef_nonneg38 c _

theorem bRate38_le38 (c : BoundedCoefficients lower upper) (n : ℤ) :
    bRate38 c.val n ≤ (upper / lower) * fullWeightRate c.val n :=
  weight_bCoef_le38 c _

/-- `b_n (2πn)² ≤ a_n` for every `n` (from `W = β_0 + r² B`). -/
theorem bRate38_mul_sq_le38 (c : BoundedCoefficients lower upper) (n : ℤ) :
    (2 * Real.pi * n) ^ 2 * bRate38 c.val n ≤ fullWeightRate c.val n := by
  have h := weight_eq_bWeight38 c (2 * Real.pi * n)
  have h0 := coefficient_nonneg38' c 0
  show _ ≤ weight c.val (2 * Real.pi * n)
  unfold bRate38 fullWeightRate
  linarith

/-- The tilted rate `ã_n = a_n - δ b_n` (`W̃(2πn)`). -/
theorem fullWeightRate_tilt38 (c : BoundedCoefficients lower upper) (δ : ℝ) (n : ℤ) :
    fullWeightRate (tiltCoef38 c.val δ) n = fullWeightRate c.val n - δ * bRate38 c.val n := by
  unfold fullWeightRate bRate38 fullWeightRate
  exact weight_tiltCoef38 c δ _

theorem fullWeightRate_pos38 (c : BoundedCoefficients lower upper) (n : ℤ) :
    0 < fullWeightRate c.val n :=
  fullWeightRate_pos lower upper c.val (coef_lower38 c) (coef_bound38 c) (coef_upper38 c) n

/-- `b_n / a_n ≤ c_+/c_-` and `b_n/a_n ≤ 1/(2πn)²` for `n ≠ 0`, so `∑ b_n/a_n < ∞`. -/
theorem summable_bRate_div38 (c : BoundedCoefficients lower upper) :
    Summable (fun n : ℤ => bRate38 c.val n / fullWeightRate c.val n) := by
  have ha := fullWeightRate_pos38 c
  have hs : Summable (fun n : ℤ => 1 / ((2 * Real.pi) ^ 2) * (1 / ((n : ℝ) ^ 2))) := by
    have := (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
    exact this.mul_left _
  refine Summable.of_norm_bounded_eventually (g := fun n : ℤ => 1 / ((2 * Real.pi) ^ 2) * (1 / ((n : ℝ) ^ 2)))
    hs ?_
  have hfin : {n : ℤ | n = 0}ᶜ ∈ (cofinite : Filter ℤ) :=
    Filter.mem_cofinite.2 (by simp)
  filter_upwards [hfin] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hb0 := bRate38_nonneg c n
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hb0 (ha n).le), div_le_iff₀ (ha n)]
  have h := bRate38_mul_sq_le38 c n
  have hp : 0 < (2 * Real.pi * n) ^ 2 := by positivity
  rw [mul_pow] at h
  have e : 1 / (2 * Real.pi) ^ 2 * (1 / (n : ℝ) ^ 2) * fullWeightRate c.val n =
      fullWeightRate c.val n / ((2 * Real.pi) ^ 2 * (n : ℝ) ^ 2) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  linarith

end Rates


/-! ## W12.04: the determinant `D_δ = ∏_n (1 - δ b_n/a_n) > 0` -/

section Determinant

variable {lower upper : ℝ}

/-- `x_n = δ b_n / a_n`. -/
def tiltRatio38 (c : ℕ → ℝ) (δ : ℝ) (n : ℤ) : ℝ := δ * bRate38 c n / fullWeightRate c n

theorem tiltRatio38_nonneg (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ) (n : ℤ) :
    0 ≤ tiltRatio38 c.val δ n :=
  div_nonneg (mul_nonneg hδ0.le (bRate38_nonneg c n)) (fullWeightRate_pos38 c n).le

/-- `x_n ≤ δ c_+/c_- < 1`. -/
theorem tiltRatio38_le38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ) (n : ℤ) :
    tiltRatio38 c.val δ n ≤ δ * (upper / lower) := by
  have ha := fullWeightRate_pos38 c n
  unfold tiltRatio38
  rw [div_le_iff₀ ha]
  have := bRate38_le38 c n
  nlinarith

theorem tiltRatio38_lt_one (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) (n : ℤ) : tiltRatio38 c.val δ n < 1 := by
  have hl := coef_lower38 c
  refine (tiltRatio38_le38 c hδ0 n).trans_lt ?_
  rw [← mul_div_assoc, div_lt_one hl]
  exact hδ

theorem summable_tiltRatio38 (c : BoundedCoefficients lower upper) (δ : ℝ) :
    Summable (tiltRatio38 c.val δ) := by
  have := (summable_bRate_div38 c).mul_left δ
  refine this.congr (fun n => ?_)
  unfold tiltRatio38
  ring

/-- `1 - x_n = ã_n / a_n`. -/
theorem one_sub_tiltRatio38 (c : BoundedCoefficients lower upper) (δ : ℝ) (n : ℤ) :
    1 - tiltRatio38 c.val δ n =
      fullWeightRate (tiltCoef38 c.val δ) n / fullWeightRate c.val n := by
  have ha := (fullWeightRate_pos38 c n).ne'
  rw [fullWeightRate_tilt38]
  unfold tiltRatio38
  field_simp

/-- `D_δ = ∏_{n∈ℤ} (1 - δ b_n/a_n)` (the unconditional infinite product over `ℤ`, with the
convention of mathlib's `tprod`; positivity and convergence are proved in `hasProd_tilt38`). -/
def Dtilt38 (c : ℕ → ℝ) (δ : ℝ) : ℝ := ∏' n : ℤ, (1 - tiltRatio38 c δ n)

/-- **W12.04.** For `0 < δ`, `δ c_+ < c_-`, the product `∏_n (1 - δ b_n/a_n)` converges (as a
`HasProd` over finite subsets of `ℤ`, hence along every exhaustion) to a strictly positive limit. -/
theorem hasProd_tilt38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) :
    0 < Dtilt38 c.val δ ∧ HasProd (fun n : ℤ => 1 - tiltRatio38 c.val δ n) (Dtilt38 c.val δ) := by
  have hl := coef_lower38 c
  have hup : 0 < upper := lt_of_lt_of_le hl c.property.2.1
  set q : ℝ := δ * (upper / lower) with hq
  have hq1 : q < 1 := by
    rw [hq, ← mul_div_assoc, div_lt_one hl]; exact hδ
  have hq0 : 0 < 1 - q := by linarith
  set f : ℤ → ℝ := fun n => 1 - tiltRatio38 c.val δ n with hf
  have hfpos : ∀ n, 0 < f n := fun n => by
    simp only [hf]; linarith [tiltRatio38_lt_one c hδ0 hδ n]
  have hfle : ∀ n, 1 - q ≤ f n := fun n => by
    simp only [hf]; linarith [tiltRatio38_le38 c hδ0 n]
  have hlog : ∀ n, ‖Real.log (f n)‖ ≤ (1 - q)⁻¹ * tiltRatio38 c.val δ n := by
    intro n
    have hx0 := tiltRatio38_nonneg c hδ0 n
    have h1 : f n ≤ 1 := by simp only [hf]; linarith
    have hlog0 : Real.log (f n) ≤ 0 := Real.log_nonpos (hfpos n).le h1
    have hlogge : 1 - (f n)⁻¹ ≤ Real.log (f n) := Real.one_sub_inv_le_log_of_pos (hfpos n)
    rw [Real.norm_eq_abs, abs_of_nonpos hlog0]
    have h2 : -(1 - (f n)⁻¹) = tiltRatio38 c.val δ n / f n := by
      have h0 := (hfpos n).ne'
      have hfn : f n = 1 - tiltRatio38 c.val δ n := rfl
      rw [hfn] at h0 ⊢
      field_simp
      ring
    have h3 : tiltRatio38 c.val δ n / f n ≤ (1 - q)⁻¹ * tiltRatio38 c.val δ n := by
      rw [div_eq_mul_inv, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ hx0
      exact inv_anti₀ hq0 (hfle n)
    linarith
  have hsum : Summable (fun n => Real.log (f n)) :=
    Summable.of_norm_bounded ((summable_tiltRatio38 c δ).mul_left _) hlog
  have hH := Real.hasProd_of_hasSum_log hfpos hsum.hasSum
  have e : Dtilt38 c.val δ = Real.exp (∑' n, Real.log (f n)) := by
    unfold Dtilt38
    exact hH.tprod_eq
  refine ⟨?_, ?_⟩
  · rw [e]; exact Real.exp_pos _
  · rw [e]; exact hH

theorem tendsto_prod_tilt38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) :
    Tendsto (fun N : ℕ => ∏ n ∈ stdExh38 N, (1 - tiltRatio38 c.val δ n)) atTop
      (𝓝 (Dtilt38 c.val δ)) :=
  (hasProd_tilt38 c hδ0 hδ).2.comp isExhaustion_stdExh38.tendsto_atTop

end Determinant

end NlsGge.Birkhoff
end
