import NlsGge.Sobolev.WeightedHilbert
import NlsGge.Weights.Entire

set_option autoImplicit false
noncomputable section
open scoped Real ENNReal

namespace NlsGge.Pilot

abbrev BoundedCoefficients (lower upper : ℝ) : Type :=
  {c : ℕ → ℝ // AdmittedCoefficients lower upper c}

def boundedCoefficients_const (lower upper : ℝ) (hlower : 0 < lower)
    (hlu : lower ≤ upper) : BoundedCoefficients lower upper :=
  ⟨fun _ => lower, hlower, hlu, fun _ => ⟨le_rfl, hlu⟩⟩

def sourceRate {lower upper : ℝ} (c : BoundedCoefficients lower upper) (n : ℤ) : ℝ :=
  NlsGge.Weights.weight c.val (2 * π * (n : ℝ))

def fullModeWeight {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s : ℝ) (n : ℤ) : ℝ := sourceRate c n * Real.rpow (japaneseBracket n) (-2 * s)

theorem sourceRate_lower {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (n : ℤ) : lower ≤ sourceRate c n :=
  NlsGge.Weights.weight_lower lower upper c.val c.property.1
    (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) _

theorem sourceRate_pos {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (n : ℤ) : 0 < sourceRate c n := c.property.1.trans_le (sourceRate_lower c n)

theorem fullModeWeight_pos {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s : ℝ) (n : ℤ) : 0 < fullModeWeight c s n := by
  apply mul_pos (sourceRate_pos c n)
  apply Real.rpow_pos_of_pos
  unfold japaneseBracket
  positivity

instance fullModeWeightPositive {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s : ℝ) : Fact (∀ n : ℤ, 0 < fullModeWeight c s n) :=
  ⟨fullModeWeight_pos c s⟩

abbrev FullWeightedHilbert {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s : ℝ) : Type := WeightedRealHilbert (fullModeWeight c s)

theorem fullWeightedHilbert_membership_iff {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) (x : ℤ → ℂ) :
    x ∈ weightedSubmodule (fullModeWeight c s) ↔ WeightedSquareSummable (sourceRate c) s x := by
  change Memℓp (weightedCoordinates (fullModeWeight c s) x) 2 ↔ _
  rw [weightedCoordinates_mem_l2_iff (fullModeWeight c s)
    (fun n => (fullModeWeight_pos c s n).le) x]
  rfl

theorem fullWeightedHilbert_norm_sq {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s : ℝ) (x : FullWeightedHilbert c s) :
    ‖x‖ ^ 2 = ∑' n : ℤ, sourceRate c n * Real.rpow (japaneseBracket n) (-2 * s) *
      ‖(show WeightedHilbert (fullModeWeight c s) from x) n‖ ^ 2 :=
  weightedHilbert_norm_sq (fullModeWeight c s) x

theorem sourceRate_term_lower {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (k : ℕ) (n : ℤ) :
    (lower / (Nat.factorial k : ℝ) ^ 4) * (2 * π * (n : ℝ)) ^ (2 * k) ≤ sourceRate c n := by
  have hs := NlsGge.Weights.weightTerm_summable lower upper c.val c.property.1
    (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) (2 * π * (n : ℝ))
  have hterm := hs.le_tsum k (fun j _ => NlsGge.Weights.weightTerm_nonneg
    lower c.val c.property.1 (fun j => (c.property.2.2 j).1) (2 * π * (n : ℝ)) j)
  have hc : lower / (Nat.factorial k : ℝ) ^ 4 ≤ NlsGge.coefficient c.val k := by
    unfold NlsGge.coefficient
    exact div_le_div_of_nonneg_right (c.property.2.2 k).1 (by positivity)
  have hp : 0 ≤ (2 * π * (n : ℝ)) ^ (2 * k) := by
    rw [pow_mul]
    positivity
  exact (mul_le_mul_of_nonneg_right hc hp).trans hterm

theorem sourceRate_polynomial_domination {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (k : ℕ) (n : ℤ) :
    japaneseBracket n ^ (2 * k) ≤
      (2 : ℝ) ^ (k - 1) *
        (lower⁻¹ + (lower / (Nat.factorial k : ℝ) ^ 4)⁻¹) * sourceRate c n := by
  have hlow := c.property.1
  have hcoef : 0 < lower / (Nat.factorial k : ℝ) ^ 4 := by positivity
  have hscale : (1 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hn : (n : ℝ) ^ 2 ≤ (2 * π * (n : ℝ)) ^ 2 := by
    simpa only [one_mul, mul_pow] using mul_le_mul_of_nonneg_right hscale (sq_nonneg (n : ℝ))
  have hnPow : (n : ℝ) ^ (2 * k) ≤ (2 * π * (n : ℝ)) ^ (2 * k) := by
    simpa only [pow_mul] using pow_le_pow_left₀ (sq_nonneg (n : ℝ)) hn k
  have hterm : (n : ℝ) ^ (2 * k) ≤
      sourceRate c n / (lower / (Nat.factorial k : ℝ) ^ 4) := by
    apply (le_div_iff₀ hcoef).2
    calc
      (n : ℝ) ^ (2 * k) * (lower / (Nat.factorial k : ℝ) ^ 4) ≤
          (lower / (Nat.factorial k : ℝ) ^ 4) * (2 * π * (n : ℝ)) ^ (2 * k) := by
        nlinarith [mul_le_mul_of_nonneg_left hnPow hcoef.le]
      _ ≤ sourceRate c n := sourceRate_term_lower c k n
  have hzero : (1 : ℝ) ≤ sourceRate c n / lower := by
    apply (le_div_iff₀ hlow).2
    simpa using sourceRate_lower c n
  have hjap : japaneseBracket n ^ (2 * k) = (1 + (n : ℝ) ^ 2) ^ k := by
    unfold japaneseBracket
    rw [pow_mul, Real.sq_sqrt (by positivity)]
  rw [hjap]
  calc
    (1 + (n : ℝ) ^ 2) ^ k ≤
        (2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (2 * k)) := by
      simpa only [one_pow, ← pow_mul] using add_pow_le (by norm_num : (0 : ℝ) ≤ 1)
        (sq_nonneg (n : ℝ)) k
    _ ≤ (2 : ℝ) ^ (k - 1) * (sourceRate c n / lower +
        sourceRate c n / (lower / (Nat.factorial k : ℝ) ^ 4)) :=
      mul_le_mul_of_nonneg_left (add_le_add hzero hterm) (by positivity)
    _ = _ := by ring



/-- Uniform scalar consequence of actual full-series polynomial domination. -/
theorem sourceSobolevComparison (lower upper r s : ℝ) (hlower : 0 < lower) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : BoundedCoefficients lower upper) (n : ℤ),
      Real.rpow (japaneseBracket n) (2 * r) ≤ C * fullModeWeight c s n := by
  obtain ⟨k, hk⟩ := exists_nat_ge (r + s)
  let C : ℝ := (2 : ℝ) ^ (k - 1) *
    (lower⁻¹ + (lower / (Nat.factorial k : ℝ) ^ 4)⁻¹)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro c n
  have hjone : 1 ≤ japaneseBracket n := by
    unfold japaneseBracket
    apply Real.one_le_sqrt.2
    nlinarith [sq_nonneg (n : ℝ)]
  have hjpos : 0 < japaneseBracket n := zero_lt_one.trans_le hjone
  have hexp : 2 * (r + s) ≤ ((2 * k : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * (r + s) ≤ 2 * (k : ℝ) by linarith)
  have hpow : Real.rpow (japaneseBracket n) (2 * (r + s)) ≤ C * sourceRate c n := by
    calc
      Real.rpow (japaneseBracket n) (2 * (r + s)) ≤
          Real.rpow (japaneseBracket n) ((2 * k : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hjone hexp
      _ = japaneseBracket n ^ (2 * k) := Real.rpow_natCast _ _
      _ ≤ C * sourceRate c n := sourceRate_polynomial_domination c k n
  calc
    Real.rpow (japaneseBracket n) (2 * r) =
        Real.rpow (japaneseBracket n) (2 * (r + s)) *
          Real.rpow (japaneseBracket n) (-2 * s) := by
      calc
        Real.rpow (japaneseBracket n) (2 * r) =
            Real.rpow (japaneseBracket n) (2 * (r + s) + (-2 * s)) := by
          congr 1
          ring
        _ = _ := Real.rpow_add hjpos _ _
    _ ≤ (C * sourceRate c n) * Real.rpow (japaneseBracket n) (-2 * s) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hjpos.le _)
    _ = C * fullModeWeight c s n := by unfold fullModeWeight; ring

/-- Every source weighted member has actual square-summable Sobolev coordinates. -/
theorem sourceWeightedSquareSummable_sobolev {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s r : ℝ) (x : ℤ → ℂ)
    (hx : WeightedSquareSummable (sourceRate c) s x) : SobolevSquareSummable r x := by
  obtain ⟨C, hC, hcmp⟩ := sourceSobolevComparison lower upper r s c.property.1
  have hs := hx.mul_left C
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (Real.rpow_nonneg (by
    unfold japaneseBracket; positivity) _) (sq_nonneg _)) (fun n => ?_) hs
  calc
    Real.rpow (japaneseBracket n) (2 * r) * ‖x n‖ ^ 2 ≤
        (C * fullModeWeight c s n) * ‖x n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hcmp c n) (sq_nonneg _)
    _ = C * (sourceRate c n * Real.rpow (japaneseBracket n) (-2 * s) * ‖x n‖ ^ 2) := by
      unfold fullModeWeight
      ring

/-- Actual plain lp2 reconstruction coordinates, with membership proved first. -/
def fullWeightedSequenceL2 {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s : ℝ) (x : FullWeightedHilbert c s) : lp (fun _ : ℤ => ℂ) 2 := by
  let y : WeightedHilbert (fullModeWeight c s) := x
  refine ⟨(y : ℤ → ℂ), ?_⟩
  apply memℓp_gen
  have hy := (fullWeightedHilbert_membership_iff c s (y : ℤ → ℂ)).1 y.property
  have hs := sourceWeightedSquareSummable_sobolev c s 0 (y : ℤ → ℂ) hy
  have hz (n : ℤ) : Real.rpow (japaneseBracket n) 0 = 1 := Real.rpow_zero _
  have hs' : Summable (fun n : ℤ => ‖y n‖ ^ 2) := hs.congr (fun n => by
    change Real.rpow (japaneseBracket n) (2 * 0) * ‖y n‖ ^ 2 = ‖y n‖ ^ 2
    rw [mul_zero, hz, one_mul])
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs'

theorem fullWeightedSequenceL2_apply {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) (x : FullWeightedHilbert c s) (n : ℤ) :
    fullWeightedSequenceL2 c s x n =
      (show WeightedHilbert (fullModeWeight c s) from x) n := rfl


end NlsGge.Pilot
