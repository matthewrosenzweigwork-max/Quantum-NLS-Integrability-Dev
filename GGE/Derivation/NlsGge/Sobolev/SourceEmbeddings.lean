import NlsGge.Sobolev.SourceWeighted

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.Pilot

section RealComparison

variable (w v : ℤ → ℝ) [Fact (∀ n : ℤ, 0 < w n)] [Fact (∀ n : ℤ, 0 < v n)]

def weightedRealComparisonLinear (C : ℝ) (hC : 0 ≤ C)
    (hcmp : ∀ n : ℤ, v n ≤ C * w n) : WeightedRealHilbert w →ₗ[ℝ] WeightedRealHilbert v where
  toFun x := weightedComparison w v C hC hcmp (show WeightedHilbert w from x)
  map_add' x y := (weightedComparison w v C hC hcmp).map_add x y
  map_smul' r x := by
    change weightedComparison w v C hC hcmp ((r : ℂ) • (show WeightedHilbert w from x)) =
      (r : ℂ) • weightedComparison w v C hC hcmp (show WeightedHilbert w from x)
    exact (weightedComparison w v C hC hcmp).map_smul (r : ℂ) x

theorem weightedRealComparison_norm_le (C : ℝ) (hC : 0 ≤ C)
    (hcmp : ∀ n : ℤ, v n ≤ C * w n) (x : WeightedRealHilbert w) :
    ‖weightedRealComparisonLinear w v C hC hcmp x‖ ≤ Real.sqrt C * ‖x‖ :=
  weightedComparison_norm_le w v C hC hcmp (show WeightedHilbert w from x)

def weightedRealComparisonContinuous (C : ℝ) (hC : 0 ≤ C)
    (hcmp : ∀ n : ℤ, v n ≤ C * w n) : WeightedRealHilbert w →L[ℝ] WeightedRealHilbert v :=
  (weightedRealComparisonLinear w v C hC hcmp).mkContinuous (Real.sqrt C)
    (weightedRealComparison_norm_le w v C hC hcmp)

theorem weightedRealComparison_apply (C : ℝ) (hC : 0 ≤ C)
    (hcmp : ∀ n : ℤ, v n ≤ C * w n) (x : WeightedRealHilbert w) (n : ℤ) :
    (show WeightedHilbert v from weightedRealComparisonContinuous w v C hC hcmp x) n =
      (show WeightedHilbert w from x) n := rfl

theorem weightedRealComparison_injective (C : ℝ) (hC : 0 ≤ C)
    (hcmp : ∀ n : ℤ, v n ≤ C * w n) :
    Function.Injective (weightedRealComparisonContinuous w v C hC hcmp) := by
  intro x y h
  apply Subtype.ext
  funext n
  exact congrArg (fun z : WeightedRealHilbert v => (show WeightedHilbert v from z) n) h

end RealComparison

def sobolevModeWeight (r : ℝ) (n : ℤ) : ℝ := Real.rpow (japaneseBracket n) (2 * r)

instance sobolevModeWeightPositive (r : ℝ) : Fact (∀ n : ℤ, 0 < sobolevModeWeight r n) :=
  ⟨fun n => Real.rpow_pos_of_pos (japaneseBracket_pos n) _⟩

abbrev SobolevHilbert (r : ℝ) : Type := WeightedRealHilbert (sobolevModeWeight r)

def sourceSobolevBound (lower upper r s : ℝ) (hlower : 0 < lower) : ℝ :=
  (sourceSobolevComparison lower upper r s hlower).choose

theorem sourceSobolevBound_nonneg (lower upper r s : ℝ) (hlower : 0 < lower) :
    0 ≤ sourceSobolevBound lower upper r s hlower :=
  (sourceSobolevComparison lower upper r s hlower).choose_spec.1

theorem sourceSobolevBound_dominates (lower upper r s : ℝ) (hlower : 0 < lower)
    (c : BoundedCoefficients lower upper) (n : ℤ) :
    sobolevModeWeight r n ≤ sourceSobolevBound lower upper r s hlower * fullModeWeight c s n :=
  (sourceSobolevComparison lower upper r s hlower).choose_spec.2 c n

def fullWeightedToSobolev {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s r : ℝ) : FullWeightedHilbert c s →L[ℝ] SobolevHilbert r :=
  weightedRealComparisonContinuous (fullModeWeight c s) (sobolevModeWeight r)
    (sourceSobolevBound lower upper r s c.property.1)
    (sourceSobolevBound_nonneg lower upper r s c.property.1)
    (sourceSobolevBound_dominates lower upper r s c.property.1 c)

theorem fullWeightedToSobolev_apply {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s r : ℝ) (x : FullWeightedHilbert c s) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight r) from fullWeightedToSobolev c s r x) n =
      (show WeightedHilbert (fullModeWeight c s) from x) n := rfl

theorem fullWeightedToSobolev_injective {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s r : ℝ) : Function.Injective (fullWeightedToSobolev c s r) :=
  weightedRealComparison_injective _ _ _ _ _

theorem fullWeightedToSobolev_norm_le {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s r : ℝ) (x : FullWeightedHilbert c s) :
    ‖fullWeightedToSobolev c s r x‖ ≤
      Real.sqrt (sourceSobolevBound lower upper r s c.property.1) * ‖x‖ :=
  weightedRealComparison_norm_le _ _ _ _ _ x

theorem fullModeWeight_restrict {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s t : ℝ) (hst : s ≤ t) (n : ℤ) : fullModeWeight c t n ≤ fullModeWeight c s n := by
  apply mul_le_mul_of_nonneg_left _ (sourceRate_pos c n).le
  exact Real.rpow_le_rpow_of_exponent_le (japaneseBracket_one_le n) (by linarith)

def fullWeightedRestriction {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s t : ℝ) (hst : s ≤ t) : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c t :=
  weightedRealComparisonContinuous (fullModeWeight c s) (fullModeWeight c t) 1 (by norm_num)
    (fun n => by simpa only [one_mul] using fullModeWeight_restrict c s t hst n)

theorem fullWeightedRestriction_apply {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s t : ℝ) (hst : s ≤ t) (x : FullWeightedHilbert c s) (n : ℤ) :
    (show WeightedHilbert (fullModeWeight c t) from fullWeightedRestriction c s t hst x) n =
      (show WeightedHilbert (fullModeWeight c s) from x) n := rfl

theorem fullWeightedRestriction_injective {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s t : ℝ) (hst : s ≤ t) :
    Function.Injective (fullWeightedRestriction c s t hst) :=
  weightedRealComparison_injective _ _ _ _ _

theorem fullWeightedRestriction_norm_le {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s t : ℝ) (hst : s ≤ t) (x : FullWeightedHilbert c s) :
    ‖fullWeightedRestriction c s t hst x‖ ≤ ‖x‖ := by
  change ‖weightedRealComparisonLinear (fullModeWeight c s) (fullModeWeight c t)
    1 (by norm_num) (fun n => by simpa only [one_mul] using fullModeWeight_restrict c s t hst n) x‖ ≤ ‖x‖
  have h := weightedRealComparison_norm_le (fullModeWeight c s) (fullModeWeight c t)
    1 (by norm_num) (fun n => by simpa only [one_mul] using fullModeWeight_restrict c s t hst n) x
  simpa only [Real.sqrt_one, one_mul] using h

end NlsGge.Pilot
