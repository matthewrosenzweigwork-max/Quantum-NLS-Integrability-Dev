import NlsGge.Measure.CountableReconstruction

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.Measure

private def fullWeightedModeLinear {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (n : ℤ) :
    ℂ →ₗ[ℝ] NlsGge.Pilot.FullWeightedHilbert c s where
  toFun z :=
    (NlsGge.Pilot.weightedIsometry (NlsGge.Pilot.fullModeWeight c s)).symm
      (lp.single 2 n ((Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * z))
  map_add' z u := by
    change (NlsGge.Pilot.weightedIsometry (NlsGge.Pilot.fullModeWeight c s)).symm
      (lp.single 2 n ((Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * (z + u))) =
        (NlsGge.Pilot.weightedIsometry (NlsGge.Pilot.fullModeWeight c s)).symm
          (lp.single 2 n ((Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * z)) +
        (NlsGge.Pilot.weightedIsometry (NlsGge.Pilot.fullModeWeight c s)).symm
          (lp.single 2 n ((Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * u))
    rw [mul_add, lp.single_add, map_add]
  map_smul' r z := by
    change (NlsGge.Pilot.weightedIsometry (NlsGge.Pilot.fullModeWeight c s)).symm
      (lp.single 2 n ((Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * ((r : ℂ) * z))) =
        (r : ℂ) • (NlsGge.Pilot.weightedIsometry (NlsGge.Pilot.fullModeWeight c s)).symm
          (lp.single 2 n ((Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * z))
    rw [show (Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * ((r : ℂ) * z) =
      (r : ℂ) • ((Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * z) by
        simp only [smul_eq_mul]; ring, lp.single_smul, map_smul]

private lemma fullWeightedModeLinear_norm {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (n : ℤ) (z : ℂ) :
    ‖fullWeightedModeLinear c s n z‖ = Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) * ‖z‖ := by
  change ‖(NlsGge.Pilot.weightedIsometry (NlsGge.Pilot.fullModeWeight c s)).symm
    (lp.single 2 n ((Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * z))‖ = _
  rw [LinearIsometryEquiv.norm_map, lp.norm_single (by norm_num), norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

def fullWeightedModeMap {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (n : ℤ) :
    ℂ →L[ℝ] NlsGge.Pilot.FullWeightedHilbert c s :=
  (fullWeightedModeLinear c s n).mkContinuous (Real.sqrt (NlsGge.Pilot.fullModeWeight c s n))
    (fun z => (fullWeightedModeLinear_norm c s n z).le)

lemma fullWeightedModeMap_apply {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (n : ℤ) (z : ℂ) :
    fullWeightedModeMap c s n z =
      (NlsGge.Pilot.weightedIsometry (NlsGge.Pilot.fullModeWeight c s)).symm
        (lp.single 2 n ((Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * z)) := rfl

lemma fullWeightedModeMap_coordinate {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (n m : ℤ) (z : ℂ) :
    (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s)
      from fullWeightedModeMap c s n z) m = if m = n then z else 0 := by
  change (lp.single (E := fun _ : ℤ => ℂ) 2 n
      ((Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * z)) m /
    (Real.sqrt (NlsGge.Pilot.fullModeWeight c s m) : ℂ) = if m = n then z else 0
  by_cases h : m = n
  · subst m
    simp only [lp.coeFn_single, Pi.single_eq_same]
    field_simp [NlsGge.Pilot.weightSqrt_ne_zero (NlsGge.Pilot.fullModeWeight c s) n]
    simp
  · simp [lp.coeFn_single, Pi.single_apply, h, Ne.symm h]

lemma fullWeightedModeMap_norm {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (n : ℤ) (z : ℂ) :
    ‖fullWeightedModeMap c s n z‖ = Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) * ‖z‖ :=
  fullWeightedModeLinear_norm c s n z

lemma fullWeightedSequencePartial_eq_sumModeMaps {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (N : ℕ) (z : ℤ → ℂ) :
    fullWeightedSequencePartial c s N z =
      ∑ n ∈ NlsGge.Pilot.symmetricModes N, fullWeightedModeMap c s n (z n) := by
  change (NlsGge.Pilot.weightedIsometry (NlsGge.Pilot.fullModeWeight c s)).symm
    (∑ n ∈ NlsGge.Pilot.symmetricModes N,
      lp.single 2 n ((Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * z n)) =
      ∑ n ∈ NlsGge.Pilot.symmetricModes N,
        (NlsGge.Pilot.weightedIsometry (NlsGge.Pilot.fullModeWeight c s)).symm
          (lp.single 2 n ((Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * z n))
  simp only [map_sum]

end NlsGge.Measure
