import QuantumNLS.Reg010LowRiccati

/-! The continuous fractional correction on all of L² for 0<s<1/2. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.Reg010LowCorrection
open QuantumNLS.PhysicalTensor QuantumNLS.Reg010LowBasic QuantumNLS.Reg010LowRiccati

variable {L : ℝ} [Fact (0 < L)]

def lowMajorant (s Y : ℝ) : ℝ :=
  if Y ≤ 1 then Y ^ (2 * s - 1) else Y ^ (2 * s - 2)

theorem lowMajorant_integrable (s : ℝ) (hs : 0 < s) (hs' : s < 1 / 2) :
    IntegrableOn (lowMajorant s) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  constructor
  · have h : IntegrableOn (fun Y : ℝ => Y ^ (2 * s - 1)) (Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo,
        intervalIntegral.integrableOn_Ioo_rpow_iff (show (0 : ℝ) < 1 by norm_num)]
      linarith
    apply h.congr_fun
    · intro Y hY
      simp [lowMajorant, hY.2]
    · exact measurableSet_Ioc
  · have h : IntegrableOn (fun Y : ℝ => Y ^ (2 * s - 2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
    apply h.congr_fun
    · intro Y hY
      simp [lowMajorant, not_le_of_gt (mem_Ioi.mp hY)]
    · exact measurableSet_Ioi

theorem low_correction_majorant (κ : ℝ) (hκ : 0 < κ) (B : Set (L2T L))
    (hB : Bornology.IsBounded B) (s : ℝ) (hs : 0 < s) (hs' : s < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ IntegrableOn (fun Y => C * lowMajorant s Y) (Ioi 0) ∧
      ∀ u ∈ B, ∀ Y > 0, |Y ^ (2 * s - 3) * correction κ hκ u Y| ≤ C * lowMajorant s Y := by
  obtain ⟨C, hC, hb⟩ := correction_bounds κ hκ B hB
  refine ⟨C, hC, (lowMajorant_integrable s hs hs').const_mul C, ?_⟩
  intro u hu Y hY
  have hp := Real.rpow_nonneg hY.le (2 * s - 3)
  rw [abs_mul, abs_of_nonneg hp]
  calc
    _ ≤ Y ^ (2 * s - 3) * (C * (if Y ≤ 1 then Y ^ 2 else Y)) :=
      mul_le_mul_of_nonneg_left (hb u hu Y hY) hp
    _ = C * lowMajorant s Y := by
      by_cases hy : Y ≤ 1
      · simp only [ite_eq_left hy, lowMajorant]
        rw [mul_left_comm, ← Real.rpow_two Y, ← Real.rpow_add hY]
        congr 1
        congr 1
        ring
      · simp only [ite_eq_right hy, lowMajorant]
        rw [mul_left_comm]
        conv_lhs => arg 2; arg 2; rw [← Real.rpow_one Y]
        rw [← Real.rpow_add hY]
        congr 1
        congr 1
        ring

def coefficient (s : ℝ) : ℝ := 2 * Real.sin (Real.pi * s) / Real.pi

/-- The same scalar integral is used for the low and L⁴ ranges. -/
def J (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (u : L2T L) : ℝ :=
  coefficient s * ∫ Y in Ioi (0 : ℝ), Y ^ (2 * s - 3) * correction κ hκ u Y

theorem weighted_correction_measurable (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (u : L2T L) :
    Measurable (fun Y : ℝ => Y ^ (2 * s - 3) * correction κ hκ u Y) :=
  (measurable_id.pow_const _).mul (correction_measurable κ hκ u)

theorem weighted_correction_integrable (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs : 0 < s) (hs' : s < 1 / 2) (u : L2T L) :
    IntegrableOn (fun Y : ℝ => Y ^ (2 * s - 3) * correction κ hκ u Y) (Ioi 0) := by
  obtain ⟨C, _, hi, hb⟩ := low_correction_majorant κ hκ {u} Bornology.isBounded_singleton s hs hs'
  apply hi.mono' (weighted_correction_measurable κ hκ s u).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
  simpa only [Real.norm_eq_abs] using hb u (mem_singleton u) Y hY

/-- Dominated convergence uses one L² ball about the point, so no additional
higher-order moment assumption is hidden in this continuity theorem. -/
theorem J_continuous (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs : 0 < s) (hs' : s < 1 / 2) :
    Continuous (J (L := L) κ hκ s) := by
  unfold J
  apply continuous_const.mul
  rw [continuous_iff_continuousAt]
  intro u
  obtain ⟨C, _, hi, hb⟩ := low_correction_majorant κ hκ (Metric.closedBall u 1)
    Metric.isBounded_closedBall s hs hs'
  apply continuousAt_of_dominated (bound := fun Y => C * lowMajorant s Y)
  · exact Eventually.of_forall (fun v =>
      (weighted_correction_measurable κ hκ s v).aestronglyMeasurable)
  · filter_upwards [Metric.closedBall_mem_nhds u (by norm_num : (0 : ℝ) < 1)] with v hv
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    simpa only [Real.norm_eq_abs] using hb v hv Y hY
  · exact hi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    exact (continuous_const.mul (fixed_Y_continuous κ hκ hY)).continuousAt

/-- Quantitative bounded-set mapping for the printed correction. -/
theorem J_bounded_on_bounded (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs : 0 < s) (hs' : s < 1 / 2) (B : Set (L2T L)) (hB : Bornology.IsBounded B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ B, |J κ hκ s u| ≤ K := by
  obtain ⟨C, hC, hi, hb⟩ := low_correction_majorant κ hκ B hB s hs hs'
  let K := |coefficient s| * |∫ Y in Ioi (0 : ℝ), C * lowMajorant s Y|
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro u hu
  have hh : ‖∫ Y in Ioi (0 : ℝ), Y ^ (2 * s - 3) * correction κ hκ u Y‖ ≤
      ∫ Y in Ioi (0 : ℝ), C * lowMajorant s Y := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    simpa only [Real.norm_eq_abs] using hb u hu Y hY
  rw [Real.norm_eq_abs] at hh
  rw [J, abs_mul]
  exact mul_le_mul_of_nonneg_left (hh.trans (le_abs_self _)) (abs_nonneg _)

#print axioms lowMajorant_integrable
#print axioms low_correction_majorant
#print axioms weighted_correction_measurable
#print axioms weighted_correction_integrable
#print axioms J_continuous
#print axioms J_bounded_on_bounded
end QuantumNLS.Reg010LowCorrection

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowCorrection." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowCorrection." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round45 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
