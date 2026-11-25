import QuantumNLS.Reg010LowL4Error
import QuantumNLS.Reg010LowL4Space

/-! The continuous fractional correction on native L⁴ for 0<s<1. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.Reg010LowL4Correction
open QuantumNLS.PhysicalTensor QuantumNLS.Reg010LowBasic
open QuantumNLS.Reg010LowCorrection QuantumNLS.Reg010LowL4Error QuantumNLS.Reg010LowL4Space

variable {L : ℝ} [Fact (0 < L)]

/-- A uniform quadratic/constant bound on every bounded subset of native L⁴. -/
theorem L4_correction_bounds (κ : ℝ) (hκ : 0 < κ) (B : Set (L4T L))
    (hB : Bornology.IsBounded B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ B, ∀ Y > 0,
      |correction κ hκ (toL2 u) Y| ≤ C * (if Y ≤ 1 then Y ^ 2 else 1) := by
  obtain ⟨U, hU⟩ := isBounded_iff_forall_norm_le.mp hB
  let V := max U 0
  let A := inclusionConstant L * V
  have hA : 0 ≤ A := by dsimp [A, inclusionConstant]; positivity
  let Y₀ := max 1 (max (Real.log 3 / L) (16 * κ * A ^ 2))
  have hY₀ : 1 ≤ Y₀ := le_max_left _ _
  have hn : ∀ u ∈ B, ‖toL2 u‖ ≤ A := by
    intro u hu
    exact (toL2_norm u).trans (mul_le_mul_of_nonneg_left
      ((hU u hu).trans (le_max_left _ _)) (by dsimp [inclusionConstant]; positivity))
  have hs : ∀ u ∈ B, ∀ Y > 0, |correction κ hκ (toL2 u) Y| ≤ A ^ 2 * Y ^ 2 := by
    intro u hu Y hY
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hn u hu) 2) (sq_nonneg Y)
    exact (small_bound κ hκ (toL2 u) hY).trans (by nlinarith)
  have hl : ∀ u ∈ B, ∀ Y : ℝ, Y₀ ≤ Y → |correction κ hκ (toL2 u) Y| ≤ 4 * κ * V ^ 4 := by
    intro u hu Y hY
    have ht : QuantumNLS.RootH1RatioConvergence.threshold κ (toL2 u) ≤ Y := by
      apply le_trans _ hY
      unfold QuantumNLS.RootH1RatioConvergence.threshold Y₀
      gcongr
      exact hn u hu
    have hh := L4_large_bound κ hκ (toL2 u) (toL2_fourth_integrable u) ht
    rw [toL2_fourth_integral] at hh
    exact hh.trans (by gcongr; exact (hU u hu).trans (le_max_left _ _))
  let C := max (A ^ 2) (max (4 * κ * V ^ 4) (A ^ 2 * Y₀ ^ 2))
  refine ⟨C, (sq_nonneg A).trans (le_max_left _ _), ?_⟩
  intro u hu Y hY
  by_cases h1 : Y ≤ 1
  · simp only [ite_eq_left h1]
    exact (hs u hu Y hY).trans (by gcongr; exact le_max_left _ _)
  · simp only [ite_eq_right h1, mul_one]
    by_cases h0 : Y₀ ≤ Y
    · exact (hl u hu Y h0).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hs u hu Y hY).trans ((mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hY.le (le_of_not_ge h0) 2) (sq_nonneg A)).trans
          ((le_max_right _ _).trans (le_max_right _ _)))

def L4Majorant (s Y : ℝ) : ℝ :=
  if Y ≤ 1 then Y ^ (2 * s - 1) else Y ^ (2 * s - 3)

theorem L4Majorant_integrable (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    IntegrableOn (L4Majorant s) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  constructor
  · have h : IntegrableOn (fun Y : ℝ => Y ^ (2 * s - 1)) (Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo,
        intervalIntegral.integrableOn_Ioo_rpow_iff (show (0 : ℝ) < 1 by norm_num)]
      linarith
    apply h.congr_fun
    · intro Y hY
      simp [L4Majorant, hY.2]
    · exact measurableSet_Ioc
  · have h : IntegrableOn (fun Y : ℝ => Y ^ (2 * s - 3)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
    apply h.congr_fun
    · intro Y hY
      simp [L4Majorant, not_le_of_gt (mem_Ioi.mp hY)]
    · exact measurableSet_Ioi

theorem L4_correction_majorant (κ : ℝ) (hκ : 0 < κ) (B : Set (L4T L))
    (hB : Bornology.IsBounded B) (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ IntegrableOn (fun Y => C * L4Majorant s Y) (Ioi 0) ∧
      ∀ u ∈ B, ∀ Y > 0, |Y ^ (2 * s - 3) * correction κ hκ (toL2 u) Y| ≤ C * L4Majorant s Y := by
  obtain ⟨C, hC, hb⟩ := L4_correction_bounds κ hκ B hB
  refine ⟨C, hC, (L4Majorant_integrable s hs hs').const_mul C, ?_⟩
  intro u hu Y hY
  have hp := Real.rpow_nonneg hY.le (2 * s - 3)
  rw [abs_mul, abs_of_nonneg hp]
  calc
    _ ≤ Y ^ (2 * s - 3) * (C * (if Y ≤ 1 then Y ^ 2 else 1)) :=
      mul_le_mul_of_nonneg_left (hb u hu Y hY) hp
    _ = C * L4Majorant s Y := by
      by_cases hy : Y ≤ 1
      · simp only [ite_eq_left hy, L4Majorant]
        rw [mul_left_comm, ← Real.rpow_two Y, ← Real.rpow_add hY]
        congr 1
        congr 1
        ring
      · simp [L4Majorant, hy, mul_comm]

/-- The printed correction pulled back along the native L⁴ inclusion. -/
def J4 (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (u : L4T L) : ℝ :=
  J κ hκ s (toL2 u)

theorem weighted_correction_measurable (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (u : L4T L) :
    Measurable (fun Y : ℝ => Y ^ (2 * s - 3) * correction κ hκ (toL2 u) Y) :=
  (measurable_id.pow_const _).mul (correction_measurable κ hκ (toL2 u))

theorem weighted_correction_integrable (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs : 0 < s) (hs' : s < 1) (u : L4T L) :
    IntegrableOn (fun Y : ℝ => Y ^ (2 * s - 3) * correction κ hκ (toL2 u) Y) (Ioi 0) := by
  obtain ⟨C, _, hi, hb⟩ := L4_correction_majorant κ hκ {u} Bornology.isBounded_singleton s hs hs'
  apply hi.mono' (weighted_correction_measurable κ hκ s u).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
  simpa only [Real.norm_eq_abs] using hb u (mem_singleton u) Y hY

/-- Dominated convergence uses one L⁴ ball about the point, so no additional
higher-order moment assumption is hidden in this continuity theorem. -/
theorem J4_continuous (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    Continuous (J4 (L := L) κ hκ s) := by
  unfold J4 J
  apply continuous_const.mul
  rw [continuous_iff_continuousAt]
  intro u
  obtain ⟨C, _, hi, hb⟩ := L4_correction_majorant κ hκ (Metric.closedBall u 1)
    Metric.isBounded_closedBall s hs hs'
  apply continuousAt_of_dominated (bound := fun Y => C * L4Majorant s Y)
  · exact Eventually.of_forall (fun v =>
      (weighted_correction_measurable κ hκ s v).aestronglyMeasurable)
  · filter_upwards [Metric.closedBall_mem_nhds u (by norm_num : (0 : ℝ) < 1)] with v hv
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    simpa only [Real.norm_eq_abs] using hb v hv Y hY
  · exact hi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    exact (continuous_const.mul ((fixed_Y_continuous κ hκ hY).comp toL2_continuous)).continuousAt

/-- Quantitative bounded-set mapping for the printed correction. -/
theorem J4_bounded_on_bounded (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs : 0 < s) (hs' : s < 1) (B : Set (L4T L)) (hB : Bornology.IsBounded B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ B, |J4 κ hκ s u| ≤ K := by
  obtain ⟨C, hC, hi, hb⟩ := L4_correction_majorant κ hκ B hB s hs hs'
  let K := |coefficient s| * |∫ Y in Ioi (0 : ℝ), C * L4Majorant s Y|
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro u hu
  have hh : ‖∫ Y in Ioi (0 : ℝ), Y ^ (2 * s - 3) * correction κ hκ (toL2 u) Y‖ ≤
      ∫ Y in Ioi (0 : ℝ), C * L4Majorant s Y := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    simpa only [Real.norm_eq_abs] using hb u hu Y hY
  rw [Real.norm_eq_abs] at hh
  rw [J4, J, abs_mul]
  exact mul_le_mul_of_nonneg_left (hh.trans (le_abs_self _)) (abs_nonneg _)

#print axioms L4_correction_bounds
#print axioms L4Majorant_integrable
#print axioms L4_correction_majorant
#print axioms weighted_correction_measurable
#print axioms weighted_correction_integrable
#print axioms J4_continuous
#print axioms J4_bounded_on_bounded
end QuantumNLS.Reg010LowL4Correction

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowL4Correction." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowL4Correction." then
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
