import QuantumNLS.TerraMultiRound74Majorant
import Mathlib.MeasureTheory.Integral.Prod

/-! Measurability and integration of the actual upper-order correction. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.TerraMultiRound75Correction
open QuantumNLS.TranslatedCorrelation QuantumNLS.Reg014Moments
open QuantumNLS.Reg014Continuity QuantumNLS.TerraMultiRound74Majorant
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound61FiniteDivision
open QuantumNLS.TerraMultiRound64FieldIdentity QuantumNLS.FreeLimit

variable {L : ℝ} [Fact (0 < L)]

theorem kernel_integral_measurable (μ : Measure ℝ) [SFinite μ] (r : ℕ) :
    Measurable (fun Y : ℝ => ∫ t, kernel r Y t ∂μ) := by
  have h : Measurable (fun z : ℝ × ℝ => kernel r z.1 z.2) := by
    unfold kernel
    exact ((measurable_fst.pow_const 2).mul (measurable_snd.pow_const (2*r))).div
      ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem divided_measurable (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (r : ℕ) :
    Measurable (fun Y : ℝ => dividedDifference μ ν Y r) := by
  induction r with
  | zero => exact (kernel_integral_measurable μ 0).sub (kernel_integral_measurable ν 0)
  | succ r ih =>
    simp only [dividedDifference]
    exact ((measurable_id.pow_const 2).mul measurable_const).sub ((measurable_id.pow_const 2).mul ih)

theorem correction_aestronglyMeasurable (κ : ℝ) (hκ : 0 < κ) (u : Hk L 1) :
    AEStronglyMeasurable (fun Y => Dfun κ hκ 2 u.val Y) (volume.restrict (Ioi 0)) := by
  let μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val
  let ν := freeMeasure L u.val
  have hμ : IsFiniteMeasure μ := by
    dsimp [μ]
    rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas]
    infer_instance
  have hν : IsFiniteMeasure ν := by
    dsimp [ν]
    rw [← QuantumNLS.FullMass.Mmeas_zero_coupling]
    infer_instance
  apply ((divided_measurable μ ν 2).aestronglyMeasurable).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
  exact (Dfun_eq_divided κ hκ 1 (by omega) u.val hY
    (representative_hsq (L := L) 1 u)).symm

def correction (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (u : Hk L 1) : ℝ :=
  ∫ Y in Ioi 0, Y ^ (2 * s - 5) * Dfun κ hκ 2 u.val Y

theorem correction_integrable (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs1 : 1 < s) (hs2 : s < 2) (u : Hk L 1) :
    IntegrableOn (fun Y => Y ^ (2 * s - 5) * Dfun κ hκ 2 u.val Y) (Ioi 0) := by
  obtain ⟨C, hC, hint, hb⟩ := upper_correction_majorant κ hκ {u}
    (Bornology.isBounded_singleton) s hs1 hs2
  have hp : AEStronglyMeasurable (fun Y : ℝ => Y ^ (2 * s - 5)) (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro Y hY
    exact (continuousAt_id.rpow_const (Or.inl (ne_of_gt hY))).continuousWithinAt
  apply hint.mono' (hp.mul (correction_aestronglyMeasurable κ hκ u))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
  simpa only [Real.norm_eq_abs, Pi.mul_apply] using hb u (mem_singleton u) Y hY

/-- The absolutely convergent upper correction depends continuously on the field in H¹. -/
theorem correction_continuous (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs1 : 1 < s) (hs2 : s < 2) : Continuous (correction κ hκ s : Hk L 1 → ℝ) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  obtain ⟨C, hC, hint, hb⟩ := upper_correction_majorant κ hκ (Metric.ball u 1)
    Metric.isBounded_ball s hs1 hs2
  unfold correction
  apply continuousAt_of_dominated (bound := fun Y => C * upperMajorant s Y)
  · exact Filter.Eventually.of_forall (fun v => (correction_integrable κ hκ s hs1 hs2 v).aestronglyMeasurable)
  · filter_upwards [Metric.ball_mem_nhds u (show (0 : ℝ) < 1 by norm_num)] with v hv
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    simpa only [Real.norm_eq_abs] using hb v hv Y hY
  · exact hint
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    exact (continuous_const.mul (Dfun_continuous κ hκ 2 (by omega) hY)).continuousAt

/-- Uniform control of the correction integral on bounded H¹ sets. -/
theorem correction_bounded (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs1 : 1 < s) (hs2 : s < 2) (B : Set (Hk L 1))
    (hB : Bornology.IsBounded B) :
    ∃ K : ℝ, ∀ u ∈ B, |correction κ hκ s u| ≤ K := by
  obtain ⟨C, hC, hint, hb⟩ := upper_correction_majorant κ hκ B hB s hs1 hs2
  refine ⟨∫ Y in Ioi 0, C * upperMajorant s Y, ?_⟩
  intro u hu
  unfold correction
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hint
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
  simpa only [Real.norm_eq_abs] using hb u hu Y hY

#print axioms correction_bounded
#print axioms correction_continuous
#print axioms kernel_integral_measurable
#print axioms divided_measurable
#print axioms correction_aestronglyMeasurable
#print axioms correction_integrable
end QuantumNLS.TerraMultiRound75Correction
