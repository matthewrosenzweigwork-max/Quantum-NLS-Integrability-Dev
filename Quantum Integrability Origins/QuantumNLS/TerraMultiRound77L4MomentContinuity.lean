import QuantumNLS.TerraMultiRound77YCorrection
import QuantumNLS.TerraMultiRound77LowEquivalence

/-! Exact-order transfer through the native L4 correction. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Reg010LowBasic
open QuantumNLS.Reg010LowCorrection QuantumNLS.Reg010LowL4Space QuantumNLS.Reg010LowL4Correction
open QuantumNLS.TerraMultiRound77YCorrection QuantumNLS.TerraMultiRound77LowEquivalence
namespace QuantumNLS.TerraMultiRound77L4MomentContinuity

/-- The unnormalized low-order correction integral is continuous on native L4. -/
theorem raw_L4_correction_continuous {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (s : ℝ) (hs0 : 0 < s) (hs : s < 1) :
    Continuous (fun u : L4T L => ∫ Y in Ioi (0 : ℝ), Y ^ (2*s-3) * correction κ hκ (toL2 u) Y) := by
  rw [continuous_iff_continuousAt]
  intro u
  obtain ⟨C, _, hi, hb⟩ := L4_correction_majorant κ hκ (Metric.closedBall u 1)
    Metric.isBounded_closedBall s hs0 hs
  apply continuousAt_of_dominated (bound := fun Y => C * L4Majorant s Y)
  · exact Eventually.of_forall (fun v => (QuantumNLS.Reg010LowL4Correction.weighted_correction_measurable κ hκ s v).aestronglyMeasurable)
  · filter_upwards [Metric.closedBall_mem_nhds u (by norm_num : (0 : ℝ) < 1)] with v hv
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    simpa only [Real.norm_eq_abs] using hb v hv Y hY
  · exact hi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    exact (continuous_const.mul ((fixed_Y_continuous κ hκ hY).comp toL2_continuous)).continuousAt

/-- On native L4 fields, same-order free moment convergence transfers to
physical moment convergence, throughout 0<s<1. -/
theorem physical_moment_tendsto_of_free_L4 {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : ℕ → L4T L) (v : L4T L) (s : ℝ)
    (hs0 : 0 < s) (hs : s < 1) (hu : Tendsto u atTop (𝓝 v))
    (hfree : ∀ j, Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L (toL2 (u j))))
    (hfreev : Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L (toL2 v)))
    (hlim : Tendsto (fun j => ∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L (toL2 (u j))) atTop
      (𝓝 (∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L (toL2 v)))) :
    Tendsto (fun j => ∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ (toL2 (u j))) atTop
      (𝓝 (∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ (toL2 v))) := by
  let K : ℝ := 2 / (∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1)
  let R : L4T L → ℝ := fun w => ∫ Y in Ioi 0, Y ^ (2*s-3) * correction κ hκ (toL2 w) Y
  have hR : Tendsto (fun j => R (u j)) atTop (𝓝 (R v)) :=
    ((raw_L4_correction_continuous hκ s hs0 hs).tendsto v).comp hu
  have hid : ∀ w : L4T L, Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L (toL2 w)) →
      (∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ (toL2 w)) =
      (∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L (toL2 w)) + K * R w := by
    intro w hw
    have hm := (physical_free_moment_iff_L4 hκ w s hs0 hs).mpr hw
    have hh := physical_free_Y_correction hκ (toL2 w) s hs0 hs hm hw
    dsimp [K, R]
    linarith
  have hh := hlim.add (hR.const_mul K)
  rw [← hid v hfreev] at hh
  exact hh.congr' (Eventually.of_forall fun j => (hid (u j) (hfree j)).symm)

#print axioms raw_L4_correction_continuous
#print axioms physical_moment_tendsto_of_free_L4
end QuantumNLS.TerraMultiRound77L4MomentContinuity
