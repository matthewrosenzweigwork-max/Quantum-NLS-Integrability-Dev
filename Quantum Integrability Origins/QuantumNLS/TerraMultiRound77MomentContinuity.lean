import QuantumNLS.TerraMultiRound77YCorrection
import QuantumNLS.TerraMultiRound77LowEquivalence

/-! Low-order transfer of free moment convergence to physical moments. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Reg010LowBasic
open QuantumNLS.Reg010LowCorrection QuantumNLS.TerraMultiRound77YCorrection
open QuantumNLS.TerraMultiRound77LowEquivalence
namespace QuantumNLS.TerraMultiRound77MomentContinuity

/-- The correction integral itself is continuous on L² in the low range,
without requiring evaluation of its positive normalization. -/
theorem raw_correction_continuous {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (s : ℝ) (hs0 : 0 < s) (hs : s < 1/2) :
    Continuous (fun u : L2T L => ∫ Y in Ioi (0 : ℝ), Y ^ (2*s-3) * correction κ hκ u Y) := by
  rw [continuous_iff_continuousAt]
  intro u
  obtain ⟨C, _, hi, hb⟩ := low_correction_majorant κ hκ (Metric.closedBall u 1)
    Metric.isBounded_closedBall s hs0 hs
  apply continuousAt_of_dominated (bound := fun Y => C * lowMajorant s Y)
  · exact Eventually.of_forall (fun v => (weighted_correction_measurable κ hκ s v).aestronglyMeasurable)
  · filter_upwards [Metric.closedBall_mem_nhds u (by norm_num : (0 : ℝ) < 1)] with v hv
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    simpa only [Real.norm_eq_abs] using hb v hv Y hY
  · exact hi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    exact (continuous_const.mul (fixed_Y_continuous κ hκ hY)).continuousAt

/-- Free moment convergence plus L² convergence implies physical moment
convergence at the same low order. Free moment convergence is an explicit
intermediate premise, not a claimed Sobolev consequence. -/
theorem physical_moment_tendsto_of_free {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : ℕ → L2T L) (v : L2T L) (s : ℝ)
    (hs0 : 0 < s) (hs : s < 1/2) (hu : Tendsto u atTop (𝓝 v))
    (hfree : ∀ j, Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L (u j)))
    (hfreev : Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L v))
    (hlim : Tendsto (fun j => ∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L (u j)) atTop
      (𝓝 (∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L v))) :
    Tendsto (fun j => ∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ (u j)) atTop
      (𝓝 (∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ v)) := by
  let K : ℝ := 2 / (∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1)
  let R : L2T L → ℝ := fun w => ∫ Y in Ioi 0, Y ^ (2*s-3) * correction κ hκ w Y
  have hR : Tendsto (fun j => R (u j)) atTop (𝓝 (R v)) :=
    ((raw_correction_continuous hκ s hs0 hs).tendsto v).comp hu
  have hid : ∀ w : L2T L, Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L w) →
      (∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ w) =
      (∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L w) + K * R w := by
    intro w hw
    have hm := (physical_free_moment_iff_L2 hκ w s hs0 hs).mpr hw
    have hh := physical_free_Y_correction hκ w s hs0 (by linarith) hm hw
    dsimp [K, R]
    linarith
  have hh := hlim.add (hR.const_mul K)
  rw [← hid v hfreev] at hh
  exact hh.congr' (Eventually.of_forall fun j => (hid (u j) (hfree j)).symm)

#print axioms raw_correction_continuous
#print axioms physical_moment_tendsto_of_free
end QuantumNLS.TerraMultiRound77MomentContinuity
