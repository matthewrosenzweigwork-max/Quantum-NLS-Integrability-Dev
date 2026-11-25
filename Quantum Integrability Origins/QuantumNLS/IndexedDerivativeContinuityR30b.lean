import QuantumNLS.IndexedCauchyKernelsR30b

/-! The chosen Cauchy derivative kernels vary continuously along every
printed rectangle. Dominated continuity uses the actual circle majorant. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 20000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Filter Topology Complex MeasureTheory
namespace QuantumNLS.IndexedDerivativeContinuityR30b
open LOCAL009R22LiteralScalar
open PhysicalTensor KernelDefinition KernelConvergence LocalPlacement Local013PowerSeries
  IndexedInverseR28b IndexedInverseSeriesR28b IndexedInverseBoundsR29b IndexedCFCBindingR29b
  IndexedKernelContinuityR29b IndexedKernelIntegralR29b IndexedCauchyKernelsR30b
  IndexedContourBoundsR29b PeriodReconstruction
attribute [local instance] IndexedKernelContinuityR29b.kernelNormed
attribute [local instance] IndexedCauchyKernelsR30b.kernelComplexSpace
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
variable {L κ : ℝ} [Fact (0 < L)]

theorem continuousOn_derivativeKernels (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    (n : ℤ) (N : ℕ) (p : Fin (N+1)) :
    ContinuousOn (fun z => derivativeKernels (L := L) κ z N p)
      (Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) := by
  let G := Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)
  have hq := q_bounds hκ hs
  let B := W κ*q κ L/(1-q κ L)
  have hB : 0 ≤ B := div_nonneg (mul_nonneg (W_pos hκ).le hq.1) (by linarith)
  have hγ (θ : ℝ) : Continuous (fun z : ℂ => circleMap z (cauchyRadius L) θ) := by
    unfold circleMap
    fun_prop
  have hc (θ : ℝ) : ContinuousOn (fun z => circleKernels (L := L) κ z θ N p) G := by
    exact ((continuousOn_inverseKernels (L := L) hκ hs n N p).comp
      (hγ θ).continuousOn (fun z hz => circle_in_tube n hz θ)).const_smul (weight (cauchyRadius L) θ)
  intro z hz
  change ContinuousWithinAt (fun z => ∫ θ in (0 : ℝ)..2*Real.pi,
    circleKernels (L := L) κ z θ N p) G z
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := fun _ => ((2*Real.pi)⁻¹/cauchyRadius L)*B)
  · filter_upwards [self_mem_nhdsWithin] with w hw
    simpa only [uIoc_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi)] using
      (show IntervalIntegrable (fun θ => circleKernels (L := L) κ w θ N p) volume 0 (2*Real.pi) from
      (show ContinuousOn (fun θ => circleKernels (L := L) κ w θ N p) (uIcc 0 (2*Real.pi)) from by
        simpa only [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi)] using
          continuous_circle_coord hκ hs n hw N p).intervalIntegrable).1.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact Eventually.of_forall (fun θ _ =>
      (norm_coeff_le_radiusBound (by norm_num : (1 : ℝ) ≤ 8)
        (circleKernels (L := L) κ w θ N) p).trans
        (weighted_radius hB _ _ (radius_bound_inverse hκ hs n (circle_in_tube n hw θ))
          (norm_weight (cauchyRadius_pos (L := L)) θ).le N))
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun θ _ => hc θ z hz

end QuantumNLS.IndexedDerivativeContinuityR30b
#print axioms QuantumNLS.IndexedDerivativeContinuityR30b.continuousOn_derivativeKernels
