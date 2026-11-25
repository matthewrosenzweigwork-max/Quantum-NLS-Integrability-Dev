import QuantumNLS.IndexedQuotientKernelsR30b

/-! A chosen expansion for the entire literal correction. The factor 1/N
kills every fixed chosen coefficient by a uniform radius bound. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
open Set Metric Filter Topology Complex
namespace QuantumNLS.IndexedCorrectionKernelsR30b
open LOCAL009R22LiteralScalar
open PhysicalTensor TensorCarrier KernelDefinition KernelConvergence LocalPlacement Local013PowerSeries
  IndexedInverseR28b IndexedInverseSeriesR28b IndexedInverseBoundsR29b IndexedCFCBindingR29b
  IndexedCauchyKernelsR30b IndexedQuotientKernelsR30b IndexedInverseContourR29b
  LOCAL009R23PhysicalInverse LOCAL009R23OperatorContour PeriodReconstruction
  PlacementFiberPrefixProductExpansionLOCAL011
attribute [local instance] IndexedKernelContinuityR29b.kernelNormed
attribute [local instance] IndexedCauchyKernelsR30b.kernelComplexSpace
variable {L κ : ℝ} [Fact (0 < L)]

def correctionKernels (κ : ℝ) (z : ℂ) (N : ℕ) : KernelList (H := L2T L) N :=
  scaleList ((κ^2*eps N/2 : ℝ) : ℂ) (chosenProductKernelList N
    (quotientKernels (L := L) κ z N) (derivativeKernels (L := L) κ z N))

def kernelBound (κ L : ℝ) : ℝ := (κ^2/2)*quotientBound κ L*derivativeBound κ L

theorem bounds_nonneg (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) :
    0 ≤ quotientBound κ L ∧ 0 ≤ derivativeBound κ L ∧ 0 ≤ kernelBound κ L := by
  have hq := q_bounds hκ hs
  have hL : 0 < L := Fact.out
  have hd : 0 < 1-q κ L := by linarith
  have hQ : 0 ≤ quotientBound κ L := by unfold quotientBound LOCAL009R22Ratio.ratioBound; positivity
  have hD : 0 ≤ derivativeBound κ L := by
    unfold derivativeBound
    exact div_nonneg (div_nonneg (mul_nonneg (W_pos hκ).le hq.1) hd.le)
      (cauchyRadius_pos (L := L)).le
  exact ⟨hQ,hD,by unfold kernelBound; positivity⟩

theorem correction_radius_bound (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) (N : ℕ) :
    RadiusBound.radiusBound 8 (correctionKernels (L := L) κ z N) ≤ kernelBound κ L*eps N := by
  have hB := bounds_nonneg hκ hs
  have hε : 0 ≤ eps N := by unfold eps; positivity
  change RadiusBound.radiusBound 8 (((κ^2*eps N/2 : ℝ) : ℂ) • chosenProductKernelList N
    (quotientKernels (L := L) κ z N) (derivativeKernels (L := L) κ z N)) ≤ _
  rw [RadiusBound.radiusBound_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ κ^2*eps N/2)]
  calc
    _ ≤ (κ^2*eps N/2)*(RadiusBound.radiusBound 8 (quotientKernels (L := L) κ z N)*
        RadiusBound.radiusBound 8 (derivativeKernels (L := L) κ z N)) :=
      mul_le_mul_of_nonneg_left (chosenProductKernelList_radius_le (by norm_num) _ _) (by positivity)
    _ ≤ (κ^2*eps N/2)*(quotientBound κ L*derivativeBound κ L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (quotient_radius_bound hκ hs n (contour_mem_tube n hz) N)
        (derivative_radius_bound hκ hs n hz N)
        (RadiusBound.radiusBound_nonneg (by norm_num) _) hB.1
    _ = _ := by unfold kernelBound; ring

theorem correction_converges_zero (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) :
    ConvergesOnRadius 8 (correctionKernels (L := L) κ z) (fun _ => 0) := by
  have hB := (bounds_nonneg hκ hs).2.2
  have he (N : ℕ) : eps N ≤ 1 := by
    by_cases hN : 0 < N
    · exact eps_le_one hN
    · have : N = 0 := by omega
      simp [this,eps]
  refine ⟨⟨kernelBound κ L,fun N => (correction_radius_bound hκ hs n hz N).trans
    (by nlinarith [he N])⟩,fun j => ?_⟩
  simp only [sub_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun N => (norm_coeffAt_le (by norm_num : (1 : ℝ) ≤ 8)
      (correctionKernels (L := L) κ z) N j).trans (correction_radius_bound hκ hs n hz N))
  simpa only [mul_zero] using IndexedContourBoundsR29b.eps_tendsto_zero.const_mul (kernelBound κ L)

theorem represented_correction (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) :
    RadiusBound.represented (correctionKernels (L := L) κ z N) =
      integrand L κ 1 (eps N) N z-inverseOp L κ 1 (eps N) N z := by
  rw [correctionKernels,represented_smul,represented_chosenProductKernelList,
    represented_quotient hκ hs hN n (contour_mem_tube n hz),represented_derivative hκ hs hN n hz]
  simp only [integrand,add_sub_cancel_left]
  rfl

end QuantumNLS.IndexedCorrectionKernelsR30b
#print axioms QuantumNLS.IndexedCorrectionKernelsR30b.correction_radius_bound
#print axioms QuantumNLS.IndexedCorrectionKernelsR30b.correction_converges_zero
#print axioms QuantumNLS.IndexedCorrectionKernelsR30b.represented_correction
