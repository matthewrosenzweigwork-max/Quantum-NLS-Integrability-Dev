import QuantumNLS.IndexedCorrectionKernelsR30b
import QuantumNLS.IndexedDerivativeContinuityR30b
import QuantumNLS.IndexedQuotientContinuityR30b
import QuantumNLS.Local014RealSymbol

/-! The complete literal corrected rectangular contour and its Hermitian
part have chosen radius-8 expansions. The principal kernels contain exactly
the leading inverse term: every correction coefficient tends to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 20000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Filter Topology Complex MeasureTheory
namespace QuantumNLS.IndexedCorrectedContourR30b
open LOCAL009R22LiteralScalar
open TensorCarrier KernelDefinition KernelConvergence LocalPlacement Local013PowerSeries
  IndexedCauchyKernelsR30b IndexedKernelIntegralR29b
attribute [local instance] IndexedKernelContinuityR29b.kernelNormed
attribute [local instance] IndexedCauchyKernelsR30b.kernelComplexSpace
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem converges_add {R : ℝ} (hR : 0 ≤ R)
    {A B : ∀ N : ℕ, KernelList (H := H) N}
    {Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hA : ConvergesOnRadius R A Alim) (hB : ConvergesOnRadius R B Blim) :
    ConvergesOnRadius R (fun N => A N+B N) (fun p => Alim p+Blim p) := by
  obtain ⟨⟨C,hC⟩,hl⟩ := hA
  obtain ⟨⟨D,hD⟩,hm⟩ := hB
  refine ⟨⟨C+D,fun N => (RadiusBound.radiusBound_add hR _ _).trans
    (add_le_add (hC N) (hD N))⟩,fun p => ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mp
  apply ((tendsto_iff_norm_sub_tendsto_zero.mpr (hl p)).add
    (tendsto_iff_norm_sub_tendsto_zero.mpr (hm p))).congr'
  filter_upwards [eventually_ge_atTop p] with N hN
  simp only [coeffAt,dite_eq_left hN,Pi.add_apply]

theorem represented_add (N : ℕ) (A B : KernelList (H := H) N) :
    RadiusBound.represented (A+B) = RadiusBound.represented A+RadiusBound.represented B := by
  unfold RadiusBound.represented
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [RadiusBound.Q_eq_genericU_N_r,Pi.add_apply]
  exact RootOverlapLimit.genericU_add N p.1 _ (A p) (B p)

open PhysicalTensor IndexedInverseR28b IndexedInverseSeriesR28b IndexedInverseBoundsR29b
  IndexedCFCBindingR29b IndexedContourBoundsR29b IndexedInverseContourR29b
  IndexedCorrectionKernelsR30b IndexedDerivativeContinuityR30b IndexedQuotientKernelsR30b
  IndexedKernelContinuityR29b IndexedQuotientContinuityR30b
  LOCAL009R23PhysicalInverse LOCAL009R23OperatorContour PeriodReconstruction
  PlacementFiberPrefixProductExpansionLOCAL011
variable {L κ : ℝ} [Fact (0 < L)]

def fullKernels (κ : ℝ) (z : ℂ) (N : ℕ) : KernelList (H := L2T L) N :=
  inverseKernels (L := L) κ z N+correctionKernels (L := L) κ z N

set_option backward.isDefEq.respectTransparency false in
theorem full_converges (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) :
    ConvergesOnRadius 8 (fullKernels (L := L) κ z) (inverseLimit (L := L) κ z) := by
  change ConvergesOnRadius 8 (fun N => inverseKernels (L := L) κ z N+correctionKernels (L := L) κ z N)
    (inverseLimit (L := L) κ z)
  simpa only [add_zero] using converges_add (by norm_num : (0 : ℝ) ≤ 8)
    (inverse_series_converges hκ hs n (contour_mem_tube n hz)).1 (correction_converges_zero hκ hs n hz)

theorem represented_full (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) :
    RadiusBound.represented (fullKernels (L := L) κ z N) = integrand L κ 1 (eps N) N z := by
  rw [fullKernels,represented_add,represented_actual_cfc hκ hs hN n (contour_mem_tube n hz),
    represented_correction hκ hs hN n hz]
  abel

theorem full_radius_bound (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) (N : ℕ) :
    RadiusBound.radiusBound 8 (fullKernels (L := L) κ z N) ≤
      W κ*q κ L/(1-q κ L)+kernelBound κ L := by
  have he : eps N ≤ 1 := by
    by_cases hN : 0 < N
    · exact eps_le_one hN
    · have : N = 0 := by omega
      simp [this,eps]
  exact (RadiusBound.radiusBound_add (by norm_num) _ _).trans
    (add_le_add (radius_bound_inverse hκ hs n (contour_mem_tube n hz) N)
      ((correction_radius_bound hκ hs n hz N).trans
        (by nlinarith [(bounds_nonneg hκ hs).2.2])))

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_full (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ)
    (N : ℕ) (p : Fin (N+1)) :
    ContinuousOn (fun z => fullKernels (L := L) κ z N p)
      (Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) := by
  let G := Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)
  have hi := (continuousOn_inverseKernels (L := L) hκ hs n N p).mono (fun z hz => contour_mem_tube n hz)
  have hQ : ContinuousOn (fun z => quotientKernels (L := L) κ z N) G :=
    continuousOn_pi.mpr (fun p => (continuousOn_quotientKernels (L := L) hκ hs n N p).mono
      (fun z hz => contour_mem_tube n hz))
  have hD : ContinuousOn (fun z => derivativeKernels (L := L) κ z N) G :=
    continuousOn_pi.mpr (continuousOn_derivativeKernels hκ hs n N)
  have hp := (continuous_product_coord (H := L2T L) N p).comp_continuousOn (hQ.prodMk hD)
  exact (hi.add (hp.const_smul (((κ^2*eps N/2 : ℝ) : ℂ)))).congr (fun z hz => rfl)

theorem integrated_full (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ)
    {a b : ℝ} (hab : a ≤ b) (γ : ℝ → ℂ) (hc : Continuous γ)
    (hm : ∀ x ∈ Icc a b, γ x ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) :
    ConvergesOnRadius 8 (intList (fun x => fullKernels (L := L) κ (γ x)) a b)
      (intLimit (fun x => inverseLimit (L := L) κ (γ x)) a b) ∧
    ∀ N : ℕ, 0 < N → RadiusBound.represented (intList (fun x => fullKernels (L := L) κ (γ x)) a b N) =
      ∫ x in a..b, integrand L κ 1 (eps N) N (γ x) := by
  have hK (N : ℕ) (p : Fin (N+1)) := (continuousOn_full hκ hs n N p).comp hc.continuousOn hm
  refine ⟨integrated_converges (by norm_num) hab _ _ hK
    (fun x hx N => full_radius_bound hκ hs n (hm x hx) N)
    (fun x hx => full_converges hκ hs n (hm x hx)),fun N hN => ?_⟩
  rw [represented_intList (a := a) (b := b) _ (fun M p => by simpa only [Function.comp_def,uIcc_of_le hab] using hK M p) N]
  apply intervalIntegral.integral_congr
  intro x hx
  exact represented_full hκ hs hN n (hm x (by simpa only [uIcc_of_le hab] using hx))

end QuantumNLS.IndexedCorrectedContourR30b
#print axioms QuantumNLS.IndexedCorrectedContourR30b.full_converges
#print axioms QuantumNLS.IndexedCorrectedContourR30b.represented_full
#print axioms QuantumNLS.IndexedCorrectedContourR30b.integrated_full
