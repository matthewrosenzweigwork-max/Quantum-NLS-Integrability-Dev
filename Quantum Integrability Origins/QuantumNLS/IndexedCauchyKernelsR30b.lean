import QuantumNLS.IndexedInverseContourR29b
import QuantumNLS.IndexedContourBoundsR29b

/-! Chosen radius-8 Cauchy kernels for the full z derivative of the actual
LOCAL-009 inverse. The bounds and coefficient limits precede representation;
operator-norm estimates alone are not used to infer kernel convergence. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 30000
noncomputable section
open Set Metric Filter Topology Complex MeasureTheory
open scoped BigOperators
namespace QuantumNLS.IndexedCauchyKernelsR30b
open TensorCarrier KernelDefinition KernelConvergence LocalPlacement
  IndexedKernelIntegralR29b IndexedKernelContinuityR29b
attribute [local instance] IndexedKernelContinuityR29b.kernelNormed
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance kernelComplexSpace (p : ℕ) : NormedSpace ℂ (BoundedSymmetricKernel H p) :=
  ContinuousLinearMap.toNormedSpace
section Generic

def scaleList {N : ℕ} (c : ℂ) (A : KernelList (H := H) N) : KernelList (H := H) N :=
  fun p => c • A p

theorem converges_smul {R : ℝ} {A : ∀ N : ℕ, KernelList (H := H) N}
    {Alim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hA : ConvergesOnRadius R A Alim) (c : ℂ) :
    ConvergesOnRadius R (fun N => scaleList c (A N)) (fun p => c • Alim p) := by
  obtain ⟨⟨C, hC⟩, hlim⟩ := hA
  refine ⟨⟨‖c‖*C, fun N => ?_⟩, fun p => ?_⟩
  · change RadiusBound.radiusBound R (c • A N) ≤ _
    rw [RadiusBound.radiusBound_smul]
    exact mul_le_mul_of_nonneg_left (hC N) (norm_nonneg c)
  · apply tendsto_iff_norm_sub_tendsto_zero.mp
    have h := (tendsto_iff_norm_sub_tendsto_zero.mpr (hlim p)).const_smul c
    apply h.congr'
    filter_upwards [eventually_ge_atTop p] with N hN
    simp only [coeffAt,dite_eq_left hN,scaleList]

theorem represented_smul (N : ℕ) (c : ℂ) (A : KernelList (H := H) N) :
    RadiusBound.represented (scaleList c A) = c • RadiusBound.represented A := by
  unfold RadiusBound.represented
  calc
    _ = ∑ p : Fin (N+1), c • RadiusBound.Q N p.1 (by omega) (A p) := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [scaleList,RadiusBound.Q_eq_genericU_N_r]
      exact RootOverlapLimit.genericU_smul N p.1 _ c (A p)
    _ = _ := Finset.smul_sum.symm

theorem weighted_radius {R B C : ℝ} (hB : 0 ≤ B)
    (A : ∀ N : ℕ, KernelList (H := H) N) (c : ℂ)
    (hb : ∀ N, RadiusBound.radiusBound R (A N) ≤ B) (hc : ‖c‖ ≤ C) (N : ℕ) :
    RadiusBound.radiusBound R (scaleList c (A N)) ≤ C*B := by
  change RadiusBound.radiusBound R (c • A N) ≤ _
  rw [RadiusBound.radiusBound_smul]
  exact (mul_le_mul_of_nonneg_left (hb N) (norm_nonneg c)).trans
    (mul_le_mul_of_nonneg_right hc hB)

end Generic

def weight (r θ : ℝ) : ℂ :=
  (2*Real.pi*I)⁻¹ * (deriv (circleMap 0 r) θ / (circleMap 0 r θ)^2)

theorem circle_ne_zero {r : ℝ} (hr : 0 < r) (θ : ℝ) : circleMap 0 r θ ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_circleMap_zero,abs_of_pos hr]
  exact hr.ne'

theorem continuous_weight {r : ℝ} (hr : 0 < r) : Continuous (weight r) := by
  unfold weight
  simp only [deriv_circleMap]
  exact continuous_const.mul ((by fun_prop : Continuous (fun θ : ℝ => circleMap 0 r θ*I)).div
    ((continuous_circleMap 0 r).pow 2) (fun θ => pow_ne_zero 2 (circle_ne_zero hr θ)))

theorem norm_weight {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ‖weight r θ‖ = (2*Real.pi)⁻¹/r := by
  simp only [weight,deriv_circleMap,norm_mul,norm_inv,norm_div,norm_pow,
    norm_I,mul_one,norm_circleMap_zero,abs_of_pos hr]
  norm_num [Complex.norm_real,abs_of_nonneg Real.pi_pos.le]
  field_simp

attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal

open PhysicalTensor IndexedInverseR28b IndexedInverseSeriesR28b IndexedInverseBoundsR29b
  IndexedCFCBindingR29b IndexedContourBoundsR29b IndexedInverseContourR29b
  LOCAL009R23PhysicalInverse LOCAL009R23OperatorContour LOCAL009R22Geometry
  LOCAL009R22LiteralScalar PeriodReconstruction
variable {L κ : ℝ} [Fact (0 < L)]

def circleKernels (κ : ℝ) (z : ℂ) (θ : ℝ) :=
  fun N => scaleList (weight (cauchyRadius L) θ)
    (inverseKernels (L := L) κ (circleMap z (cauchyRadius L) θ) N)

def circleLimit (κ : ℝ) (z : ℂ) (θ : ℝ) :=
  fun p => weight (cauchyRadius L) θ • inverseLimit (L := L) κ (circleMap z (cauchyRadius L) θ) p

def derivativeKernels (κ : ℝ) (z : ℂ) :=
  intList (circleKernels (L := L) κ z) 0 (2*Real.pi)

def derivativeLimit (κ : ℝ) (z : ℂ) :=
  intLimit (circleLimit (L := L) κ z) 0 (2*Real.pi)

def derivativeBound (κ L : ℝ) : ℝ :=
  (W κ*q κ L/(1-q κ L))/cauchyRadius L

theorem cauchyRadius_pos : 0 < cauchyRadius L := by
  have hL : 0 < L := Fact.out
  unfold cauchyRadius halfWidth
  positivity

theorem circle_in_tube (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L))
    (θ : ℝ) : circleMap z (cauchyRadius L) θ ∈ tube L n := by
  exact (contour_ball_subset_band (by have hL : 0 < L := Fact.out; unfold halfWidth; positivity) hz)
    (sphere_subset_closedBall (circleMap_mem_sphere z (cauchyRadius_pos (L := L)).le θ))

theorem continuous_circle_coord (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L))
    (N : ℕ) (p : Fin (N+1)) :
    ContinuousOn (fun θ => circleKernels (L := L) κ z θ N p) (Icc 0 (2*Real.pi)) := by
  change ContinuousOn (fun θ => weight (cauchyRadius L) θ •
    inverseKernels (L := L) κ (circleMap z (cauchyRadius L) θ) N p) _
  exact (continuous_weight (cauchyRadius_pos (L := L))).continuousOn.smul
    ((continuousOn_inverseKernels (L := L) hκ hs n N p).comp
      (continuous_circleMap z (cauchyRadius L)).continuousOn (fun θ _ => circle_in_tube n hz θ))

/-- Full chosen-kernel convergence of the Cauchy derivative, at every point
of every printed rectangle. The circle and all its integrability duties are
constructed from the source geometry. -/
theorem derivative_converges (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) :
    ConvergesOnRadius 8 (derivativeKernels (L := L) κ z) (derivativeLimit (L := L) κ z) := by
  have hq := q_bounds hκ hs
  have hB : 0 ≤ W κ*q κ L/(1-q κ L) :=
    div_nonneg (mul_nonneg (W_pos hκ).le hq.1) (by linarith)
  exact integrated_converges (by norm_num) (by positivity)
    (circleKernels (L := L) κ z) (circleLimit (L := L) κ z)
    (continuous_circle_coord hκ hs n hz)
    (fun θ _ N => weighted_radius hB _ _ (radius_bound_inverse hκ hs n (circle_in_tube n hz θ))
      (norm_weight (cauchyRadius_pos (L := L)) θ).le N)
    (fun θ _ => converges_smul
      (inverse_series_converges hκ hs n (circle_in_tube n hz θ)).1 _)

theorem derivative_radius_bound (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) (N : ℕ) :
    RadiusBound.radiusBound 8 (derivativeKernels (L := L) κ z N) ≤ derivativeBound κ L := by
  have hq := q_bounds hκ hs
  have hB : 0 ≤ W κ*q κ L/(1-q κ L) :=
    div_nonneg (mul_nonneg (W_pos hκ).le hq.1) (by linarith)
  have hi := integrated_radius_bound (by norm_num : (0 : ℝ) ≤ 8)
    (by positivity : (0 : ℝ) ≤ 2*Real.pi) (circleKernels (L := L) κ z)
    (continuous_circle_coord hκ hs n hz)
    (fun θ _ N => weighted_radius hB _ _ (radius_bound_inverse hκ hs n (circle_in_tube n hz θ))
      (norm_weight (cauchyRadius_pos (L := L)) θ).le N) N
  change RadiusBound.radiusBound 8 (derivativeKernels (L := L) κ z N) ≤ _ at hi
  refine hi.trans_eq ?_
  unfold derivativeBound
  field_simp
  ring

/-- These chosen kernels represent the full operator derivative in the
literal correction, rather than a derivative of scalar eigenvalues alone. -/
theorem represented_derivative (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) :
    RadiusBound.represented (derivativeKernels (L := L) κ z N) =
      deriv (inverseOp L κ 1 (eps N) N) z := by
  have hr := cauchyRadius_pos (L := L)
  have hc := represented_intList (a := 0) (b := 2*Real.pi) (circleKernels (L := L) κ z)
    (fun M p => by simpa only [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi)] using
      continuous_circle_coord hκ hs n hz M p) N
  have hd : DifferentiableOn ℂ (inverseOp L κ 1 (eps N) N) (tube L n) := by
    intro w hw
    exact (LOCAL009R23PhysicalInverse.inverseOp_spec hκ (by norm_num : (0 : ℝ) < 1)
      (show κ*L*1 ≤ 1/1000000 by nlinarith) hN (eps_pos hN) (eps_le_one hN)
      (by rw [eps_budget hN]) n hw).2.1.differentiableWithinAt
  have hball : closedBall z (cauchyRadius L) ⊆ tube L n :=
    contour_ball_subset_band (by have hL : 0 < L := Fact.out; unfold halfWidth; positivity) hz
  have hf := DifferentiableOn.deriv_eq_smul_circleIntegral
    (E := Sector L N →L[ℂ] Sector L N) (f := inverseOp L κ 1 (eps N) N) (c := z) hr (hd.mono hball)
  have he : RadiusBound.represented (derivativeKernels (L := L) κ z N) =
      (2*Real.pi*I)⁻¹ • ∮ w in C(z,cauchyRadius L), (1/(w-z)^2) • inverseOp L κ 1 (eps N) N w := by
    unfold derivativeKernels
    rw [hc,circleIntegral,← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro θ _
    change RadiusBound.represented (scaleList (weight (cauchyRadius L) θ)
      (inverseKernels (L := L) κ (circleMap z (cauchyRadius L) θ) N)) = _
    rw [represented_smul,represented_actual_cfc hκ hs hN n (circle_in_tube n hz θ)]
    simp only [weight,smul_smul,div_eq_mul_inv,circleMap,zero_add,add_sub_cancel_left,deriv_circleMap]
    congr 1
    ring
  rw [he,hf,smul_smul,inv_mul_cancel₀ two_pi_I_ne_zero,one_smul]

end QuantumNLS.IndexedCauchyKernelsR30b
#print axioms QuantumNLS.IndexedCauchyKernelsR30b.derivative_converges
#print axioms QuantumNLS.IndexedCauchyKernelsR30b.derivative_radius_bound
#print axioms QuantumNLS.IndexedCauchyKernelsR30b.represented_derivative
