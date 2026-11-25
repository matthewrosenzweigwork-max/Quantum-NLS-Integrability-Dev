import QuantumNLS.IndexedCFCBindingR29b
import QuantumNLS.IndexedInverseBoundsR29b

/-! Uniform operator-norm bounds for the full literal correction on the
printed rectangle, at ε=1/N. This is not a claim of kernel convergence of
the correction or a classical period claim. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
noncomputable section
open Complex Set Metric Filter Topology
namespace QuantumNLS.IndexedContourBoundsR29b
open PhysicalTensor IndexedInverseR28b IndexedInverseSeriesR28b
  IndexedCFCBindingR29b LOCAL009R23PhysicalInverse LOCAL009R22LiteralScalar
  LOCAL009R22Geometry LOCAL009R23OperatorContour LOCAL009R23DiagonalAnalytic
  LOCAL009R22Ratio PeriodReconstruction
variable {L κ : ℝ} [Fact (0 < L)]

def cauchyRadius (L : ℝ) : ℝ := halfWidth L/16

theorem source_radius_small (_hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) :
    0 < radius L 1 ∧ κ*radius L 1 ≤ 1/1000 := by
  have hL : 0 < L := Fact.out
  constructor
  · unfold radius halfWidth; positivity
  · have hh := source_small (M := 1) (show κ*L*1 ≤ 1/1000000 by nlinarith)
    calc
      κ*radius L 1 = 2*(κ*1/(halfWidth L/2)) := by unfold radius; ring
      _ ≤ 1/1000 := by linarith

/-- Cauchy's estimate applies to the full operator-valued inverse, with a
common inner-tube radius independent of n and N. -/
theorem derivative_bound (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) :
    ‖deriv (inverseOp L κ 1 (eps N) N) z‖ ≤ radius L 1/cauchyRadius L := by
  have hL : 0 < L := Fact.out
  have ha : 0 < halfWidth L := by unfold halfWidth; positivity
  have hr : 0 < cauchyRadius L := by unfold cauchyRadius; positivity
  have hb : closedBall z (cauchyRadius L) ⊆ tube L n := contour_ball_subset_band ha hz
  have spec (w : ℂ) (hw : w ∈ tube L n) :=
    inverseOp_spec hκ (by norm_num : (0 : ℝ) < 1)
      (show κ*L*1 ≤ 1/1000000 by nlinarith) hN (eps_pos hN) (eps_le_one hN)
      (by rw [eps_budget hN]) n hw
  have hd : DifferentiableOn ℂ (inverseOp L κ 1 (eps N) N) (tube L n) :=
    fun w hw => (spec w hw).2.1.differentiableWithinAt
  exact norm_deriv_le_of_forall_mem_sphere_norm_le (F := Sector L N →L[ℂ] Sector L N)
    (f := inverseOp L κ 1 (eps N) N) hr (hd.diffContOnCl_ball hb)
    (fun w hw => (spec w (hb (sphere_subset_closedBall hw))).2.2.2)

theorem quotient_bound (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    ‖quotientOp L κ 1 (eps N) N z‖ ≤ ratioBound κ (radius L 1) := by
  have hh := source_radius_small hκ hs
  have hp := inverseOp_spec hκ (by norm_num : (0 : ℝ) < 1)
    (show κ*L*1 ≤ 1/1000000 by nlinarith) hN (eps_pos hN) (eps_le_one hN)
    (by rw [eps_budget hN]) n hz
  have hq := quotient_spec hκ (by norm_num : (0 : ℝ) < 1)
    (show κ*L*1 ≤ 1/1000000 by nlinarith) hN (eps_pos hN) (eps_le_one hN)
    (by rw [eps_budget hN]) n hz
  apply norm_le_of_eigen (basis hκ (eps_pos hN) hN) _ _ hq.1
  · unfold ratioBound; positivity
  · intro m
    have he := (norm_eigen_le (basis hκ (eps_pos hN) hN) _ _ m (hp.1 m)).trans hp.2.2.2
    exact ratio_norm_le hκ hh.2 (source_phase_bound (Fact.out : 0 < L) n hz)
      (source_gap_bound (Fact.out : 0 < L) n hz) (mem_closedBall_zero_iff.mpr he)

def correctionBound (κ L : ℝ) : ℝ :=
  (κ^2/2)*ratioBound κ (radius L 1)*(radius L 1/cauchyRadius L)

theorem correctionBound_nonneg (hκ : 0 < κ) : 0 ≤ correctionBound κ L := by
  have hL : 0 < L := Fact.out
  unfold correctionBound ratioBound radius cauchyRadius halfWidth
  positivity

/-- The literal correction, including f/f', the full z derivative, and its
1/N prefactor, is uniformly O(1/N) in operator norm on the printed contour. -/
theorem correction_bound (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) :
    ‖integrand L κ 1 (eps N) N z-inverseOp L κ 1 (eps N) N z‖ ≤
      correctionBound κ L*eps N := by
  have hL : 0 < L := Fact.out
  have ha : 0 < halfWidth L := by unfold halfWidth; positivity
  have hε := eps_pos hN
  have hm : z ∈ tube L n := (contour_ball_subset_band ha hz)
    (mem_closedBall_self (by unfold halfWidth; positivity))
  rw [integrand,add_sub_cancel_left,RadiusBound.norm_smul_kernel,
    Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ κ^2*eps N/2)]
  calc
    _ ≤ (κ^2*eps N/2)*(‖quotientOp L κ 1 (eps N) N z‖*
        ‖deriv (inverseOp L κ 1 (eps N) N) z‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (κ^2*eps N/2)*(ratioBound κ (radius L 1)*(radius L 1/cauchyRadius L)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (quotient_bound hκ hs hN n hm) (derivative_bound hκ hs hN n hz)
        (ContinuousLinearMap.opNorm_nonneg (deriv (inverseOp L κ 1 (eps N) N) z))
        (by unfold ratioBound; positivity)
    _ = _ := by unfold correctionBound; ring


theorem eps_tendsto_zero : Tendsto eps atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

/-- At every point of the literal contour, the complete correction vanishes
in norm in the mean-field limit. Sector spaces may vary with N. -/
theorem correction_norm_tendsto_zero (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) :
    Tendsto (fun N => ‖integrand L κ 1 (eps N) N z-inverseOp L κ 1 (eps N) N z‖)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun N =>
    ContinuousLinearMap.opNorm_nonneg (integrand L κ 1 (eps N) N z-inverseOp L κ 1 (eps N) N z))
    (show ∀ᶠ N in atTop, ‖integrand L κ 1 (eps N) N z-inverseOp L κ 1 (eps N) N z‖ ≤
        correctionBound κ L*eps N from by
      filter_upwards [eventually_gt_atTop 0] with N hN
      exact correction_bound hκ hs hN n hz)
  simpa only [mul_zero] using eps_tendsto_zero.const_mul (correctionBound κ L)

end QuantumNLS.IndexedContourBoundsR29b
#print axioms QuantumNLS.IndexedContourBoundsR29b.derivative_bound
#print axioms QuantumNLS.IndexedContourBoundsR29b.quotient_bound
#print axioms QuantumNLS.IndexedContourBoundsR29b.correction_bound

#print axioms QuantumNLS.IndexedContourBoundsR29b.correction_norm_tendsto_zero
