import QuantumNLS.Ext025A8HartreeBounds
import QuantumNLS.Ext025A8RankMargin
import QuantumNLS.Ext025A8Picard

/-! PROP-001: construct the actual vector series and a common local
Picard time from the exponential rank sum. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators InnerProductSpace NNReal
namespace QuantumNLS.Ext025A8
open TensorCarrier
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

def hartreeField (A : ∀ n : ℕ,
    HilbertTensorPower ℂ H (n + 1) →L[ℂ] HilbertTensorPower ℂ H (n + 1)) (u : H) : H :=
  (-Complex.I) • ∑' n, hartreeTerm A n u

theorem hartreeField_ball_bounds (A : ∀ n : ℕ,
    HilbertTensorPower ℂ H (n + 1) →L[ℂ] HilbertTensorPower ℂ H (n + 1))
    {S : ℝ} (hS : 0 ≤ S)
    (hv : Summable (fun n => (n + 1 : ℕ) * ‖A n‖ * S ^ (2 * n + 1)))
    (hd : Summable (fun n => (n + 1 : ℕ) * (2 * n + 1 : ℕ) * ‖A n‖ * S ^ (2 * n))) :
    ∃ M K : ℝ≥0, (∀ u ∈ closedBall (0 : H) S, ‖hartreeField A u‖ ≤ M) ∧
      LipschitzOnWith K (hartreeField A) (closedBall (0 : H) S) := by
  let M : ℝ≥0 := NNReal.mk (∑' n, (n + 1 : ℕ) * ‖A n‖ * S ^ (2 * n + 1))
    (tsum_nonneg (fun _ => by positivity))
  let K : ℝ≥0 := NNReal.mk (∑' n, (n + 1 : ℕ) * (2 * n + 1 : ℕ) * ‖A n‖ * S ^ (2 * n))
    (tsum_nonneg (fun _ => by positivity))
  refine ⟨M, K, ?_, ?_⟩
  · intro u hu
    have hu' := mem_closedBall_zero_iff.mp hu
    have hb (n : ℕ) : ‖hartreeTerm A n u‖ ≤
        (n + 1 : ℕ) * ‖A n‖ * S ^ (2 * n + 1) :=
      (hartreeTerm_norm A n u).trans (by gcongr)
    simpa only [hartreeField, norm_smul, norm_neg, Complex.norm_I, one_mul, M, NNReal.coe_mk]
      using tsum_of_norm_bounded hv.hasSum hb
  · apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv'
    have hu' := mem_closedBall_zero_iff.mp hu
    have hv'' := mem_closedBall_zero_iff.mp hv'
    have hsu := hartree_series_summable A hS hv hu'
    have hsv := hartree_series_summable A hS hv hv''
    have hb := tsum_of_norm_bounded (hd.mul_right ‖u - v‖).hasSum
      (fun n => hartreeTerm_lipschitz A n hS hu' hv'')
    rw [tsum_mul_right] at hb
    simpa only [hartreeField, dist_eq_norm, ← smul_sub, norm_smul, norm_neg,
      Complex.norm_I, one_mul, ← hsu.tsum_sub hsv, K, NNReal.coe_mk] using hb

/-- Selfadjoint kernels give the actual mass orthogonality of the
summed field, after norm convergence has been proved. -/
theorem hartreeField_orthogonal (A : ∀ n : ℕ,
    HilbertTensorPower ℂ H (n + 1) →L[ℂ] HilbertTensorPower ℂ H (n + 1))
    (hA : ∀ n, IsSelfAdjoint (A n)) {u : H}
    (hs : Summable (fun n => hartreeTerm A n u)) :
    (⟪u, hartreeField A u⟫_ℂ).re = 0 := by
  have hr (n : ℕ) : (⟪u, hartreeTerm A n u⟫_ℂ).im = 0 := by
    have hsym : ⟪hartreeContraction (A n) u u, u⟫_ℂ =
        ⟪u, hartreeContraction (A n) u u⟫_ℂ :=
      (hartreeContraction_selfAdjoint (A n) (hA n) u).isSymmetric u u
    have him := inner_im_symm (𝕜 := ℂ) u (hartreeContraction (A n) u u)
    simp only [RCLike.im_to_complex] at him
    have hsi := congrArg Complex.im hsym
    have hz : (⟪u, hartreeContraction (A n) u u⟫_ℂ).im = 0 := by linarith
    simp only [hartreeTerm, inner_smul_right, Complex.mul_im,
      Complex.natCast_re, Complex.natCast_im, hz, mul_zero, zero_mul, add_zero]
  have hi := (innerSL ℂ u).hasSum hs.hasSum
  have hz : (⟪u, ∑' n, hartreeTerm A n u⟫_ℂ).im = 0 := by
    have hh := Complex.hasSum_im hi
    simp only [innerSL_apply_apply, hr] at hh
    exact hh.unique (hasSum_zero)
  simp [hartreeField, inner_smul_right, Complex.mul_re, hz]

/-- Source exponential summability, rather than a supplied differentiable
Hartree map, gives a larger common ball and a positive Picard time for every
unit initial point. No compactness of the unit sphere is used. -/
theorem prop001_local_application (A : ∀ n : ℕ,
    HilbertTensorPower ℂ H (n + 1) →L[ℂ] HilbertTensorPower ℂ H (n + 1))
    {a : ℝ} (ha : 0 < a)
    (hs : Summable (fun n => (n + 1 : ℕ) * ‖A n‖ * Real.exp (a * n))) :
    ∃ S > (1 : ℝ), ∃ δ > (0 : ℝ), ∀ u : H, ‖u‖ ≤ 1 → ∀ b : ℝ,
      ∃ α : ℝ → H, Continuous α ∧ α b = u ∧
        (∀ t, α t ∈ closedBall (0 : H) S) ∧
        (∀ t ∈ Ioo (b - δ) (b + δ), HasDerivAt α (hartreeField A (α t)) t) := by
  obtain ⟨S, hS, hv, hd⟩ := exponential_rank_margin ha (fun n => norm_nonneg (A n)) hs
  obtain ⟨M, K, hM, hK⟩ := hartreeField_ball_bounds A ((zero_lt_one.trans hS).le) hv hd
  obtain ⟨δ, hδ, hsol⟩ := bounded_ball_picard hS hM hK
  exact ⟨S, hS, δ, hδ, hsol⟩
end QuantumNLS.Ext025A8

#print axioms QuantumNLS.Ext025A8.hartreeField
#print axioms QuantumNLS.Ext025A8.hartreeField_ball_bounds
#print axioms QuantumNLS.Ext025A8.hartreeField_orthogonal
#print axioms QuantumNLS.Ext025A8.prop001_local_application
