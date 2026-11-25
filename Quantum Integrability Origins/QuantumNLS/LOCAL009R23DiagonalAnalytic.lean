import QuantumNLS.LOCAL009R22Assembly
import Mathlib.Analysis.Complex.Liouville

/-! Operator-norm holomorphy from a uniformly bounded analytic complete-basis
family. No norm differentiability hypothesis is imposed on the lifted family. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
noncomputable section
open Complex Set Metric Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.LOCAL009R23DiagonalAnalytic
open QuantumNLS.LOCAL009R22Assembly QuantumNLS.LOCAL009R22OperatorSupport

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def diagonal (b : HilbertBasis ι ℂ H) (a : ι → ℂ) : H →L[ℂ] H := by
  classical
  exact if h : ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖a i‖ ≤ C then
    (QuantumNLS.HilbertDiagOp.diag_exists b a h.choose h.choose_spec.2 h.choose_spec.1).choose
  else 0

theorem diagonal_eigen (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) (i : ι) :
    diagonal b a (b i) = a i • b i := by
  have h : ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖a i‖ ≤ C := ⟨C,hC,ha⟩
  rw [diagonal, dite_eq_left h]
  exact eigen_of_coeff b _ a
    (QuantumNLS.HilbertDiagOp.diag_exists b a h.choose h.choose_spec.2 h.choose_spec.1).choose_spec.1 i

theorem norm_le_of_eigen (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H)
    (a : ι → ℂ) (ha : ∀ i, A (b i) = a i • b i)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ i, ‖a i‖ ≤ C) : ‖A‖ ≤ C := by
  have h := diagonal_error_norm b A 0 a (fun _ => 0) ha (by simp) hC
    (by simpa using hbound)
  simpa using h

/-- Uniform quadratic remainder on an inner disk, from Cauchy's estimate. -/
theorem uniform_remainder {f : ℂ → ℂ} {z : ℂ} {r C : ℝ}
    (hr : 0 < r) (hf : ∀ w ∈ closedBall z (2*r), AnalyticAt ℂ f w)
    (hC : ∀ w ∈ closedBall z (2*r), ‖f w‖ ≤ C)
    {w : ℂ} (hw : w ∈ ball z r) :
    ‖f w - f z - (w-z)*deriv f z‖ ≤ (2*C/r^2)*‖w-z‖^2 := by
  have hsub {v : ℂ} (hv : v ∈ closedBall z r) : closedBall v r ⊆ closedBall z (2*r) := by
    intro u hu
    exact mem_closedBall.mpr ((dist_triangle u v z).trans (by
      have := mem_closedBall.mp hu
      have := mem_closedBall.mp hv
      linarith))
  have hsecond (v : ℂ) (hv : v ∈ closedBall z r) :
      ‖deriv (deriv f) v‖ ≤ 2*C/r^2 := by
    have hdiff : DiffContOnCl ℂ f (ball v r) :=
      DifferentiableOn.diffContOnCl_ball
        (fun u hu => (hf u hu).differentiableAt.differentiableWithinAt) (hsub hv)
    have hb := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hr hdiff
      (fun u hu => hC u (hsub hv (sphere_subset_closedBall hu)))
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using hb
  have hderiv (v : ℂ) (hv : v ∈ closedBall z r) :
      ‖deriv f v - deriv f z‖ ≤ (2*C/r^2)*‖v-z‖ := by
    exact (convex_closedBall z r).norm_image_sub_le_of_norm_deriv_le
      (fun u hu => (hf u (closedBall_subset_closedBall (by linarith) hu)).deriv.differentiableAt)
      hsecond (mem_closedBall_self hr.le) hv
  let s := closedBall z ‖w-z‖
  have hs : s ⊆ closedBall z r := closedBall_subset_closedBall (by
    exact (show ‖w-z‖ < r by simpa [mem_ball, dist_eq_norm] using hw).le)
  have hz : z ∈ s := mem_closedBall_self (norm_nonneg _)
  have hws : w ∈ s := by simp [s, mem_closedBall, dist_eq_norm]
  have hrem (v : ℂ) (hv : v ∈ s) :
      HasDerivAt (fun u => f u - f z - (u-z)*deriv f z) (deriv f v - deriv f z) v := by
    convert (((hf v (closedBall_subset_closedBall (by linarith) (hs hv))).differentiableAt.hasDerivAt).sub_const (f z)).sub
      (((hasDerivAt_id v).sub_const z).mul_const (deriv f z)) using 1 <;> first | (ext u; rfl) | simp
  have hb (v : ℂ) (hv : v ∈ s) : ‖deriv f v - deriv f z‖ ≤ (2*C/r^2)*‖w-z‖ := by
    apply (hderiv v (hs hv)).trans
    apply mul_le_mul_of_nonneg_left
    · simpa [s, mem_closedBall, dist_eq_norm] using hv
    · have hc0 := (norm_nonneg (f z)).trans (hC z (mem_closedBall_self (by positivity)))
      positivity
  have h := (convex_closedBall z ‖w-z‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => (hrem v hv).hasDerivWithinAt) hb hz hws
  simpa [sub_self, zero_mul, sub_zero, pow_two, mul_assoc] using h

/-- A bounded analytic scalar family lifts to an operator-norm derivative,
with the derivative of the entire scalar function on every basis vector. -/
theorem analytic_lift (b : HilbertBasis ι ℂ H) (F : ℂ → H →L[ℂ] H)
    (f : ι → ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U) {C : ℝ} (hC : 0 ≤ C)
    (he : ∀ z ∈ U, ∀ i, F z (b i) = f i z • b i)
    (hf : ∀ i z, z ∈ U → AnalyticAt ℂ (f i) z)
    (hb : ∀ i z, z ∈ U → ‖f i z‖ ≤ C) {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℂ F z ∧
      ∀ i, deriv F z (b i) = deriv (f i) z • b i := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let r := δ/3
  have hr : 0 < r := by dsimp [r]; positivity
  have hclosed : closedBall z (2*r) ⊆ U := by
    apply Subset.trans (closedBall_subset_ball (by dsimp [r]; linarith)) hball
  have hd (i : ι) : ‖deriv (f i) z‖ ≤ C/r := by
    apply norm_deriv_le_of_forall_mem_sphere_norm_le hr
    · exact DifferentiableOn.diffContOnCl_ball
        (fun v hv => (hf i v (hclosed hv)).differentiableAt.differentiableWithinAt)
        (closedBall_subset_closedBall (by linarith))
    · intro v hv
      exact hb i v (hclosed (closedBall_subset_closedBall (by linarith) (sphere_subset_closedBall hv)))
  let D := diagonal b (fun i => deriv (f i) z)
  have hD := diagonal_eigen b (fun i => deriv (f i) z) (by positivity : 0 ≤ C/r) hd
  have hbound : ∀ᶠ w in 𝓝 z,
      ‖F w - F z - (w-z) • D‖ ≤ (2*C/r^2)*‖w-z‖^2 := by
    filter_upwards [Metric.ball_mem_nhds z hr] with w hw
    apply norm_le_of_eigen b _ (fun i => f i w - f i z - (w-z)*deriv (f i) z)
    · intro i
      change F w (b i) - F z (b i) - (w-z) • D (b i) = _
      rw [he w (hclosed (ball_subset_closedBall (ball_subset_ball (by linarith) hw))) i,
        he z hz i, show D (b i) = _ from hD i]
      simp only [smul_smul, sub_smul]
      /-
        he w (hclosed (ball_subset_closedBall (ball_subset_ball (by linarith) hw))) i,
        he z hz i, hD, smul_smul, sub_smul] -/
    · positivity
    · intro i
      exact uniform_remainder hr (fun v hv => hf i v (hclosed hv))
        (fun v hv => hb i v (hclosed hv)) hw
  have hbig : (fun w => F w-F z-(w-z) • D) =O[𝓝 z] (fun w => ‖w-z‖^2) :=
    Asymptotics.IsBigO.of_bound (2*C/r^2) (by simpa only [norm_pow, norm_norm] using hbound)
  have hlittle := hbig.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub z (by decide : 1 < 2))
  have hder : HasDerivAt F D z := HasDerivAt.of_isLittleO hlittle
  exact ⟨hder.differentiableAt, fun i => by rw [hder.deriv]; exact hD i⟩

end QuantumNLS.LOCAL009R23DiagonalAnalytic
