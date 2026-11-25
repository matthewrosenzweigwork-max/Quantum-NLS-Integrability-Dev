import QuantumNLS.Ext025A2Cauchy

/-! GP-05: weak scalar integration of covectors and recovery of norm-convergent
series of averaged covectors. No operator-norm Bochner measurability of the
covector family is assumed. Full Banach polarization is separately open. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Metric
namespace QuantumNLS.Ext025A2
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- Scalar evaluation integration defines a bounded covector. -/
def gp05_weak_average (φ : X → E →L[ℂ] ℂ) {M : ℝ}
    (hs : ∀ v : E, Integrable (fun x => φ x v) μ)
    (hb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ M) : E →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun v => ∫ x, φ x v ∂μ
      map_add' := fun v w => by
        simp only [map_add]
        exact integral_add (hs v) (hs w)
      map_smul' := fun c v => by simp only [map_smul, integral_smul, RingHom.id_apply] }
    M (fun v => by
      have h : ∀ᵐ x ∂μ, ‖φ x v‖ ≤ M * ‖v‖ := hb.mono fun x hx =>
        (φ x).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg v))
      simpa using norm_integral_le_of_norm_le_const h)

/-- The averaged covector retains the uniform operator-norm bound. -/
theorem gp05_weak_average_norm (φ : X → E →L[ℂ] ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hs : ∀ v : E, Integrable (fun x => φ x v) μ)
    (hb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ M) : ‖gp05_weak_average φ hs hb‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro v
  have h : ∀ᵐ x ∂μ, ‖φ x v‖ ≤ M * ‖v‖ := hb.mono fun x hx =>
    (φ x).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg v))
  simpa [gp05_weak_average] using norm_integral_le_of_norm_le_const h

/-- Summable uniform coefficient bounds recover a norm-convergent dual series.
Scalar evaluations of its sum are exactly the scalar integrals of the original
coefficient sums. This applies coefficient by coefficient to Haar averaging. -/
theorem gp05_weak_average_normal_series {φ : ℕ → X → E →L[ℂ] ℂ} {b : ℕ → ℝ}
    (hb0 : ∀ n, 0 ≤ b n) (hb : Summable b)
    (hs : ∀ n (v : E), Integrable (fun x => φ n x v) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖φ n x‖ ≤ b n) :
    Summable (fun n => gp05_weak_average (φ n) (hs n) (hbound n)) ∧
      ∀ v : E, (∑' n, gp05_weak_average (φ n) (hs n) (hbound n)) v =
        ∫ x, ∑' n, φ n x v ∂μ := by
  have hsum : Summable (fun n => gp05_weak_average (φ n) (hs n) (hbound n)) :=
    hb.of_norm_bounded (fun n => gp05_weak_average_norm (φ n) (hb0 n) (hs n) (hbound n))
  refine ⟨hsum, fun v => ?_⟩
  rw [tsum_apply hsum]
  change (∑' n, ∫ x, φ n x v ∂μ) = ∫ x, ∑' n, φ n x v ∂μ
  apply integral_tsum_of_summable_integral_norm (fun n => hs n v)
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
    (fun n => ?_) (hb.mul_right ‖v‖)
  calc
    ∫ x, ‖φ n x v‖ ∂μ ≤ ∫ _, b n * ‖v‖ ∂μ := by
      apply integral_mono_ae (hs n v).norm (integrable_const _)
      exact (hbound n).mono fun x hx =>
        (φ n x).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg v))
    _ = b n * ‖v‖ := by simp

section Lines
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A common Banach ball gives the stated fixed-order estimates on every
complex line in a unit direction, in the full Banach target norm. -/
theorem gp05_banach_line_bounds {f : E → F} {U : Set E} {a : E} {r M : ℝ}
    (hf : DifferentiableOn ℂ f U) (hr : 0 < r) (hball : closedBall a r ⊆ U)
    (hM : ∀ x ∈ closedBall a r, ‖f x‖ ≤ M) (v : E) (hv : ‖v‖ ≤ 1) (n : ℕ) :
    ‖iteratedDeriv n (fun z : ℂ => f (a + z • v)) 0‖ ≤ n.factorial * M / r ^ n := by
  have hmap : MapsTo (fun z : ℂ => a + z • v) (closedBall 0 r) (closedBall a r) := by
    intro z hz
    rw [mem_closedBall_iff_norm] at hz ⊢
    simp only [sub_zero] at hz
    simpa only [add_sub_cancel_left, norm_smul] using
      (mul_le_mul_of_nonneg_left hv (norm_nonneg z)).trans (by simpa using hz)
  have hdline : Differentiable ℂ (fun z : ℂ => a + z • v) := by fun_prop
  have hd : DifferentiableOn ℂ (fun z : ℂ => f (a + z • v)) (closedBall 0 r) :=
    hf.comp hdline.differentiableOn
      (fun z hz => hball (hmap hz))
  apply gp05_cauchy_all_orders hd hr (Subset.refl _) _ n
  intro z hz
  exact hM _ (hmap (sphere_subset_closedBall hz))
end Lines
end QuantumNLS.Ext025A2
#print axioms QuantumNLS.Ext025A2.gp05_weak_average
#print axioms QuantumNLS.Ext025A2.gp05_weak_average_norm
#print axioms QuantumNLS.Ext025A2.gp05_weak_average_normal_series
#print axioms QuantumNLS.Ext025A2.gp05_banach_line_bounds
