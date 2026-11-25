import Mathlib

/-! Real calculus used to remove the window. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Metric Filter Topology
namespace QuantumNLS.Q07RealCalculusR24
section Comp
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem linear_twice (A : E →L[ℝ] F) (P : G →L[ℝ] H)
    {f : F → G} {U : Set F} (hU : IsOpen U) {x : E} (hx : A x ∈ U)
    (hf : ∀ y ∈ U, DifferentiableAt ℝ f y)
    (h2 : DifferentiableAt ℝ (fderiv ℝ f) (A x)) :
    DifferentiableAt ℝ (fun y => P (f (A y))) x ∧
    DifferentiableAt ℝ (fderiv ℝ (fun y => P (f (A y)))) x ∧
    ∀ v w : E,
      fderiv ℝ (fderiv ℝ (fun y => P (f (A y)))) x v w =
        P (fderiv ℝ (fderiv ℝ f) (A x) (A v) (A w)) := by
  let T : (F →L[ℝ] G) →L[ℝ] (E →L[ℝ] H) :=
    ((ContinuousLinearMap.compL ℝ E F H).flip A).comp (ContinuousLinearMap.compL ℝ F G H P)
  have hD := T.hasFDerivAt.comp x (h2.hasFDerivAt.comp x A.hasFDerivAt)
  have he : fderiv ℝ (fun y => P (f (A y))) =ᶠ[𝓝 x]
      (fun y => T (fderiv ℝ f (A y))) := by
    filter_upwards [A.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)] with y hy
    exact (P.hasFDerivAt.comp y ((hf (A y) hy).hasFDerivAt.comp y A.hasFDerivAt)).fderiv
  have hDD := hD.congr_of_eventuallyEq he
  refine ⟨(P.differentiableAt.comp x ((hf (A x) hx).comp x A.differentiableAt)),
    hDD.differentiableAt,?_⟩
  intro v w
  rw [hDD.fderiv]
  rfl
end Comp

/-- A value bound and a second derivative bound on the entire real segment
control the actual first derivative. -/
theorem finite_difference {g d : ℝ → ℝ} {A H ε : ℝ} (hε : 0 < ε)
    (_hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg : ∀ t ∈ Icc 0 ε, HasDerivAt g (d t) t)
    (hd : ∀ t ∈ Icc 0 ε, DifferentiableAt ℝ d t)
    (hdd : ∀ t ∈ Icc 0 ε, |deriv d t| ≤ H)
    (hv0 : |g 0| ≤ A) (hvε : |g ε| ≤ A) :
    |d 0| ≤ 2*A/ε + H*ε := by
  have hdif : ∀ t ∈ Icc 0 ε, |d t-d 0| ≤ H*ε := by
    intro t ht
    have hb := (convex_Icc (0 : ℝ) ε).norm_image_sub_le_of_norm_deriv_le
      hd (fun t ht => by simpa only [Real.norm_eq_abs] using hdd t ht)
      (left_mem_Icc.mpr hε.le) ht
    rw [Real.norm_eq_abs,Real.norm_eq_abs,sub_zero,abs_of_nonneg ht.1] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left ht.2 hH)
  let q : ℝ → ℝ := fun t => g t-t*d 0
  have hq : ∀ t ∈ Icc 0 ε, HasDerivAt q (d t-d 0) t := by
    intro t ht
    convert (hg t ht).sub ((hasDerivAt_id t).const_smul (d 0)) using 1
    · funext y
      change g y-y*d 0 = g y-d 0*y
      ring
    · simp
  have hrem : |q ε-q 0| ≤ (H*ε)*ε := by
    have hm := (convex_Icc (0 : ℝ) ε).norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (hq t ht).differentiableAt)
      (fun t ht => by simpa only [(hq t ht).deriv,Real.norm_eq_abs] using hdif t ht)
      (left_mem_Icc.mpr hε.le) (right_mem_Icc.mpr hε.le)
    simpa only [Real.norm_eq_abs,sub_zero,abs_of_pos hε] using hm
  have ht : |ε*d 0| ≤ 2*A+H*ε^2 := by
    have hx : ε*d 0 = g ε-g 0-(q ε-q 0) := by dsimp [q]; ring
    rw [hx]
    have hb := abs_sub (g ε-g 0) (q ε-q 0)
    have hb2 := abs_sub (g ε) (g 0)
    nlinarith
  rw [abs_mul,abs_of_pos hε] at ht
  apply (mul_le_mul_iff_of_pos_right hε).mp
  calc |d 0| * ε = ε*|d 0| := mul_comm _ _
    _ ≤ 2*A+H*ε^2 := ht
    _ = (2*A/ε+H*ε)*ε := by field_simp
section Bound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem derivative_bound {f : E → ℝ} {B A H ε : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hf : ∀ x : E, ‖x‖ < B+2 → DifferentiableAt ℝ f x)
    (hf2 : ∀ x : E, ‖x‖ < B+2 → DifferentiableAt ℝ (fderiv ℝ f) x)
    (hh : ∀ x : E, ‖x‖ < B+2 → ∀ v w : E,
      |fderiv ℝ (fderiv ℝ f) x v w| ≤ H*‖v‖*‖w‖)
    (hv : ∀ x : E, ‖x‖ ≤ B+1 → |f x| ≤ A)
    (u : E) (hu : ‖u‖ ≤ B) :
    ‖fderiv ℝ f u‖ ≤ 2*A/ε+H*ε := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hnv
  let z : ℝ → E := fun t => u+t • v
  have hz : ∀ t ∈ Icc 0 ε, ‖z t‖ ≤ B+1 := by
    intro t ht
    have hb := norm_add_le u (t • v)
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1,hnv,mul_one] at hb
    dsimp [z]
    linarith [ht.2]
  have hzd : ∀ t : ℝ, HasDerivAt z v t := by
    intro t
    simpa [z] using ((hasDerivAt_id t).smul_const v).const_add u
  let g : ℝ → ℝ := fun t => f (z t)
  let d : ℝ → ℝ := fun t => fderiv ℝ f (z t) v
  have hg : ∀ t ∈ Icc 0 ε, HasDerivAt g (d t) t := by
    intro t ht
    exact (hf (z t) (by linarith [hz t ht])).hasFDerivAt.comp_hasDerivAt t (hzd t)
  have hd : ∀ t ∈ Icc 0 ε,
      HasDerivAt d (fderiv ℝ (fderiv ℝ f) (z t) v v) t := by
    intro t ht
    have h := ((hf2 (z t) (by linarith [hz t ht])).hasFDerivAt.comp_hasDerivAt t
      (hzd t)).clm_apply (hasDerivAt_const t v)
    simpa [d] using h
  have hb : |d 0| ≤ 2*A/ε+H*ε := finite_difference hε hA hH hg
    (fun t ht => (hd t ht).differentiableAt)
    (fun t ht => by rw [(hd t ht).deriv]; simpa [hnv] using hh (z t) (by linarith [hz t ht]) v v)
    (hv (z 0) (hz 0 (left_mem_Icc.mpr hε.le)))
    (hv (z ε) (hz ε (right_mem_Icc.mpr hε.le)))
  simpa [d,z,Real.norm_eq_abs] using hb
end Bound
end QuantumNLS.Q07RealCalculusR24
