import Mathlib
import QuantumNLS.Local007Lift

/-! LOCAL-007 stage P: generic analysis for the `ℓ∞` family `r_n(u) = R(T_n u)`.

* `analytic_even_bounds`: a real-analytic function `R` with `R 0 = 1`, even near `0`, satisfies
  `|R v - 1| ≤ C‖v‖²`, `‖R'(v)‖ ≤ C‖v‖`, `|R v - 1| < 1/2` on a ball (analytic ⇒ `C²`, `R'(0) = 0`);
* `lp_lift`: for norm-nonincreasing linear maps `T_n`, `u ↦ (n ↦ R(T_n u)) ∈ ℓ∞(ℤ)` is real analytic on a ball
  (pointwise lift of the power series of `R`, `Local007Lift`);
* `lp_deriv`: its derivative acts coordinatewise: `(r'(u) h)_n = R'(T_n u)(T_n h)`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open BoundedContinuousFunction Metric Filter Topology Set
open scoped ENNReal NNReal
namespace QuantumNLS.Local007Lp
open QuantumNLS.Local007Lift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analytic_even_bounds {R : E → ℝ} (hR : AnalyticAt ℝ R 0) (h0 : R 0 = 1)
    (heven : ∀ᶠ v in 𝓝 (0 : E), R (-v) = R v) :
    ∃ ρ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ ball (0 : E) ρ,
      DifferentiableAt ℝ R v ∧ |R v - 1| ≤ C * ‖v‖ ^ 2 ∧ ‖fderiv ℝ R v‖ ≤ C * ‖v‖ ∧ |R v - 1| < 1 / 2 := by
  -- analytic on a ball
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.eventually_nhds_iff_ball.1 hR.eventually_analyticAt
  have hcd : ∀ x ∈ ball (0 : E) ρ0, ContDiffAt ℝ 2 R x := fun x hx => (hball x hx).contDiffAt
  have hd : ∀ x ∈ ball (0 : E) ρ0, DifferentiableAt ℝ R x := fun x hx =>
    (hcd x hx).differentiableAt (by norm_num)
  have hdd : ∀ x ∈ ball (0 : E) ρ0, DifferentiableAt ℝ (fderiv ℝ R) x := fun x hx => by
    have := (hcd x hx).fderiv_right (m := 1) (by norm_num)
    exact this.differentiableAt (by norm_num)
  -- continuity of the second derivative at 0
  have hc2 : ContinuousAt (fderiv ℝ (fderiv ℝ R)) 0 := by
    have := (hcd 0 (mem_ball_self hρ0)).fderiv_right (m := 1) (by norm_num)
    exact (this.fderiv_right (m := 0) (by norm_num)).continuousAt
  have hnorm : ContinuousAt (fun x => ‖fderiv ℝ (fderiv ℝ R) x‖) 0 := by
    have := continuous_norm.continuousAt.comp (f := fderiv ℝ (fderiv ℝ R)) (x := (0 : E)) hc2
    exact this
  have hev1 : ∀ᶠ x in 𝓝 (0 : E), ‖fderiv ℝ (fderiv ℝ R) x‖ < ‖fderiv ℝ (fderiv ℝ R) 0‖ + 1 :=
    hnorm.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨ρ1, hρ1, hb1⟩ := Metric.eventually_nhds_iff_ball.1 hev1
  set M : ℝ := ‖fderiv ℝ (fderiv ℝ R) 0‖ + 1 with hM
  have hM0 : 0 < M := by positivity
  have hbd : ∀ x ∈ ball (0 : E) (min ρ0 ρ1), ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ M := fun x hx =>
    (hb1 x (ball_subset_ball (min_le_right _ _) hx)).le
  -- R'(0) = 0
  have hD0 : fderiv ℝ R 0 = 0 := by
    have hneg : fderiv ℝ (fun v => R (-v)) 0 = fderiv ℝ R 0 :=
      Filter.EventuallyEq.fderiv_eq (f₁ := fun v => R (-v)) (f := R) heven
    have hcomp : fderiv ℝ (fun v => R (-v)) 0 = -fderiv ℝ R 0 := by
      have hm0 : (-(0 : E)) ∈ ball (0 : E) ρ0 := by simpa using (mem_ball_self hρ0 : (0 : E) ∈ ball (0 : E) ρ0)
      have h1 : HasFDerivAt R (fderiv ℝ R (-(0 : E))) (-(0 : E)) := (hd _ hm0).hasFDerivAt
      have h2 : HasFDerivAt (fun v : E => R (-v))
          ((fderiv ℝ R (-(0 : E))).comp (-(ContinuousLinearMap.id ℝ E))) 0 :=
        h1.comp (0 : E) (hasFDerivAt_id (0 : E)).neg
      rw [h2.fderiv]
      ext w; simp
    have : fderiv ℝ R 0 = -fderiv ℝ R 0 := by rw [← hcomp, hneg]
    ext w
    have h3 := congrArg (fun T => T w) this
    simp only [ContinuousLinearMap.neg_apply] at h3
    simp only [ContinuousLinearMap.zero_apply]
    linarith
  set ρ2 : ℝ := min ρ0 ρ1 with hρ2
  have hρ2pos : 0 < ρ2 := lt_min hρ0 hρ1
  -- bound on the derivative
  have hDb : ∀ x ∈ ball (0 : E) ρ2, ‖fderiv ℝ R x‖ ≤ M * ‖x‖ := by
    intro x hx
    have hconv : Convex ℝ (ball (0 : E) ρ2) := convex_ball _ _
    have := hconv.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ R) (C := M)
      (fun y hy => hdd y (ball_subset_ball (min_le_left _ _) hy)) (fun y hy => hbd y hy)
      (mem_ball_self hρ2pos) hx
    rw [hD0, sub_zero, sub_zero] at this
    simpa using this
  have hRb : ∀ x ∈ ball (0 : E) ρ2, |R x - 1| ≤ M * ‖x‖ ^ 2 := by
    intro x hx
    have hconv : Convex ℝ (closedBall (0 : E) ‖x‖) := convex_closedBall _ _
    have hsub : closedBall (0 : E) ‖x‖ ⊆ ball (0 : E) ρ2 := by
      intro y hy
      rw [mem_closedBall, dist_zero_right] at hy
      rw [mem_ball, dist_zero_right]
      exact lt_of_le_of_lt hy (by simpa using hx)
    have := hconv.norm_image_sub_le_of_norm_fderiv_le (f := R) (C := M * ‖x‖)
      (fun y hy => hd y (ball_subset_ball (min_le_left _ _) (hsub hy)))
      (fun y hy => by
        refine (hDb y (hsub hy)).trans ?_
        rw [mem_closedBall, dist_zero_right] at hy
        exact mul_le_mul_of_nonneg_left hy hM0.le)
      (show (0 : E) ∈ closedBall (0 : E) ‖x‖ by simp) (show x ∈ closedBall (0 : E) ‖x‖ by simp)
    rw [h0, sub_zero] at this
    rw [Real.norm_eq_abs] at this
    nlinarith [sq_nonneg ‖x‖]
  refine ⟨min ρ2 (1 / (2 * M + 2)), lt_min hρ2pos (by positivity), M, hM0.le, fun v hv => ?_⟩
  have hv2 : v ∈ ball (0 : E) ρ2 := ball_subset_ball (min_le_left _ _) hv
  refine ⟨hd v (ball_subset_ball (min_le_left _ _) hv2), hRb v hv2, hDb v hv2, ?_⟩
  have hvn : ‖v‖ < 1 / (2 * M + 2) := lt_of_lt_of_le (by simpa using hv) (min_le_right _ _)
  have h1 : ‖v‖ < 1 := lt_of_lt_of_le hvn (by rw [div_le_one (by positivity)]; linarith)
  have h2 : M * ‖v‖ ^ 2 ≤ M * ‖v‖ := by
    have : ‖v‖ ^ 2 ≤ ‖v‖ := by nlinarith [norm_nonneg v]
    exact mul_le_mul_of_nonneg_left this hM0.le
  have h3 : M * ‖v‖ < 1 / 2 := by
    have : ‖v‖ * (2 * M + 2) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hvn
    nlinarith [norm_nonneg v]
  exact lt_of_le_of_lt (hRb v hv2) (by linarith)


/-- The coordinate embedding `u ↦ (n ↦ T_n u)` into `ℤ →ᵇ E`. -/
def Tmap (T : ℤ → E →L[ℝ] E) (hT : ∀ n u, ‖T n u‖ ≤ ‖u‖) : E →L[ℝ] (ℤ →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun u => ofNormedAddCommGroupDiscrete (fun n => T n u) ‖u‖ (fun n => hT n u)
      map_add' := fun u w => by ext n; simp
      map_smul' := fun a u => by ext n; simp }
    1 (fun u => by
      refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun n => ?_
      simpa using hT n u)

theorem Tmap_apply (T : ℤ → E →L[ℝ] E) (hT : ∀ n u, ‖T n u‖ ≤ ‖u‖) (u : E) (n : ℤ) :
    Tmap T hT u n = T n u := rfl

theorem norm_Tmap_le (T : ℤ → E →L[ℝ] E) (hT : ∀ n u, ‖T n u‖ ≤ ‖u‖) (u : E) : ‖Tmap T hT u‖ ≤ ‖u‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun n => hT n u

theorem lp_lift (T : ℤ → E →L[ℝ] E) (hT : ∀ n u, ‖T n u‖ ≤ ‖u‖) {R : E → ℝ} (hR : AnalyticAt ℝ R 0) :
    ∃ ρ > 0, ∃ r : E → (ℤ →ᵇ ℝ), AnalyticOnNhd ℝ r (ball (0 : E) ρ) ∧
      ∀ u ∈ ball (0 : E) ρ, ∀ n : ℤ, r u n = R (T n u) := by
  obtain ⟨p, r0, hr0⟩ := hR
  have hl := hasFPowerSeriesOnBall_lift (T := ℤ) hr0
  have hfin : min r0 1 ≠ ⊤ := (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top).ne
  have hlt : ∀ u : E, ‖u‖ < (min r0 1).toReal → ((‖Tmap T hT u‖₊ : ℝ≥0) : ℝ≥0∞) < r0 := by
    intro u hu'
    have h1 : ‖Tmap T hT u‖ < (min r0 1).toReal := lt_of_le_of_lt (norm_Tmap_le T hT u) hu'
    have h3 : ((‖Tmap T hT u‖₊ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ‖Tmap T hT u‖ := by
      rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    rw [h3]
    have h2 : ENNReal.ofReal ‖Tmap T hT u‖ < min r0 1 := by
      rw [← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (norm_nonneg _) h1)).2 h1
    exact lt_of_lt_of_le h2 (min_le_left _ _)
  refine ⟨(min r0 1).toReal, ENNReal.toReal_pos (lt_min hr0.r_pos one_pos).ne' hfin,
    fun u => (liftSeries (T := ℤ) p).sum (Tmap T hT u), ?_, ?_⟩
  · intro u hu
    have hu' : ‖u‖ < (min r0 1).toReal := by simpa using hu
    have hmem : Tmap T hT u ∈ Metric.eball (0 : ℤ →ᵇ E) r0 := by
      rw [Metric.mem_eball, edist_zero_right]
      exact hlt u hu'
    exact (hl.analyticAt_of_mem hmem).comp ((Tmap T hT).analyticAt u)
  · intro u hu n
    have hu' : ‖u‖ < (min r0 1).toReal := by simpa using hu
    have := lift_sum_apply hr0 (Tmap T hT u) (hlt u hu') n
    simpa [Tmap_apply] using this

theorem lp_deriv (T : ℤ → E →L[ℝ] E) (hT : ∀ n u, ‖T n u‖ ≤ ‖u‖) {R : E → ℝ} {ρ : ℝ}
    {r : E → (ℤ →ᵇ ℝ)} (hr : AnalyticOnNhd ℝ r (ball (0 : E) ρ))
    (hrv : ∀ u ∈ ball (0 : E) ρ, ∀ n : ℤ, r u n = R (T n u)) {u : E} (hu : u ∈ ball (0 : E) ρ) (n : ℤ)
    (hRd : DifferentiableAt ℝ R (T n u)) (h : E) :
    (fderiv ℝ r u h) n = fderiv ℝ R (T n u) (T n h) := by
  have hrd : DifferentiableAt ℝ r u := (hr u hu).differentiableAt
  have e1 := (BoundedContinuousFunction.evalCLM ℝ n).hasFDerivAt (x := r u)
  have h1' := e1.comp u hrd.hasFDerivAt
  have h1 : HasFDerivAt (fun w => r w n) ((BoundedContinuousFunction.evalCLM ℝ n).comp (fderiv ℝ r u)) u := h1'
  have h2 : HasFDerivAt (fun w => R (T n w)) ((fderiv ℝ R (T n u)).comp (T n)) u :=
    hRd.hasFDerivAt.comp u (T n).hasFDerivAt
  have h3 : (fun w => r w n) =ᶠ[𝓝 u] fun w => R (T n w) := by
    filter_upwards [isOpen_ball.mem_nhds hu] with w hw using hrv w hw n
  have := h1.unique (h2.congr_of_eventuallyEq h3)
  have := congrArg (fun A => A h) this
  simpa using this

end QuantumNLS.Local007Lp
#print axioms QuantumNLS.Local007Lp.analytic_even_bounds
#print axioms QuantumNLS.Local007Lp.lp_lift
#print axioms QuantumNLS.Local007Lp.lp_deriv
