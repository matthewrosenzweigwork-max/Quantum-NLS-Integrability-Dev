import Mathlib
import QuantumNLS.RB01LinfLift

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-19: holomorphic dependence of parametric contour integrals
on a Banach-space parameter.  Generic, unconditional.

Source `collective_actions.tex:405-411`: the moments, `H_n`, `D_n`, `r_n` are "uniform bounded holomorphic-family
assertions ... They follow directly from the uniform contour bounds and the Banach-valued Cauchy formula".  Here the
Banach-valued contour integral is realized without Bochner integration of `ℓ∞`-valued maps:
* `contSub`: the continuous elements of `ℓ∞(ℝ)`; `intCLM a b`: `g ↦ ∫_a^b g`, bounded by `|b − a|` on it; by
  Hahn–Banach (`exists_extension_norm_eq`) it extends to a bounded functional on all of `ℓ∞(ℝ)`;
* **`analyticOnNhd_integral`**: if `F : E → ℝ → ℂ` is complex analytic in `x ∈ U` (open) for each `θ ∈ [a, b]`,
  continuous in `θ ∈ [a, b]` for each `x ∈ U`, and locally uniformly bounded, then `x ↦ ∫_a^b F(x, θ) dθ` is complex
  analytic on `U` (the family `θ ↦ F(·, θ)` is one bounded analytic `ℓ∞(ℝ)`-valued map by
  `RB01LinfLift.linf_lift`; the integral is the Hahn–Banach extension applied to it);
* **`analyticOnNhd_circleIntegral`**: the same for `x ↦ ∮_{|w−c|=R} f(x, w) dw`;
* `norm_circleIntegral_le`: `‖(2πi)⁻¹ ∮_{|w-c|=R} f‖ ≤ R · C` for `‖f‖ ≤ C` on the circle. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal Interval

namespace QuantumNLS.RB01ParamInt

open QuantumNLS.RB01LinfLift (Linf linf_lift)

/-- The continuous elements of `ℓ∞(ℝ)`. -/
def contSub : Submodule ℂ (Linf ℝ) where
  carrier := {g | Continuous (fun θ : ℝ => (g θ : ℂ))}
  add_mem' := by
    intro f g hf hg
    simp only [mem_ofPred_eq, lp.coeFn_add, Pi.add_apply] at hf hg ⊢
    exact hf.add hg
  zero_mem' := by
    simp only [mem_ofPred_eq, lp.coeFn_zero, Pi.zero_apply]
    exact continuous_const
  smul_mem' := by
    intro c f hf
    simp only [mem_ofPred_eq, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hf ⊢
    exact continuous_const.mul hf

theorem norm_apply_le (g : Linf ℝ) (θ : ℝ) : ‖(g θ : ℂ)‖ ≤ ‖g‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero g θ

/-- Integration over `[a, b]` on continuous elements, as a linear functional. -/
def intFun (a b : ℝ) : contSub →ₗ[ℂ] ℂ where
  toFun g := ∫ θ in a..b, (g.1 θ : ℂ)
  map_add' f g := by
    simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
    exact intervalIntegral.integral_add (f.2.intervalIntegrable _ _) (g.2.intervalIntegrable _ _)
  map_smul' c f := by
    simp only [Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact intervalIntegral.integral_const_mul c _

theorem norm_intFun_le (a b : ℝ) (g : contSub) : ‖intFun a b g‖ ≤ |b - a| * ‖g‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := ‖g‖)
    (f := fun θ => (g.1 θ : ℂ)) (fun θ _ => norm_apply_le g.1 θ)
  change ‖∫ θ in a..b, (g.1 θ : ℂ)‖ ≤ _
  rw [mul_comm]
  exact h

/-- Integration over `[a, b]` as a bounded functional on the continuous elements of `ℓ∞(ℝ)`. -/
def intCLM (a b : ℝ) : StrongDual ℂ contSub := (intFun a b).mkContinuous |b - a| (norm_intFun_le a b)

theorem intCLM_apply (a b : ℝ) (g : contSub) : intCLM a b g = ∫ θ in a..b, (g.1 θ : ℂ) := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- **Holomorphic dependence of a parametric integral** on a Banach-space parameter. -/
theorem analyticOnNhd_integral {U : Set E} {F : E → ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (han : ∀ θ ∈ Icc a b, AnalyticOnNhd ℂ (fun x => F x θ) U)
    (hcont : ∀ x ∈ U, ContinuousOn (F x) (Icc a b))
    (hbd : ∀ x ∈ U, ∃ r > 0, ∃ M : ℝ, ball x r ⊆ U ∧ ∀ y ∈ ball x r, ∀ θ ∈ Icc a b, ‖F y θ‖ ≤ M) :
    AnalyticOnNhd ℂ (fun x => ∫ θ in a..b, F x θ) U := by
  intro x hx
  obtain ⟨r, hr, M, hsub, hM⟩ := hbd x hx
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_ball_self hr) a (left_mem_Icc.2 hab))
  set P : ℝ → ℝ := fun θ => (projIcc a b hab θ : ℝ) with hP
  have hPmem : ∀ θ, P θ ∈ Icc a b := fun θ => (projIcc a b hab θ).2
  have hPc : Continuous P := continuous_subtype_val.comp continuous_projIcc
  obtain ⟨G, hG, -, -, hGan⟩ := linf_lift (I := ℝ) (Φ := fun θ y => F y (P θ)) (x₀ := x) hr hM0
    (fun θ => (han (P θ) (hPmem θ)).mono hsub) (fun θ y hy => hM y hy (P θ) (hPmem θ))
  obtain ⟨T, hT, -⟩ := exists_extension_norm_eq contSub (intCLM a b)
  have hr' : 0 < r / Real.exp 1 := by positivity
  have hball : ball x (r / Real.exp 1) ⊆ ball x r :=
    ball_subset_ball (div_le_self hr.le (Real.one_le_exp zero_le_one))
  have heq : (fun y => T (G y)) =ᶠ[𝓝 x] fun y => ∫ θ in a..b, F y θ := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr')] with y hy
    have hyr := hball hy
    have hc : Continuous fun θ : ℝ => (G y θ : ℂ) := by
      have : (fun θ : ℝ => (G y θ : ℂ)) = fun θ => F y (P θ) := funext fun θ => hG y hyr θ
      rw [this]
      exact (hcont y (hsub hyr)).comp_continuous hPc hPmem
    have hmem : G y ∈ contSub := hc
    have := hT ⟨G y, hmem⟩
    simp only at this
    rw [this, intCLM_apply]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le hab] at hθ
    change (G y θ : ℂ) = F y θ
    rw [hG y hyr θ, hP]
    simp only [projIcc_of_mem hab hθ]
  exact ((T.analyticAt _).comp (hGan x (mem_ball_self hr'))).congr heq

/-- **Holomorphic dependence of a parametric circle integral** on a Banach-space parameter. -/
theorem analyticOnNhd_circleIntegral {U : Set E} {f : E → ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (han : ∀ w ∈ sphere c R, AnalyticOnNhd ℂ (fun x => f x w) U)
    (hcont : ∀ x ∈ U, ContinuousOn (f x) (sphere c R))
    (hbd : ∀ x ∈ U, ∃ r > 0, ∃ M : ℝ, ball x r ⊆ U ∧ ∀ y ∈ ball x r, ∀ w ∈ sphere c R, ‖f y w‖ ≤ M) :
    AnalyticOnNhd ℂ (fun x => ∮ w in C(c, R), f x w) U := by
  have hmem : ∀ θ : ℝ, circleMap c R θ ∈ sphere c R := circleMap_mem_sphere c hR
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  refine analyticOnNhd_integral (F := fun x θ => deriv (circleMap c R) θ • f x (circleMap c R θ)) h2π
    (fun θ _ => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · intro y hy
    simp only [smul_eq_mul]
    exact analyticAt_const.mul (han _ (hmem θ) y hy)
  · simp only [deriv_circleMap, smul_eq_mul]
    exact ((continuous_circleMap 0 R).mul continuous_const).continuousOn.mul
      ((hcont x hx).comp_continuous (continuous_circleMap c R) hmem).continuousOn
  · obtain ⟨r, hr, M, hsub, hM⟩ := hbd x hx
    refine ⟨r, hr, |R| * M, hsub, fun y hy θ _ => ?_⟩
    rw [deriv_circleMap, smul_eq_mul, norm_mul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
    exact mul_le_mul_of_nonneg_left (hM y hy _ (hmem θ)) (abs_nonneg R)

theorem norm_circleIntegral_le {f : ℂ → ℂ} {c : ℂ} {R C : ℝ} (hR : 0 ≤ R) (hf : ∀ w ∈ sphere c R, ‖f w‖ ≤ C) :
    ‖(2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(c, R), f w‖ ≤ R * C := by
  have h := circleIntegral.norm_integral_le_of_norm_le_const hR hf
  have hn : ‖(2 * Real.pi * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_I, mul_one, Complex.norm_mul, Complex.norm_two, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [norm_mul, hn]
  calc (2 * Real.pi)⁻¹ * ‖∮ w in C(c, R), f w‖ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * R * C) := by
        gcongr
    _ = R * C := by field_simp

end QuantumNLS.RB01ParamInt

#print axioms QuantumNLS.RB01ParamInt.analyticOnNhd_integral
#print axioms QuantumNLS.RB01ParamInt.analyticOnNhd_circleIntegral
#print axioms QuantumNLS.RB01ParamInt.norm_circleIntegral_le
