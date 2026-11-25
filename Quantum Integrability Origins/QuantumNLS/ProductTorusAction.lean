import QuantumNLS.ProductTorusContinuity
import QuantumNLS.Ext025B6TorusCoordinates

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T4b: the continuous action of the product torus

Source: `chapters/global/product_torus.tex`, proof, "The product topology and full initial-point regularity", third
paragraph: "Thus `T` descends from bounded real sequences to the product of circles, using representatives in
`[-π,π]`. Continuity is also valid across endpoints of the representative interval: lifts of a converging product
sequence can be chosen so their coordinatewise differences tend to zero and remain bounded by `2π`; bounded integer
changes do not affect the maps. This constructs the asserted continuous product action." Theorem statement: "there is
a continuous action `T` of the product group `𝕋^ℤ` on `𝓗` extending these individual flows".

The product torus is the accepted EXT-025 B6 `Torus = ℤ → Circle` (product topology), and `Circle.exp t = e^{it}`.
* `lift ψ`: the representatives `arg ψ_n ∈ (−π, π]`, a bounded sequence;
* `T_congr_exp`: angles with the same image in the torus give the same map (T4a `T_period` plus the group law);
* `act DI ψ := T_{lift ψ}`;
* **`product_action`**: `act (ψψ') = act ψ ∘ act ψ'`, `act 1 = id`, `(ψ, u) ↦ act ψ u` is continuous on
  `Torus × H` (product topology), and `act` extends the individual flows:
  `act (e^{it} at coordinate n, 1 elsewhere) = φ_{I_n}^t`; moreover `act (e^{iθ}) = T_θ` for every bounded `θ`.
Continuity is proved sequentially (the torus is a countable product of metric spaces, hence first countable), with
lifts `lift ψ + lift(ψ^j/ψ)` whose coordinatewise differences tend to zero and are bounded by `2π`, and T4a
`T_tendsto`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology Set Metric
open scoped InnerProductSpace NNReal

noncomputable section

namespace QuantumNLS.ProductTorusAction

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusFlow QuantumNLS.ProductTorusCommute
  QuantumNLS.ProductTorusContinuity
open QuantumNLS.Ext025B6TorusCoordinates (Torus)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

variable {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)}

/-- The representatives `arg ψ_n ∈ (−π, π]`. -/
def lift (ψ : Torus) : Linf :=
  ⟨fun n => Complex.arg (ψ n : ℂ), memℓp_infty ⟨Real.pi, by
    rintro _ ⟨n, rfl⟩
    exact (Real.norm_eq_abs _).le.trans (Complex.abs_arg_le_pi _)⟩⟩

theorem lift_apply (ψ : Torus) (n : ℤ) : lift ψ n = Complex.arg (ψ n : ℂ) := rfl

theorem exp_lift (ψ : Torus) (n : ℤ) : Circle.exp (lift ψ n) = ψ n := Circle.exp_arg (ψ n)

theorem norm_lift_le (ψ : Torus) : ‖lift ψ‖ ≤ Real.pi :=
  lp.norm_le_of_forall_le Real.pi_pos.le fun n => by
    rw [lift_apply, Real.norm_eq_abs]
    exact Complex.abs_arg_le_pi _

/-- Angles with the same image in the torus give the same map. -/
theorem T_congr_exp (h : Hyp I DI) (hpos : Nonneg I) (hprop : Proper I) (hper : Periodic DI) {θ θ' : Linf}
    (hθ : ∀ n, Circle.exp (θ n) = Circle.exp (θ' n)) (u : E) : T DI θ u = T DI θ' u := by
  have hm : ∀ n, ∃ m : ℤ, θ n = θ' n + m * (2 * Real.pi) := fun n => Circle.exp_eq_exp.1 (hθ n)
  choose m hm using hm
  have hd : ∀ n, (θ - θ') n = 2 * Real.pi * m n := fun n => by
    rw [lp.coeFn_sub, Pi.sub_apply, hm n]
    ring
  have hB : ∀ n, |(m n : ℝ)| ≤ ‖θ - θ'‖ / (2 * Real.pi) := fun n => by
    have h1 := lp.norm_apply_le_norm (p := ⊤) ENNReal.top_ne_zero (θ - θ') n
    rw [Real.norm_eq_abs, hd, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h1
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hp := T_period h hpos hprop hper m hB (θ - θ') hd (T DI θ' u)
  rw [← hp, ← T_add h, sub_add_cancel]

/-- The action of the product torus: `act ψ := T_{lift ψ}`. -/
def act (DI : E → (E →L[ℝ] L1 ℝ)) (ψ : Torus) (u : E) : E := T DI (lift ψ) u

theorem act_exp (h : Hyp I DI) (hpos : Nonneg I) (hprop : Proper I) (hper : Periodic DI) (θ : Linf) (u : E) :
    act DI (fun n => Circle.exp (θ n)) u = T DI θ u :=
  T_congr_exp h hpos hprop hper (fun _ => Circle.exp_arg _) u

theorem act_mul (h : Hyp I DI) (hpos : Nonneg I) (hprop : Proper I) (hper : Periodic DI) (ψ ψ' : Torus)
    (u : E) : act DI (ψ * ψ') u = act DI ψ (act DI ψ' u) := by
  unfold act
  rw [← T_add h]
  refine T_congr_exp h hpos hprop hper (fun n => ?_) u
  rw [exp_lift, lp.coeFn_add, Pi.add_apply, Circle.exp_add, exp_lift, exp_lift, Pi.mul_apply]

theorem act_one (h : Hyp I DI) (hpos : Nonneg I) (hprop : Proper I) (hper : Periodic DI) (u : E) :
    act DI 1 u = u := by
  unfold act
  rw [T_congr_exp h hpos hprop hper (θ' := 0) (fun _ => by rw [exp_lift, lp.coeFn_zero, Pi.zero_apply,
    Circle.exp_zero, Pi.one_apply]) u, T_zero h]

/-- The action extends the individual flows: the torus element `e^{it}` at coordinate `n` acts as `φ_{I_n}^t`. -/
theorem act_single (h : Hyp I DI) (hpos : Nonneg I) (hprop : Proper I) (hper : Periodic DI) (n : ℤ) (t : ℝ)
    (u : E) : act DI (Pi.mulSingle n (Circle.exp t)) u = flow DI (e n) t u := by
  unfold act
  rw [flow_eq_T h]
  refine T_congr_exp h hpos hprop hper (fun k => ?_) u
  rw [exp_lift, lp.coeFn_smul, Pi.smul_apply, e, lp.single_apply, smul_eq_mul]
  by_cases hk : k = n
  · subst hk
    simp
  · rw [Pi.mulSingle_eq_of_ne hk, Pi.single_eq_of_ne hk, mul_zero, Circle.exp_zero]

/-- Continuity of the action on `Torus × H`. -/
theorem act_continuous (h : Hyp I DI) (hpos : Nonneg I) (hprop : Proper I) (hper : Periodic DI) :
    Continuous (fun p : Torus × E => act DI p.1 p.2) := by
  rw [continuous_iff_seqContinuous]
  intro xs p hxs
  have hψ : ∀ n, Tendsto (fun j => (xs j).1 n) atTop (𝓝 (p.1 n)) := fun n =>
    (((continuous_apply n).comp continuous_fst).tendsto p).comp hxs
  have hu : Tendsto (fun j => (xs j).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hxs
  set θs : ℕ → Linf := fun j => lift p.1 + lift (fun n => (xs j).1 n / p.1 n) with hθs
  have hexp : ∀ j n, Circle.exp (θs j n) = Circle.exp (lift (xs j).1 n) := fun j n => by
    show Circle.exp ((lift p.1 + lift (fun n => (xs j).1 n / p.1 n) : Linf) n) = Circle.exp (lift (xs j).1 n)
    rw [lp.coeFn_add, Pi.add_apply, Circle.exp_add, exp_lift, exp_lift, exp_lift]
    exact mul_div_cancel _ _
  have hact : (fun j => act DI (xs j).1 (xs j).2) = fun j => T DI (θs j) (xs j).2 :=
    funext fun j => (T_congr_exp h hpos hprop hper (fun n => (hexp j n).symm) _)
  have hR : ∀ j, ‖θs j‖ ≤ 2 * Real.pi := fun j =>
    (norm_add_le _ _).trans (by linarith [norm_lift_le p.1, norm_lift_le (fun n => (xs j).1 n / p.1 n)])
  have hcoord : ∀ n, Tendsto (fun j => θs j n) atTop (𝓝 (lift p.1 n)) := by
    intro n
    have hdiv : Tendsto (fun j => (xs j).1 n / p.1 n) atTop (𝓝 1) := by
      have := (hψ n).div_const (p.1 n)
      rwa [div_self'] at this
    have harg : Tendsto (fun j => Complex.arg (((xs j).1 n / p.1 n : Circle) : ℂ)) atTop (𝓝 0) := by
      have hc : ContinuousAt (fun z : Circle => Complex.arg (z : ℂ)) 1 :=
        (Complex.continuousAt_arg (by simp [Complex.one_mem_slitPlane])).comp continuous_subtype_val.continuousAt
      have := hc.tendsto.comp hdiv
      simp only [Function.comp_def, Circle.coe_one, Complex.arg_one] at this
      exact this
    have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => lift p.1 n) atTop (𝓝 (lift p.1 n))).add harg
    rw [add_zero] at this
    refine this.congr fun j => ?_
    show lift p.1 n + Complex.arg (((xs j).1 n / p.1 n : Circle) : ℂ) =
      ((lift p.1 + lift (fun n => (xs j).1 n / p.1 n) : Linf) : ℤ → ℝ) n
    rw [lp.coeFn_add, Pi.add_apply, lift_apply (fun n => (xs j).1 n / p.1 n) n]
  have hθR : ‖lift p.1‖ ≤ 2 * Real.pi := (norm_lift_le p.1).trans (by linarith [Real.pi_pos])
  have hlim := T_tendsto h hpos hprop hR hθR hcoord hu
  show Tendsto (fun j => act DI (xs j).1 (xs j).2) atTop (𝓝 (act DI p.1 p.2))
  rw [hact]
  exact hlim

/-- **The continuous product action** of `𝕋^ℤ = ℤ → Circle` on `𝓗`, extending the individual flows. -/
theorem product_action (h : Hyp I DI) (hpos : Nonneg I) (hprop : Proper I) (hper : Periodic DI) :
    (∀ ψ ψ' u, act DI (ψ * ψ') u = act DI ψ (act DI ψ' u)) ∧ (∀ u, act DI 1 u = u) ∧
      Continuous (fun p : Torus × E => act DI p.1 p.2) ∧
      (∀ n t u, act DI (Pi.mulSingle n (Circle.exp t)) u = flow DI (e n) t u) ∧
      (∀ θ u, act DI (fun n => Circle.exp (θ n)) u = T DI θ u) :=
  ⟨act_mul h hpos hprop hper, act_one h hpos hprop hper, act_continuous h hpos hprop hper,
    act_single h hpos hprop hper, act_exp h hpos hprop hper⟩

end QuantumNLS.ProductTorusAction

#print axioms QuantumNLS.ProductTorusAction.T_congr_exp
#print axioms QuantumNLS.ProductTorusAction.act_mul
#print axioms QuantumNLS.ProductTorusAction.act_continuous
#print axioms QuantumNLS.ProductTorusAction.product_action
