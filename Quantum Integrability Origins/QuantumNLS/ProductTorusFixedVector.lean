import QuantumNLS.ProductTorusAction

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T5b: fixed-vector strong continuity of the derivatives
# (GP-16 application for this consumer, first derivatives)

Source: `chapters/global/product_torus.tex`, proof, "The product topology and full initial-point regularity", last
paragraph: "With `h` fixed, `k ↦ D²𝓘(u)[h,k]` is a compact operator from `𝓗` to `ℓ¹` ... Consequently
`DX_{θ^j}(u)h → DX_θ(u)h` for coordinatewise convergent bounded angles. The convergence is uniform for `(u,h)` in a
compact set, by a finite-net argument. In the linear variational equation, the limiting tangent trajectory has compact
image on `[0,1]`. Norm continuity of `D²𝓘`, uniformly near that compact trajectory, also controls the coefficient change
caused by the already convergent base trajectories. The fixed-direction compact tail estimate controls the remaining
change of the angle parameter. The uniform derivative bound, the preceding strong convergence on that image, and
Gronwall therefore prove `DT_{θ^j}(u)h → DT_θ(u)h`. ... These assertions provide measurability without claiming
operator-norm continuity of the product action." Theorem statement: "For fixed tangent vectors, those derivatives depend
strongly continuously on the group parameter. Operator-norm continuity in the product parameter is not asserted."

Proved (hypotheses `ProductTorusFlow.Hyp` and T4a `Nonneg`, `Proper`, `Periodic`):
* `flow_tendsto_unif`: for a fixed initial point the flows converge uniformly on `[0,T]`;
* `fderiv_X_sub_apply`: `DX_{θ'}(x)k − DX_θ(x)k = W⁻¹(pair(θ'−θ) ∘ D²𝓘(x)k)`;
* **`fderiv_flow_apply_tendsto`**: `Dφ_{θ^j}^t(u)h → Dφ_θ^t(u)h` (all `t`), by the printed route: the compact family
  `{D²𝓘(x)k : x ∈ fibre, k ∈ tangent trajectory}` of Hilbert-to-`ℓ¹` operators and T1 `pair_tendsto_uniform`
  (compact slices), uniform continuity of `DX_θ` on the compact fibre plus `flow_tendsto_unif` (base trajectories),
  the uniform bound `‖DX_{θ^j}‖ ≤ R A₂/2` and Gronwall;
* **`act_fderiv_continuous`**: for fixed `u, h`, `ψ ↦ D(act ψ)(u)h` is continuous on the product torus (hence Borel
  measurable, `act_fderiv_measurable`); no operator-norm continuity is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology Set Metric
open scoped InnerProductSpace NNReal

noncomputable section

namespace QuantumNLS.ProductTorusFixedVector

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusFlow QuantumNLS.ProductTorusVariational
  QuantumNLS.ProductTorusCommute QuantumNLS.ProductTorusContinuity QuantumNLS.ProductTorusAction
open QuantumNLS.Ext025B6TorusCoordinates (Torus)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

variable {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)}

/-- Uniform convergence of the flows on `[0,T]` for a fixed initial point. -/
theorem flow_tendsto_unif (h : Hyp I DI) {θs : ℕ → Linf} {θ : Linf} {R : ℝ} (hR : ∀ j, ‖θs j‖ ≤ R)
    (hθR : ‖θ‖ ≤ R) (hcoord : ∀ n, Tendsto (fun j => θs j n) atTop (𝓝 (θ n))) (u : E) {T₀ : ℝ} :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ s ∈ Icc 0 T₀, dist (flow DI (θs j) s u) (flow DI θ s u) ≤ ε := by
  intro ε hε
  have hC : IsCompact (I ⁻¹' {I u}) := h.fibre_compact u
  have hmem : ∀ θ' : Linf, ∀ s, flow DI θ' s u ∈ I ⁻¹' {I u} := fun θ' s =>
    mem_fibre_flow h θ' (Set.mem_singleton (I u)) s
  obtain ⟨L, hL⟩ := lipschitzOn_compact h.contDiff θ hC
  have hunif := X_tendsto_uniform DI _ hC h.contDiff.continuous.continuousOn θs θ hR hθR hcoord
  have hK0 : (0 : ℝ) < ((L + 1 : ℝ≥0) : ℝ) := by positivity
  set M : ℝ := Real.exp (((L + 1 : ℝ≥0) : ℝ) * T₀) / ((L + 1 : ℝ≥0) : ℝ) with hM
  have hM0 : 0 < M := by positivity
  filter_upwards [hunif (ε / M) (by positivity)] with j hX
  intro s hs
  have hg := dist_le_of_approx_trajectories_ODE_of_mem (v := fun _ => X DI θ)
    (s := fun _ => I ⁻¹' {I u}) (K := L + 1)
    (f := fun s => flow DI (θs j) s u) (g := fun s => flow DI θ s u) (a := 0) (b := s)
    (f' := fun s => X DI (θs j) (flow DI (θs j) s u)) (g' := fun s => X DI θ (flow DI θ s u))
    (εf := ε / M) (εg := 0) (δ := 0)
    (fun _ _ => hL.weaken le_self_add) (continuous_flow_time h _ _).continuousOn
    (fun s _ => (hasDerivAt_flow h _ _ s).hasDerivWithinAt)
    (fun s _ => by rw [dist_eq_norm]; exact hX _ (hmem _ s))
    (fun s _ => hmem _ s) (continuous_flow_time h _ _).continuousOn
    (fun s _ => (hasDerivAt_flow h _ _ s).hasDerivWithinAt) (fun s _ => by simp)
    (fun s _ => hmem _ s)
    (by show dist (flow DI (θs j) 0 u) (flow DI θ 0 u) ≤ 0; rw [flow_zero h, flow_zero h, dist_self])
    s ⟨hs.1, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 hK0.ne'] at hg
  simp only [sub_zero, add_zero, zero_mul, zero_add] at hg
  refine hg.trans ?_
  have he : Real.exp (((L + 1 : ℝ≥0) : ℝ) * s) - 1 ≤ Real.exp (((L + 1 : ℝ≥0) : ℝ) * T₀) := by
    have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hK0.le)
    linarith
  calc ε / M / ((L + 1 : ℝ≥0) : ℝ) * (Real.exp (((L + 1 : ℝ≥0) : ℝ) * s) - 1)
      ≤ ε / M / ((L + 1 : ℝ≥0) : ℝ) * Real.exp (((L + 1 : ℝ≥0) : ℝ) * T₀) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = ε := by rw [hM]; field_simp

/-- `DX_{θ'}(x)k − DX_θ(x)k = W⁻¹(pair(θ'−θ) ∘ D²𝓘(x)k)`. -/
theorem fderiv_X_sub_apply (h : Hyp I DI) (θ' θ : Linf) (x k : E) :
    fderiv ℝ (X DI θ') x k - fderiv ℝ (X DI θ) x k = Winv ((pair (θ' - θ)).comp (fderiv ℝ DI x k)) := by
  rw [fderiv_X_apply h, fderiv_X_apply h, ← Winv_sub, pair_sub, ContinuousLinearMap.sub_comp]

theorem norm_Winv_comp_le (δ : Linf) (A : E →L[ℝ] L1 ℝ) : ‖Winv ((pair δ).comp A)‖ ≤ ‖(pair δ).comp A‖ / 2 :=
  le_of_eq (norm_Winv _)

/-- **Fixed-vector strong continuity of the derivatives in the angle**, nonnegative times. -/
theorem fderiv_flow_apply_tendsto_nonneg (h : Hyp I DI) {θs : ℕ → Linf} {θ : Linf} {R : ℝ}
    (hR : ∀ j, ‖θs j‖ ≤ R) (hθR : ‖θ‖ ≤ R) (hcoord : ∀ n, Tendsto (fun j => θs j n) atTop (𝓝 (θ n)))
    (u k : E) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun j => fderiv ℝ (flow DI (θs j) t) u k) atTop (𝓝 (fderiv ℝ (flow DI θ t) u k)) := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hθR
  set F : Set E := I ⁻¹' {I u} with hF
  have hFc : IsCompact F := h.fibre_compact u
  have hmem : ∀ θ' : Linf, ∀ s, flow DI θ' s u ∈ F := fun θ' s =>
    mem_fibre_flow h θ' (Set.mem_singleton (I u)) s
  have hD2c := h.contDiff.continuous_fderiv one_ne_zero
  obtain ⟨A₂, hA₂⟩ := hFc.exists_bound_of_continuousOn (h.contDiff.continuous_fderiv one_ne_zero).continuousOn
  have hA₂0 : 0 ≤ A₂ := (norm_nonneg _).trans (hA₂ u (Set.mem_singleton (I u)))
  set K : ℝ := R * A₂ / 2 + 1 with hK
  have hK0 : 0 < K := by positivity
  have hAj : ∀ θ' : Linf, ‖θ'‖ ≤ R → ∀ x ∈ F, ‖fderiv ℝ (X DI θ') x‖ ≤ K := fun θ' hθ' x hx => by
    refine (norm_fderiv_X_le h θ' x).trans ?_
    have := mul_le_mul hθ' (hA₂ x hx) (norm_nonneg _) hR0
    linarith
  -- the limiting tangent trajectory on `[0,t]`
  set w : ℝ → E := fun s => fderiv ℝ (flow DI θ s) u k with hw
  have hwc : Continuous w := (continuous_fderiv_flow h θ u).clm_apply continuous_const
  obtain ⟨W, hW⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hwc.continuousOn
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0 ⟨le_rfl, ht⟩)
  -- compact family of slices `D²𝓘(x) w(s)`
  have hfam : IsCompact ((fun p : E × ℝ => fderiv ℝ DI p.1 (w p.2)) '' (F ×ˢ Icc 0 t)) :=
    (hFc.prod isCompact_Icc).image (hD2c.comp continuous_fst |>.clm_apply (hwc.comp continuous_snd))
  -- uniform continuity of `DX_θ` on the compact fibre
  have hDXc : Continuous (fderiv ℝ (X DI θ)) := (X_contDiff h.contDiff θ).continuous_fderiv one_ne_zero
  have hUC := hFc.uniformContinuousOn_of_continuous hDXc.continuousOn
  set Mg : ℝ := Real.exp (K * t) / K with hMg
  have hMg0 : 0 < Mg := by positivity
  refine Metric.tendsto_nhds.2 fun η hη => ?_
  set ε : ℝ := η / (4 * Mg) with hε
  have hε0 : 0 < ε := by positivity
  -- step 1: angle change on the compact slices
  have hslice := pair_tendsto_uniform _ hfam θs θ hR hθR hcoord ε hε0
  -- step 2: base trajectories
  obtain ⟨ρ, hρ, hρU⟩ := Metric.uniformContinuousOn_iff.1 hUC (ε / (W + 1)) (by positivity)
  have hbase := flow_tendsto_unif h hR hθR hcoord u (T₀ := t) (ρ / 2) (by positivity)
  filter_upwards [hslice, hbase] with j hj hb
  -- the error of the tangent trajectories
  have hcont : ContinuousOn (fun s => fderiv ℝ (flow DI (θs j) s) u k - w s) (Icc 0 t) :=
    (((continuous_fderiv_flow h (θs j) u).clm_apply continuous_const).sub hwc).continuousOn
  have hder : ∀ s ∈ Ico (0 : ℝ) t, HasDerivWithinAt (fun s => fderiv ℝ (flow DI (θs j) s) u k - w s)
      (fderiv ℝ (X DI (θs j)) (flow DI (θs j) s u) (fderiv ℝ (flow DI (θs j) s) u k) -
        fderiv ℝ (X DI θ) (flow DI θ s u) (w s)) (Ici s) s := fun s _ =>
    ((hasDerivAt_fderiv_flow_apply h (θs j) u k s).sub (hasDerivAt_fderiv_flow_apply h θ u k s)).hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) t,
      ‖fderiv ℝ (X DI (θs j)) (flow DI (θs j) s u) (fderiv ℝ (flow DI (θs j) s) u k) -
        fderiv ℝ (X DI θ) (flow DI θ s u) (w s)‖ ≤
      K * ‖fderiv ℝ (flow DI (θs j) s) u k - w s‖ + (ε + ε) := by
    intro s hs
    have hsI : s ∈ Icc 0 t := Ico_subset_Icc_self hs
    set xj := flow DI (θs j) s u
    set x := flow DI θ s u
    have hsplit : fderiv ℝ (X DI (θs j)) xj (fderiv ℝ (flow DI (θs j) s) u k) - fderiv ℝ (X DI θ) x (w s) =
        fderiv ℝ (X DI (θs j)) xj (fderiv ℝ (flow DI (θs j) s) u k - w s) +
          (fderiv ℝ (X DI (θs j)) xj (w s) - fderiv ℝ (X DI θ) xj (w s)) +
          (fderiv ℝ (X DI θ) xj (w s) - fderiv ℝ (X DI θ) x (w s)) := by
      rw [map_sub]; abel
    rw [hsplit]
    have e1 : ‖fderiv ℝ (X DI (θs j)) xj (fderiv ℝ (flow DI (θs j) s) u k - w s)‖ ≤
        K * ‖fderiv ℝ (flow DI (θs j) s) u k - w s‖ :=
      ((fderiv ℝ (X DI (θs j)) xj).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hAj _ (hR j) xj (hmem _ s)) (norm_nonneg _))
    have e2 : ‖fderiv ℝ (X DI (θs j)) xj (w s) - fderiv ℝ (X DI θ) xj (w s)‖ ≤ ε := by
      rw [fderiv_X_sub_apply h, norm_Winv]
      have := hj (fderiv ℝ DI xj (w s)) ⟨(xj, s), ⟨hmem _ s, hsI⟩, rfl⟩
      linarith [norm_nonneg ((pair (θs j - θ)).comp (fderiv ℝ DI xj (w s)))]
    have e3 : ‖fderiv ℝ (X DI θ) xj (w s) - fderiv ℝ (X DI θ) x (w s)‖ ≤ ε := by
      rw [← sub_apply]
      have hdx : dist xj x < ρ := lt_of_le_of_lt (hb s hsI) (half_lt_self hρ)
      have hU := hρU xj (hmem _ s) x (hmem _ s) hdx
      rw [dist_eq_norm] at hU
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have hws : ‖w s‖ ≤ W := hW s hsI
      calc ‖fderiv ℝ (X DI θ) xj - fderiv ℝ (X DI θ) x‖ * ‖w s‖ ≤ ε / (W + 1) * W :=
            mul_le_mul hU.le hws (norm_nonneg _) (by positivity)
        _ ≤ ε := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith
    have hna := norm_add_le (fderiv ℝ (X DI (θs j)) xj (fderiv ℝ (flow DI (θs j) s) u k - w s))
      (fderiv ℝ (X DI (θs j)) xj (w s) - fderiv ℝ (X DI θ) xj (w s))
    calc _ ≤ ‖fderiv ℝ (X DI (θs j)) xj (fderiv ℝ (flow DI (θs j) s) u k - w s) +
          (fderiv ℝ (X DI (θs j)) xj (w s) - fderiv ℝ (X DI θ) xj (w s))‖ +
          ‖fderiv ℝ (X DI θ) xj (w s) - fderiv ℝ (X DI θ) x (w s)‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (a := 0) (b := t) (K := K) (δ := 0) (ε := ε + ε)
    hcont hder (by
      show ‖fderiv ℝ (flow DI (θs j) 0) u k - fderiv ℝ (flow DI θ 0) u k‖ ≤ 0
      rw [fderiv_flow_zero h, fderiv_flow_zero h, sub_self, norm_zero])
    hbound t ⟨ht, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 hK0.ne'] at hg
  simp only [sub_zero, zero_mul, zero_add] at hg
  rw [dist_eq_norm]
  calc ‖fderiv ℝ (flow DI (θs j) t) u k - fderiv ℝ (flow DI θ t) u k‖
      ≤ (ε + ε) / K * (Real.exp (K * t) - 1) := hg
    _ ≤ (ε + ε) / K * Real.exp (K * t) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = η / 2 := by rw [hε, hMg]; field_simp; ring
    _ < η := by linarith

/-- **Fixed-vector strong continuity of the derivatives in the angle** (all times). -/
theorem fderiv_flow_apply_tendsto (h : Hyp I DI) {θs : ℕ → Linf} {θ : Linf} {R : ℝ}
    (hR : ∀ j, ‖θs j‖ ≤ R) (hθR : ‖θ‖ ≤ R) (hcoord : ∀ n, Tendsto (fun j => θs j n) atTop (𝓝 (θ n)))
    (u k : E) (t : ℝ) :
    Tendsto (fun j => fderiv ℝ (flow DI (θs j) t) u k) atTop (𝓝 (fderiv ℝ (flow DI θ t) u k)) := by
  rcases le_total 0 t with ht | ht
  · exact fderiv_flow_apply_tendsto_nonneg h hR hθR hcoord u k ht
  · have e1 : (fun j => fderiv ℝ (flow DI (θs j) t) u k) = fun j => fderiv ℝ (flow DI (-θs j) (-t)) u k :=
      funext fun j => by rw [flow_eq_neg h (θs j) t]
    rw [e1, flow_eq_neg h θ t]
    exact fderiv_flow_apply_tendsto_nonneg h (θs := fun j => -θs j) (θ := -θ) (R := R)
      (fun j => by rw [norm_neg]; exact hR j) (by rw [norm_neg]; exact hθR) (neg_coord hcoord) u k (by linarith)

theorem act_eq_T (h : Hyp I DI) (hpos : Nonneg I) (hprop : Proper I) (hper : Periodic DI) {ψ : Torus} {θ : Linf}
    (hθ : ∀ n, Circle.exp (θ n) = ψ n) : act DI ψ = T DI θ :=
  funext fun u => T_congr_exp h hpos hprop hper (fun n => by rw [exp_lift, hθ]) u

/-- Lifts of a convergent torus sequence: `lift ψ + lift(ψ^j/ψ)`, bounded by `2π`, coordinatewise convergent to
`lift ψ`, with the right image in the torus. -/
theorem lifts_tendsto {ψs : ℕ → Torus} {ψ : Torus} (hψ : ∀ n, Tendsto (fun j => ψs j n) atTop (𝓝 (ψ n))) :
    (∀ j, ‖lift ψ + lift (fun n => ψs j n / ψ n)‖ ≤ 2 * Real.pi) ∧
      (∀ n, Tendsto (fun j => (lift ψ + lift (fun n => ψs j n / ψ n) : Linf) n) atTop (𝓝 (lift ψ n))) ∧
      (∀ j n, Circle.exp ((lift ψ + lift (fun n => ψs j n / ψ n) : Linf) n) = ψs j n) := by
  refine ⟨fun j => (norm_add_le _ _).trans (by linarith [norm_lift_le ψ, norm_lift_le (fun n => ψs j n / ψ n)]),
    fun n => ?_, fun j n => ?_⟩
  · have hdiv : Tendsto (fun j => ψs j n / ψ n) atTop (𝓝 1) := by
      have := (hψ n).div_const (ψ n)
      rwa [div_self'] at this
    have harg : Tendsto (fun j => Complex.arg ((ψs j n / ψ n : Circle) : ℂ)) atTop (𝓝 0) := by
      have hc : ContinuousAt (fun z : Circle => Complex.arg (z : ℂ)) 1 :=
        (Complex.continuousAt_arg (by simp [Complex.one_mem_slitPlane])).comp continuous_subtype_val.continuousAt
      have := hc.tendsto.comp hdiv
      simp only [Function.comp_def, Circle.coe_one, Complex.arg_one] at this
      exact this
    have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => lift ψ n) atTop (𝓝 (lift ψ n))).add harg
    rw [add_zero] at this
    refine this.congr fun j => ?_
    show lift ψ n + Complex.arg ((ψs j n / ψ n : Circle) : ℂ) =
      ((lift ψ + lift (fun n => ψs j n / ψ n) : Linf) : ℤ → ℝ) n
    rw [lp.coeFn_add, Pi.add_apply, lift_apply (fun n => ψs j n / ψ n) n]
  · rw [lp.coeFn_add, Pi.add_apply, Circle.exp_add, exp_lift, exp_lift]
    exact mul_div_cancel _ _

/-- **GP-16 application (first derivatives): for fixed `u, h`, `ψ ↦ D(act ψ)(u)h` is continuous on the product
torus.** Operator-norm continuity is not asserted. -/
theorem act_fderiv_continuous (h : Hyp I DI) (hpos : Nonneg I) (hprop : Proper I) (hper : Periodic DI) (u k : E) :
    Continuous (fun ψ : Torus => fderiv ℝ (act DI ψ) u k) := by
  rw [continuous_iff_seqContinuous]
  intro ψs ψ hψs
  have hψ : ∀ n, Tendsto (fun j => ψs j n) atTop (𝓝 (ψ n)) := fun n =>
    ((continuous_apply n).tendsto ψ).comp hψs
  obtain ⟨hR, hcoord, hexp⟩ := lifts_tendsto hψ
  have hθR : ‖lift ψ‖ ≤ 2 * Real.pi := (norm_lift_le ψ).trans (by linarith [Real.pi_pos])
  have hlim := fderiv_flow_apply_tendsto h hR hθR hcoord u k 1
  have e1 : (fun j => fderiv ℝ (act DI (ψs j)) u k) =
      fun j => fderiv ℝ (flow DI (lift ψ + lift (fun n => ψs j n / ψ n)) 1) u k :=
    funext fun j => by rw [act_eq_T h hpos hprop hper (hexp j)]; rfl
  have e2 : act DI ψ = flow DI (lift ψ) 1 := rfl
  show Tendsto (fun j => fderiv ℝ (act DI (ψs j)) u k) atTop (𝓝 (fderiv ℝ (act DI ψ) u k))
  rw [e1, e2]
  exact hlim

/-- Borel measurability of the fixed-vector derivative family on the product torus. -/
theorem act_fderiv_measurable [MeasurableSpace E] [BorelSpace E] (h : Hyp I DI) (hpos : Nonneg I)
    (hprop : Proper I) (hper : Periodic DI) (u k : E) :
    Measurable (fun ψ : Torus => fderiv ℝ (act DI ψ) u k) :=
  (act_fderiv_continuous h hpos hprop hper u k).measurable

end QuantumNLS.ProductTorusFixedVector

#print axioms QuantumNLS.ProductTorusFixedVector.flow_tendsto_unif
#print axioms QuantumNLS.ProductTorusFixedVector.fderiv_flow_apply_tendsto
#print axioms QuantumNLS.ProductTorusFixedVector.act_fderiv_continuous
#print axioms QuantumNLS.ProductTorusFixedVector.act_fderiv_measurable
