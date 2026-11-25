import QuantumNLS.ProductTorusPrimitiveAnalytic

/-!
# R-4C2E4AC7, stage T8b-pre (CONDITIONAL on the held GP-04 clause): derivative bounds and fixed-vector parameter
# continuity of all orders

Source: `chapters/global/product_torus.tex`, theorem, lines 39–44 ("Their full derivatives have uniform local operator
bounds. For fixed tangent vectors, those derivatives depend strongly continuously on the group parameter."), and the
proof ("Cauchy's formula on a smaller ball gives uniform operator bounds for every fixed derivative order"; "Repeating
this argument with the higher variational equations proves the same statement for each fixed finite list of tangent
vectors").

Generic (unconditional):
* `norm_changeOrigin_le_of_majorant`: `‖p n‖ rⁿ ≤ C` and `‖y‖ ≤ r/2` ⇒ `‖(p.changeOrigin y) k‖ ≤ C 2^{k+1}/r^k`;
* `norm_iteratedFDeriv_near`: then `‖D^k f(u+y)‖ ≤ k! C 2^{k+1}/r^k` for `‖y‖ < r/2`;
* `continuous_iteratedFDeriv_param`: for a family `f_ψ` of smooth maps with derivative bounds of every order on a
  ball, uniform in `ψ`, and `ψ ↦ f_ψ(z)` continuous, every `ψ ↦ D^n f_ψ(z)[v₁,…,vₙ]` is continuous (each order is a
  uniform-in-`ψ` limit of difference quotients of the previous one).
Application (conditional on `HeldGP04AnalyticInitialDependence`, through T6):
* **`act_iteratedFDeriv_bound`**: near each `u`, `‖D^k T_ψ(x)‖ ≤ k! C 2^{k+1}/r^k` for all `k`, all `x ∈ B(u, r/2)`
  and all `ψ ∈ 𝕋^ℤ` (uniform local operator bounds of all orders);
* **`act_iteratedFDeriv_continuous`**: for every order `n`, point `u` and fixed tangent vectors `v`,
  `ψ ↦ D^n T_ψ(u)[v]` is continuous on the product torus. No operator-norm continuity is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

open Filter Topology Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace QuantumNLS.ProductTorusAllOrders

open QuantumNLS.ProductTorusRealAverage

section Generic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_changeOrigin_le_of_majorant {p : FormalMultilinearSeries ℝ E F} {r C : ℝ} (hr : 0 < r)
    (hp : ∀ n, ‖p n‖ * r ^ n ≤ C) {y : E} (hy : ‖y‖ ≤ r / 2) (k : ℕ) :
    ‖p.changeOrigin y k‖ ≤ C * 2 ^ (k + 1) / r ^ k := by
  have hterm : ∀ l, ‖p.changeOriginSeries k l (fun _ => y)‖ ≤
      C / r ^ k * (((l + k).choose k : ℝ) * (1 / 2 : ℝ) ^ l) := by
    intro l
    have h1 := p.nnnorm_changeOriginSeries_apply_le_tsum k l y
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin,
      nsmul_eq_mul] at h1
    have h2 : ‖p.changeOriginSeries k l (fun _ => y)‖ ≤ ((k + l).choose l : ℝ) * (‖p (k + l)‖ * ‖y‖ ^ l) := by
      have := NNReal.coe_le_coe.2 h1
      simpa using this
    have hpk : ‖p (k + l)‖ ≤ C / r ^ (k + l) := by rw [le_div_iff₀ (by positivity)]; exact hp _
    have hyl : ‖y‖ ^ l ≤ (r / 2) ^ l := pow_le_pow_left₀ (norm_nonneg _) hy l
    have hch : ((k + l).choose l : ℝ) = ((l + k).choose k : ℝ) := by
      rw [add_comm l k]
      exact_mod_cast (Nat.choose_symm_add).symm
    have hC : 0 ≤ C := (by positivity : (0 : ℝ) ≤ ‖p 0‖ * r ^ 0).trans (hp 0)
    calc ‖p.changeOriginSeries k l (fun _ => y)‖ ≤ ((k + l).choose l : ℝ) * (‖p (k + l)‖ * ‖y‖ ^ l) := h2
      _ ≤ ((k + l).choose l : ℝ) * (C / r ^ (k + l) * (r / 2) ^ l) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hpk hyl (by positivity) (by positivity)) (by positivity)
      _ = C / r ^ k * (((l + k).choose k : ℝ) * (1 / 2 : ℝ) ^ l) := by
          rw [hch, pow_add, div_pow]
          field_simp
          rw [mul_assoc _ (2 ^ l), ← mul_pow]
          norm_num
  have hsum := (hasSum_choose_mul_geometric_of_norm_lt_one k (r := (1 / 2 : ℝ)) (by norm_num)).mul_left
    (C / r ^ k)
  have hb := tsum_of_norm_bounded hsum hterm
  calc ‖p.changeOrigin y k‖ = ‖∑' l, p.changeOriginSeries k l (fun _ => y)‖ := rfl
    _ ≤ C / r ^ k * (1 / (1 - 1 / 2) ^ (k + 1)) := hb
    _ = C * 2 ^ (k + 1) / r ^ k := by
        rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div_pow, one_div_one_div]
        ring

theorem norm_iteratedFDeriv_near [CompleteSpace F] {f : E → F} {p : FormalMultilinearSeries ℝ E F} {u : E}
    {r C : ℝ} (hr : 0 < r) (hf : HasFPowerSeriesOnBall f p u (ENNReal.ofReal r)) (hp : ∀ n, ‖p n‖ * r ^ n ≤ C)
    {y : E} (hy : ‖y‖ < r / 2) (k : ℕ) :
    ‖iteratedFDeriv ℝ k f (u + y)‖ ≤ k.factorial * (C * 2 ^ (k + 1) / r ^ k) := by
  have hy' : (‖y‖₊ : ℝ≥0∞) < ENNReal.ofReal r := by
    rw [ENNReal.ofReal, ENNReal.coe_lt_coe, Real.lt_toNNReal_iff_coe_lt, coe_nnnorm]
    linarith
  have hc := hf.changeOrigin hy'
  refine (norm_iteratedFDeriv_le_of_series hc k).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_changeOrigin_le_of_majorant hr hp hy.le k) (by positivity)

/-- Fixed-vector parameter continuity of all derivative orders from uniform derivative bounds on a ball. -/
theorem continuous_iteratedFDeriv_param [CompleteSpace F] {Ψ : Type*} [TopologicalSpace Ψ] {f : Ψ → E → F}
    {u : E} {ρ : ℝ} (hf : ∀ ψ (m : ℕ), ContDiff ℝ m (f ψ)) (M : ℕ → ℝ)
    (hM : ∀ ψ k, ∀ z ∈ ball u ρ, ‖iteratedFDeriv ℝ k (f ψ) z‖ ≤ M k)
    (h0 : ∀ z ∈ ball u ρ, Continuous (fun ψ => f ψ z)) :
    ∀ n, ∀ z ∈ ball u ρ, ∀ v : Fin n → E, Continuous (fun ψ => iteratedFDeriv ℝ n (f ψ) z v) := by
  have hdiff : ∀ ψ (k : ℕ), Differentiable ℝ (iteratedFDeriv ℝ k (f ψ)) := fun ψ k =>
    (hf ψ (k + 1)).differentiable_iteratedFDeriv (mod_cast lt_add_one k)
  intro n
  induction n with
  | zero =>
    intro z hz v
    simpa using h0 z hz
  | succ n ih =>
    intro z hz v
    obtain ⟨δ, hδ, hδb⟩ : ∃ δ > 0, closedBall z δ ⊆ ball u ρ := by
      refine ⟨(ρ - dist z u) / 2, by have := mem_ball.1 hz; linarith, fun w hw => ?_⟩
      rw [mem_closedBall] at hw
      rw [mem_ball]
      have := mem_ball.1 hz
      have := dist_triangle w z u
      linarith
    set M2 : ℝ := max (M (n + 2)) 0 with hM2
    have hM20 : 0 ≤ M2 := le_max_right _ _
    set P : ℝ := ∏ i, ‖Fin.tail v i‖ with hP
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => norm_nonneg _
    set δ' : ℝ := δ / (‖v 0‖ + 1) with hδ'
    have hδ'0 : 0 < δ' := by positivity
    set s : ℕ → ℝ := fun m => δ' / ((m : ℝ) + 1) with hs
    have hs0 : ∀ m, 0 < s m := fun m => by positivity
    have hsv : ∀ m, ‖s m • v 0‖ ≤ δ := fun m => by
      rw [norm_smul, Real.norm_of_nonneg (hs0 m).le]
      have h1 : s m ≤ δ' := div_le_self hδ'0.le (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
      calc s m * ‖v 0‖ ≤ δ' * (‖v 0‖ + 1) := mul_le_mul h1 (by linarith) (norm_nonneg _) hδ'0.le
        _ = δ := by rw [hδ']; exact div_mul_cancel₀ δ (by positivity)
    -- approximants
    set Q : ℕ → Ψ → F := fun m ψ => (s m)⁻¹ • (iteratedFDeriv ℝ n (f ψ) (z + s m • v 0) (Fin.tail v) -
      iteratedFDeriv ℝ n (f ψ) z (Fin.tail v)) with hQ
    have hQc : ∀ m, Continuous (Q m) := fun m => by
      have hzm : z + s m • v 0 ∈ ball u ρ := by
        apply hδb
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
        exact hsv m
      exact ((ih _ hzm _).sub (ih z hz _)).const_smul _
    -- the error estimate
    have herr : ∀ m ψ, ‖iteratedFDeriv ℝ (n + 1) (f ψ) z v - Q m ψ‖ ≤ s m * (M2 * ‖v 0‖ ^ 2 * P) := by
      intro m ψ
      have hhδ : ‖s m • v 0‖ ≤ δ := hsv m
      have hball : closedBall z ‖s m • v 0‖ ⊆ ball u ρ := (closedBall_subset_closedBall hhδ).trans hδb
      have hlip : ∀ w ∈ closedBall z ‖s m • v 0‖, ‖fderiv ℝ (iteratedFDeriv ℝ n (f ψ)) w -
          fderiv ℝ (iteratedFDeriv ℝ n (f ψ)) z‖ ≤ M2 * ‖s m • v 0‖ := by
        intro w hw
        rw [fderiv_iteratedFDeriv, Function.comp_apply, Function.comp_apply, ← map_sub,
          LinearIsometryEquiv.norm_map]
        have hmv := (convex_closedBall z ‖s m • v 0‖).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (C := M2)
          (f := iteratedFDeriv ℝ (n + 1) (f ψ)) (fun y _ => (hdiff ψ (n + 1)) y)
          (fun y hy => by
            rw [norm_fderiv_iteratedFDeriv]
            exact (hM ψ (n + 2) y (hball hy)).trans (le_max_left _ _))
          (mem_closedBall_self (norm_nonneg _)) hw
        have hwz : ‖w - z‖ ≤ ‖s m • v 0‖ := by rw [← dist_eq_norm]; exact hw
        exact hmv.trans (mul_le_mul_of_nonneg_left hwz hM20)
      have hrem := (convex_closedBall z ‖s m • v 0‖).norm_image_sub_le_of_norm_fderiv_le'
        (f := iteratedFDeriv ℝ n (f ψ)) (φ := fderiv ℝ (iteratedFDeriv ℝ n (f ψ)) z)
        (fun y _ => (hdiff ψ n) y) hlip (mem_closedBall_self (norm_nonneg _))
        (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left])
      rw [add_sub_cancel_left] at hrem
      have hs' : (s m)⁻¹ * s m = 1 := inv_mul_cancel₀ (hs0 m).ne'
      have hid : iteratedFDeriv ℝ (n + 1) (f ψ) z v - Q m ψ =
          (-(s m)⁻¹) • ((iteratedFDeriv ℝ n (f ψ) (z + s m • v 0) - iteratedFDeriv ℝ n (f ψ) z -
            fderiv ℝ (iteratedFDeriv ℝ n (f ψ)) z (s m • v 0)) (Fin.tail v)) := by
        rw [iteratedFDeriv_succ_apply_left, sub_apply, sub_apply,
          map_smul, smul_apply]
        simp only [hQ, smul_sub, smul_smul, neg_mul, hs', neg_smul, one_smul]
        abel
      rw [hid, norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg (hs0 m).le]
      have hsne := (hs0 m).ne'
      calc (s m)⁻¹ * ‖(iteratedFDeriv ℝ n (f ψ) (z + s m • v 0) - iteratedFDeriv ℝ n (f ψ) z -
            fderiv ℝ (iteratedFDeriv ℝ n (f ψ)) z (s m • v 0)) (Fin.tail v)‖
          ≤ (s m)⁻¹ * (‖iteratedFDeriv ℝ n (f ψ) (z + s m • v 0) - iteratedFDeriv ℝ n (f ψ) z -
            fderiv ℝ (iteratedFDeriv ℝ n (f ψ)) z (s m • v 0)‖ * P) :=
            mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.le_opNorm _ _) (inv_nonneg.2 (hs0 m).le)
        _ ≤ (s m)⁻¹ * ((M2 * ‖s m • v 0‖ * ‖s m • v 0‖) * P) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrem hP0) (inv_nonneg.2 (hs0 m).le)
        _ = s m * (M2 * ‖v 0‖ ^ 2 * P) := by
            rw [norm_smul, Real.norm_of_nonneg (hs0 m).le]
            field_simp
    have hsT : Tendsto s atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ'
      rw [mul_zero] at this
      exact this.congr fun m => by simp only [hs]; ring
    have hU : TendstoUniformly Q (fun ψ => iteratedFDeriv ℝ (n + 1) (f ψ) z v) atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      have hev := (hsT.mul_const (M2 * ‖v 0‖ ^ 2 * P)).eventually
        (eventually_lt_nhds (show 0 * (M2 * ‖v 0‖ ^ 2 * P) < ε by rw [zero_mul]; exact hε))
      filter_upwards [hev] with m hm ψ
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (herr m ψ) hm
    exact hU.continuous (Eventually.of_forall hQc).frequently

end Generic

/-! ## Application to the product action (conditional on the held GP-04 clause) -/

section Action

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusFlow QuantumNLS.ProductTorusAction
  QuantumNLS.ProductTorusPrimitive QuantumNLS.ProductTorusAnalytic
open QuantumNLS.Ext025B6TorusCoordinates (Torus)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

variable {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)}

/-- **Uniform local operator bounds of all orders**: near each `u`, `‖D^k T_ψ(x)‖ ≤ k! C 2^{k+1}/r^k` for every `k`,
every `x ∈ B(u, r/2)` and every `ψ` in the product group. -/
theorem act_iteratedFDeriv_bound (H : PHyp I DI) (hDI : AnalyticOnNhd ℝ DI univ)
    (hGP04 : HeldGP04AnalyticInitialDependence E (E →L[ℝ] L1 ℝ)) (u : E) :
    ∃ r > (0 : ℝ), ∃ C : ℝ, ∀ (ψ : Torus) (k : ℕ), ∀ x ∈ ball u (r / 2),
      ‖iteratedFDeriv ℝ k (act DI ψ) x‖ ≤ k.factorial * (C * 2 ^ (k + 1) / r ^ k) := by
  obtain ⟨r, hr, C, hP⟩ := act_uniform_analytic H hDI hGP04 u
  refine ⟨r, hr, C, fun ψ k x hx => ?_⟩
  obtain ⟨p, hp, hpC⟩ := hP ψ
  have hy : ‖x - u‖ < r / 2 := by rw [← dist_eq_norm]; exact hx
  have := norm_iteratedFDeriv_near hr hp hpC hy k
  rwa [add_sub_cancel] at this

/-- **Fixed-vector parameter continuity of all orders**: `ψ ↦ D^n T_ψ(u)[v₁,…,vₙ]` is continuous on the product
torus for every `n`, `u` and fixed tangent vectors. -/
theorem act_iteratedFDeriv_continuous (H : PHyp I DI) (hDI : AnalyticOnNhd ℝ DI univ)
    (hGP04 : HeldGP04AnalyticInitialDependence E (E →L[ℝ] L1 ℝ)) (n : ℕ) (u : E) (v : Fin n → E) :
    Continuous (fun ψ : Torus => iteratedFDeriv ℝ n (act DI ψ) u v) := by
  obtain ⟨r, hr, C, hb⟩ := act_iteratedFDeriv_bound H hDI hGP04 u
  have hA : ∀ ψ, AnalyticOnNhd ℝ (act DI ψ) univ := fun ψ z _ => act_analyticAt H hDI hGP04 ψ z
  exact continuous_iteratedFDeriv_param (f := fun ψ => act DI ψ) (u := u) (ρ := r / 2)
    (fun ψ m => (hA ψ).contDiff) (fun k => k.factorial * (C * 2 ^ (k + 1) / r ^ k))
    (fun ψ k z hz => hb ψ k z hz) (fun z _ => continuous_act H z) n u (mem_ball_self (by positivity)) v

end Action

end QuantumNLS.ProductTorusAllOrders

#print axioms QuantumNLS.ProductTorusAllOrders.norm_changeOrigin_le_of_majorant
#print axioms QuantumNLS.ProductTorusAllOrders.norm_iteratedFDeriv_near
#print axioms QuantumNLS.ProductTorusAllOrders.continuous_iteratedFDeriv_param
#print axioms QuantumNLS.ProductTorusAllOrders.act_iteratedFDeriv_bound
#print axioms QuantumNLS.ProductTorusAllOrders.act_iteratedFDeriv_continuous
