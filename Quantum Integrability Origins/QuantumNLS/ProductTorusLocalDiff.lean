import QuantumNLS.Ext025A3Variational
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T2c: short-time differentiability of a `C¹` flow

Abstract real Banach constituent for the source's "The variational equation gives ..." and "Differentiating one
transported field along the other and using uniqueness of the linear variational equation" (product_torus.tex,
proof, "Bounded angle generators and complete flows", third–fifth paragraphs). It is *not* the held GP-04 clause
"path-space Picard derivative / fixed-point differential theorem": no Picard map on a path space is differentiated
and no fixed-point theorem is used. The route is the classical Gronwall argument.

Setting: `f : E → E` is `C¹`, and `φ : ℝ → E → E` is a family of global solutions,
`∂ₜ φ t v = f (φ t v)`, `φ 0 v = v` (the complete flows of stage T2b are an instance).

Main result, `local_diff`: for every `p` there are `ρ, τ > 0` such that for every `u ∈ B(p, ρ)` the operator-valued
variational solution `J' = Df(φ s u) J`, `J 0 = id` on `[0, τ]` (accepted GP-04 constituent
`Ext025A3.gp04_variational_existence`) is the Fréchet derivative: `HasFDerivAt (φ t) (J t) u` for `t ∈ [0, τ]`.

Proof (all constants constructed):
* `local_constants`: continuity of `f` and `Df` at `p` gives a closed ball `B̄(p,a)` with `‖Df‖ ≤ K`, `‖f‖ ≤ L`;
  `lipschitz_ball`: `f` is `K`-Lipschitz there (mean value inequality on the convex ball);
* `stays`: for `v ∈ B̄(p,a/2)` and `0 ≤ t ≤ τ`, `(L+1)τ ≤ a/2`, the trajectory stays in `B̄(p,a)` (fencing argument,
  mathlib `image_norm_le_of_norm_deriv_right_lt_deriv_boundary`; no a-priori membership is assumed);
* Gronwall for `‖φ s v − φ s u‖ ≤ ‖v − u‖ e^{Ks}`;
* `unif_near_compact`: `Df` is uniformly continuous at the compact path `φ([0,τ], u)` (Heine–Cantor at a compact set);
* the error `e(s) = φ s v − φ s u − J s (v − u)` has right derivative
  `[f(φ s v) − f(φ s u) − Df(φ s u)(φ s v − φ s u)] + Df(φ s u) e(s)`, so Gronwall gives `‖e(t)‖ ≤ c ‖v − u‖`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology Set Metric
open scoped NNReal

noncomputable section

namespace QuantumNLS.ProductTorusLocalDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Uniform continuity of a continuous map at a compact set. -/
theorem unif_near_compact {F : Type*} [PseudoMetricSpace F] {g : E → F} (hg : Continuous g) {S : Set E}
    (hS : IsCompact S) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ x ∈ S, ∀ z, dist z x < ρ → dist (g z) (g x) < ε := by
  have hU := hS.uniformContinuousAt_of_continuousAt g (fun x _ => hg.continuousAt)
    (Metric.dist_mem_uniformity hε)
  obtain ⟨ρ, hρ, H⟩ := Metric.mem_uniformity_dist.1 hU
  refine ⟨ρ, hρ, fun x hx z hz => ?_⟩
  have h1 := H (a := x) (b := z) (by rwa [dist_comm])
  simp only [Set.mem_ofPred_eq] at h1
  rw [dist_comm]
  exact h1 hx

omit [CompleteSpace E] in
/-- Local constants: a closed ball on which `‖Df‖ ≤ ‖Df(p)‖ + 1` and `‖f‖ ≤ ‖f(p)‖ + 1`. -/
theorem local_constants {f : E → E} (hf : ContDiff ℝ 1 f) (p : E) :
    ∃ a > (0 : ℝ), ∀ z ∈ closedBall p a,
      ‖fderiv ℝ f z‖ ≤ ‖fderiv ℝ f p‖ + 1 ∧ ‖f z‖ ≤ ‖f p‖ + 1 := by
  have hc1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hc0 : Continuous f := hf.continuous
  obtain ⟨a1, ha1, h1⟩ := (Metric.continuousAt_iff.1 (hc1.continuousAt (x := p))) 1 one_pos
  obtain ⟨a2, ha2, h2⟩ := (Metric.continuousAt_iff.1 (hc0.continuousAt (x := p))) 1 one_pos
  refine ⟨min a1 a2 / 2, by positivity, fun z hz => ?_⟩
  rw [mem_closedBall] at hz
  have hz1 : dist z p < a1 := by
    have := min_le_left a1 a2; linarith [half_lt_self (lt_min ha1 ha2)]
  have hz2 : dist z p < a2 := by
    have := min_le_right a1 a2; linarith [half_lt_self (lt_min ha1 ha2)]
  have e1 := h1 hz1
  have e2 := h2 hz2
  rw [dist_eq_norm] at e1 e2
  constructor
  · have := norm_sub_norm_le (fderiv ℝ f z) (fderiv ℝ f p); linarith
  · have := norm_sub_norm_le (f z) (f p); linarith

omit [CompleteSpace E] in
/-- `f` is `K`-Lipschitz on a closed ball where `‖Df‖ ≤ K`. -/
theorem lipschitz_ball {f : E → E} (hf : ContDiff ℝ 1 f) {p : E} {a : ℝ} {K : ℝ≥0}
    (hK : ∀ z ∈ closedBall p a, ‖fderiv ℝ f z‖ ≤ K) : LipschitzOnWith K f (closedBall p a) :=
  Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (fun z _ => hf.differentiable one_ne_zero z)
    (fun z hz => by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hK z hz) (convex_closedBall p a)

variable {f : E → E} {φ : ℝ → E → E}

omit [CompleteSpace E] in
/-- **Trajectories stay in the ball** for short times (fencing argument). -/
theorem stays (hφ : ∀ v t, HasDerivAt (fun t => φ t v) (f (φ t v)) t) (hφ0 : ∀ v, φ 0 v = v)
    {p : E} {a L τ : ℝ} (hL0 : 0 ≤ L) (hL : ∀ z ∈ closedBall p a, ‖f z‖ ≤ L) (hτ : (L + 1) * τ ≤ a / 2)
    {v : E} (hv : v ∈ closedBall p (a / 2)) {t : ℝ} (ht : t ∈ Icc 0 τ) : φ t v ∈ closedBall p a := by
  have hB : ∀ x, HasDerivAt (fun t : ℝ => a / 2 + (L + 1) * t) (L + 1) x := by
    intro x
    simpa using ((hasDerivAt_id x).const_mul (L + 1)).const_add (a / 2)
  have key := image_norm_le_of_norm_deriv_right_lt_deriv_boundary (a := 0) (b := τ)
    (f := fun t => φ t v - p) (f' := fun t => f (φ t v))
    (fun t _ => ((hφ v t).sub_const p).continuousAt.continuousWithinAt)
    (fun t _ => ((hφ v t).sub_const p).hasDerivWithinAt)
    (B := fun t => a / 2 + (L + 1) * t) (B' := fun _ => L + 1) ?_ hB ?_ ht
  · rw [mem_closedBall, dist_eq_norm]
    have k : ‖φ t v - p‖ ≤ a / 2 + (L + 1) * t := key
    have : (L + 1) * t ≤ (L + 1) * τ := mul_le_mul_of_nonneg_left ht.2 (by linarith)
    linarith
  · show ‖φ 0 v - p‖ ≤ a / 2 + (L + 1) * 0
    rw [hφ0, mul_zero, add_zero, ← dist_eq_norm]
    exact hv
  · intro x hx hx'
    have hx'' : ‖φ x v - p‖ = a / 2 + (L + 1) * x := hx'
    have hmem : φ x v ∈ closedBall p a := by
      rw [mem_closedBall, dist_eq_norm, hx'']
      have : (L + 1) * x ≤ (L + 1) * τ := mul_le_mul_of_nonneg_left hx.2.le (by linarith)
      linarith
    show ‖f (φ x v)‖ < L + 1
    exact (hL _ hmem).trans_lt (lt_add_one L)

/-- **Short-time differentiability of the flow**, with the variational solution as derivative. -/
theorem local_diff (hf : ContDiff ℝ 1 f) (hφ : ∀ v t, HasDerivAt (fun t => φ t v) (f (φ t v)) t)
    (hφ0 : ∀ v, φ 0 v = v) (p : E) :
    ∃ ρ > (0 : ℝ), ∃ τ > (0 : ℝ), ∀ u ∈ ball p ρ, ∃ J : ℝ → E →L[ℝ] E, Continuous J ∧
      J 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ s ∈ Icc 0 τ, HasDerivWithinAt J ((fderiv ℝ f (φ s u)).comp (J s)) (Icc 0 τ) s) ∧
      ∀ t ∈ Icc 0 τ, HasFDerivAt (φ t) (J t) u := by
  obtain ⟨a, ha, hloc⟩ := local_constants hf p
  set K : ℝ≥0 := ‖fderiv ℝ f p‖₊ + 1 with hKdef
  have hKr : (K : ℝ) = ‖fderiv ℝ f p‖ + 1 := by rw [hKdef, NNReal.coe_add, coe_nnnorm, NNReal.coe_one]
  have hK0 : (0 : ℝ) < K := by rw [hKr]; positivity
  set L : ℝ := ‖f p‖ + 1 with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hKb : ∀ z ∈ closedBall p a, ‖fderiv ℝ f z‖ ≤ K := fun z hz => by rw [hKr]; exact (hloc z hz).1
  have hLb : ∀ z ∈ closedBall p a, ‖f z‖ ≤ L := fun z hz => (hloc z hz).2
  have hLip : LipschitzOnWith K f (closedBall p a) := lipschitz_ball hf hKb
  set τ : ℝ := min (a / (4 * (L + 1))) (1 / (2 * K)) with hτdef
  have hτ0 : 0 < τ := lt_min (by positivity) (by positivity)
  have hτL : (L + 1) * τ ≤ a / 2 := by
    have h1 : τ ≤ a / (4 * (L + 1)) := min_le_left _ _
    have h2 : (L + 1) * τ ≤ (L + 1) * (a / (4 * (L + 1))) := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : (L + 1) * (a / (4 * (L + 1))) = a / 4 := by field_simp
    linarith
  have hτK : 2 * (K : ℝ) * τ ≤ 1 := by
    have h1 : τ ≤ 1 / (2 * K) := min_le_right _ _
    have h2 : 2 * (K : ℝ) * τ ≤ 2 * K * (1 / (2 * K)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 * (K : ℝ) * (1 / (2 * K)) = 1 := by field_simp
    linarith
  refine ⟨a / 4, by positivity, τ, hτ0, fun u hu => ?_⟩
  have hu2 : u ∈ closedBall p (a / 2) := by
    rw [mem_closedBall]; rw [mem_ball] at hu; linarith
  have hαc : Continuous (fun s => φ s u) := continuous_iff_continuousAt.2 fun s => (hφ u s).continuousAt
  have hαB : ∀ s ∈ Icc 0 τ, φ s u ∈ closedBall p a := fun s hs => stays hφ hφ0 hL0 hLb hτL hu2 hs
  have hAc : Continuous (fun s => fderiv ℝ f (φ s u)) := (hf.continuous_fderiv one_ne_zero).comp hαc
  have hAb : ∀ s ∈ Icc 0 τ, ‖(fun s => fderiv ℝ f (φ s u)) s‖ ≤ K := fun s hs => hKb _ (hαB s hs)
  obtain ⟨J, hJc, hJ0, -, hJd⟩ := QuantumNLS.Ext025A3.gp04_variational_existence (a := 0) (b := τ)
    (t₀ := ⟨0, le_rfl, hτ0.le⟩) (fun s => fderiv ℝ f (φ s u)) hAc.continuousOn K hAb (by
      show (2 * (K : ℝ)) * max (τ - 0) (0 - 0) ≤ 1
      rw [sub_zero, sub_self, max_eq_left hτ0.le]
      exact hτK)
  have hJ0' : J 0 = ContinuousLinearMap.id ℝ E := hJ0
  have hJd' : ∀ s ∈ Icc 0 τ, HasDerivWithinAt J ((fderiv ℝ f (φ s u)).comp (J s)) (Icc 0 τ) s := hJd
  refine ⟨J, hJc, hJ0', hJd', fun t ht => ?_⟩
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set M : ℝ := Real.exp (K * τ) with hM
  have hM0 : 0 < M := Real.exp_pos _
  set ε : ℝ := c * K / (M * M) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨ρ₁, hρ₁, hU⟩ := unif_near_compact (hf.continuous_fderiv one_ne_zero)
    ((isCompact_Icc (a := (0 : ℝ)) (b := τ)).image hαc) hε0
  have hnbhd : ball u (min (a / 4) (ρ₁ / M)) ∈ 𝓝 u := ball_mem_nhds u (by positivity)
  filter_upwards [hnbhd] with v hv
  rw [mem_ball] at hv
  have hv1 : dist v u < a / 4 := lt_of_lt_of_le hv (min_le_left _ _)
  have hv2 : dist v u < ρ₁ / M := lt_of_lt_of_le hv (min_le_right _ _)
  have hv' : v ∈ closedBall p (a / 2) := by
    rw [mem_closedBall]; rw [mem_ball] at hu
    have := dist_triangle v u p; linarith
  have hβc : Continuous (fun s => φ s v) := continuous_iff_continuousAt.2 fun s => (hφ v s).continuousAt
  have hβB : ∀ s ∈ Icc 0 τ, φ s v ∈ closedBall p a := fun s hs => stays hφ hφ0 hL0 hLb hτL hv' hs
  -- Gronwall for the distance
  have hdist := dist_le_of_trajectories_ODE_of_mem (v := fun _ => f) (s := fun _ => closedBall p a) (K := K)
    (f := fun s => φ s v) (g := fun s => φ s u) (a := 0) (b := τ) (δ := dist v u)
    (fun _ _ => hLip) hβc.continuousOn (fun s _ => (hφ v s).hasDerivWithinAt)
    (fun s hs => hβB s (Ico_subset_Icc_self hs)) hαc.continuousOn (fun s _ => (hφ u s).hasDerivWithinAt)
    (fun s hs => hαB s (Ico_subset_Icc_self hs))
    (by show dist (φ 0 v) (φ 0 u) ≤ dist v u; rw [hφ0, hφ0])
  have hβα : ∀ s ∈ Icc 0 τ, ‖φ s v - φ s u‖ ≤ ‖v - u‖ * M := by
    intro s hs
    have h1 : dist (φ s v) (φ s u) ≤ dist v u * Real.exp (K * (s - 0)) := hdist s hs
    rw [dist_eq_norm, dist_eq_norm, sub_zero] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left hs.2 hK0.le
  -- the error function
  have he_cont : ContinuousOn (fun s => φ s v - φ s u - J s (v - u)) (Icc 0 t) :=
    ((hβc.sub hαc).sub (hJc.clm_apply continuous_const)).continuousOn
  have he_der : ∀ s ∈ Ico 0 t, HasDerivWithinAt (fun s => φ s v - φ s u - J s (v - u))
      (f (φ s v) - f (φ s u) - fderiv ℝ f (φ s u) (J s (v - u))) (Ici s) s := by
    intro s hs
    have hsτ : s < τ := lt_of_lt_of_le hs.2 ht.2
    have hJs : HasDerivWithinAt J ((fderiv ℝ f (φ s u)).comp (J s)) (Ici s) s := by
      have h1 := (hJd' s ⟨hs.1, hsτ.le⟩).mono
        (show Ici s ∩ Iio τ ⊆ Icc 0 τ from fun x hx => ⟨hs.1.trans hx.1, (mem_Iio.1 hx.2).le⟩)
      exact (hasDerivWithinAt_inter (Iio_mem_nhds hsτ)).1 h1
    have hJh := hJs.clm_apply (hasDerivWithinAt_const s (Ici s) (v - u))
    have h3 := ((hφ v s).hasDerivWithinAt.sub (hφ u s).hasDerivWithinAt).sub hJh
    convert h3 using 1
    simp
  have hbound : ∀ s ∈ Ico 0 t, ‖f (φ s v) - f (φ s u) - fderiv ℝ f (φ s u) (J s (v - u))‖ ≤
      K * ‖φ s v - φ s u - J s (v - u)‖ + ε * (‖v - u‖ * M) := by
    intro s hs
    have hsI : s ∈ Icc 0 τ := ⟨hs.1, (hs.2.trans_le ht.2).le⟩
    have hd : dist (φ s v) (φ s u) < ρ₁ := by
      rw [dist_eq_norm]
      have h1 : ‖v - u‖ < ρ₁ / M := by rw [← dist_eq_norm]; exact hv2
      rw [lt_div_iff₀ hM0] at h1
      exact lt_of_le_of_lt (hβα s hsI) h1
    have hrem : ‖f (φ s v) - f (φ s u) - fderiv ℝ f (φ s u) (φ s v - φ s u)‖ ≤ ε * ‖φ s v - φ s u‖ := by
      refine Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (s := ball (φ s u) ρ₁)
        (fun z _ => hf.differentiable one_ne_zero z) (fun z hz => ?_) (convex_ball _ _) (mem_ball_self hρ₁)
        (by rw [mem_ball]; exact hd)
      have h1 := hU (φ s u) ⟨s, hsI, rfl⟩ z (mem_ball.1 hz)
      rw [dist_eq_norm] at h1
      exact h1.le
    have hsplit : f (φ s v) - f (φ s u) - fderiv ℝ f (φ s u) (J s (v - u)) =
        (f (φ s v) - f (φ s u) - fderiv ℝ f (φ s u) (φ s v - φ s u)) +
          fderiv ℝ f (φ s u) (φ s v - φ s u - J s (v - u)) := by
      simp only [map_sub]; abel
    rw [hsplit]
    have hlin : ‖fderiv ℝ f (φ s u) (φ s v - φ s u - J s (v - u))‖ ≤ K * ‖φ s v - φ s u - J s (v - u)‖ :=
      ((fderiv ℝ f (φ s u)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hKb _ (hαB s hsI)) (norm_nonneg _))
    have hεm : ε * ‖φ s v - φ s u‖ ≤ ε * (‖v - u‖ * M) := mul_le_mul_of_nonneg_left (hβα s hsI) hε0.le
    calc _ ≤ ‖f (φ s v) - f (φ s u) - fderiv ℝ f (φ s u) (φ s v - φ s u)‖ +
          ‖fderiv ℝ f (φ s u) (φ s v - φ s u - J s (v - u))‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (a := 0) (b := t) (K := K)
    (f := fun s => φ s v - φ s u - J s (v - u))
    (f' := fun s => f (φ s v) - f (φ s u) - fderiv ℝ f (φ s u) (J s (v - u)))
    he_cont he_der
    (by
      show ‖φ 0 v - φ 0 u - J 0 (v - u)‖ ≤ 0
      rw [hφ0, hφ0, hJ0']
      simp)
    hbound t ⟨ht.1, le_rfl⟩
  have hexp : Real.exp (K * t) - 1 ≤ M := by
    have : Real.exp (K * t) ≤ M := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hK0.le)
    linarith
  have hg' : ‖φ t v - φ t u - J t (v - u)‖ ≤ ε * (‖v - u‖ * M) / K * (Real.exp (K * t) - 1) := by
    have h1 : ‖φ t v - φ t u - J t (v - u)‖ ≤ gronwallBound 0 K (ε * (‖v - u‖ * M)) (t - 0) := hg
    rw [gronwallBound_of_K_ne_0 hK0.ne'] at h1
    simpa only [zero_mul, zero_add, sub_zero] using h1
  calc ‖φ t v - φ t u - J t (v - u)‖ ≤ ε * (‖v - u‖ * M) / K * (Real.exp (K * t) - 1) := hg'
    _ ≤ ε * (‖v - u‖ * M) / K * M := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = c * ‖v - u‖ := by
      rw [hε]
      field_simp

end QuantumNLS.ProductTorusLocalDiff

#print axioms QuantumNLS.ProductTorusLocalDiff.unif_near_compact
#print axioms QuantumNLS.ProductTorusLocalDiff.stays
#print axioms QuantumNLS.ProductTorusLocalDiff.local_diff
