import QuantumNLS.ProductTorusLocalDiff

/-!
# `thm:reset-moser` (LOCAL-017), stage 2b-i: short-time differentiability of a flow of a `C¹` field defined on an open set

Abstract real Banach constituent for the source's "Differentiating ... by the full variational equation" steps of
`symplectic_correction.tex` (the periods subsection: "For a tangent direction `h`, variation of the integral of a one-form along
this loop", and the flow bounds "The full variational equation and Gronwall's inequality give ..."), for flows that are only
defined, and only `C¹`, on an open set `U` (the ball `B_R` of `thm:reset-moser`).

This is the ball-version of the frozen (read-only) `ProductTorusLocalDiff.local_diff`, which needs a *global* `C¹` field and
*global* solutions: here `f` is `C¹` on the open set `U`, and `φ` is a family of solutions for initial points in `U` only. The proof
is the same Gronwall argument (accepted GP-04 variational existence `Ext025A3.gp04_variational_existence`, mathlib's fencing
inequality and Gronwall), with all balls taken inside `U`.

* `FlowOn f φ U`: the hypotheses (`U` open, `f` is `C¹` on `U`, `φ` solves `∂ₜφ = f ∘ φ` for initial points of `U` for all real `t`,
  stays in `U`, `φ 0 = id`);
* `local_diff_on`: for `p ∈ U` there are `ρ, τ > 0` such that for `u ∈ B(p,ρ)` the variational solution
  `J' = Df(φ s u) J`, `J 0 = id` on `[0,τ]` is the Fréchet derivative: `HasFDerivAt (φ t) (J t) u` for `t ∈ [0,τ]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Filter Topology Set Metric
open scoped NNReal

noncomputable section

namespace QuantumNLS.ResetMoserFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Hypotheses on a flow of a field `f` on an open set `U`. -/
structure FlowOn (f : E → E) (φ : ℝ → E → E) (U : Set E) : Prop where
  isOpen : IsOpen U
  cd : ContDiffOn ℝ 1 f U
  deriv : ∀ v ∈ U, ∀ t, HasDerivAt (fun s => φ s v) (f (φ t v)) t
  mem : ∀ v ∈ U, ∀ t, φ t v ∈ U
  zero : ∀ v ∈ U, φ 0 v = v

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem unif_near_compact_on {F : Type*} [PseudoMetricSpace F] {g : E → F} {S : Set E}
    (hS : IsCompact S) (hg : ∀ x ∈ S, ContinuousAt g x) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ x ∈ S, ∀ z, dist z x < ρ → dist (g z) (g x) < ε := by
  have hU := hS.uniformContinuousAt_of_continuousAt g hg (Metric.dist_mem_uniformity hε)
  obtain ⟨ρ, hρ, H⟩ := Metric.mem_uniformity_dist.1 hU
  refine ⟨ρ, hρ, fun x hx z hz => ?_⟩
  have h1 := H (a := x) (b := z) (by rwa [dist_comm])
  simp only [Set.mem_ofPred_eq] at h1
  rw [dist_comm]
  exact h1 hx

omit [CompleteSpace E] in
theorem local_constants_on {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) {p : E}
    (hp : p ∈ U) :
    ∃ a > (0 : ℝ), closedBall p (2 * a) ⊆ U ∧ ∀ z ∈ closedBall p a,
      ‖fderiv ℝ f z‖ ≤ ‖fderiv ℝ f p‖ + 1 ∧ ‖f z‖ ≤ ‖f p‖ + 1 := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU p hp
  have hc1 : ContinuousAt (fderiv ℝ f) p :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hp)
  have hc0 : ContinuousAt f p := hf.continuousOn.continuousAt (hU.mem_nhds hp)
  obtain ⟨a1, ha1, h1⟩ := (Metric.continuousAt_iff.1 hc1) 1 one_pos
  obtain ⟨a2, ha2, h2⟩ := (Metric.continuousAt_iff.1 hc0) 1 one_pos
  have hm : 0 < min (min a1 a2) (ε / 4) := lt_min (lt_min ha1 ha2) (by positivity)
  refine ⟨min (min a1 a2) (ε / 4) / 2, by positivity, ?_, fun z hz => ?_⟩
  · intro y hy
    apply hεU
    rw [mem_closedBall] at hy
    rw [mem_ball]
    have : min (min a1 a2) (ε / 4) ≤ ε / 4 := min_le_right _ _
    linarith
  · rw [mem_closedBall] at hz
    have hz1 : dist z p < a1 := by
      have h := min_le_left (min a1 a2) (ε / 4); have h' := min_le_left a1 a2; linarith
    have hz2 : dist z p < a2 := by
      have h := min_le_left (min a1 a2) (ε / 4); have h' := min_le_right a1 a2; linarith
    have e1 := h1 hz1
    have e2 := h2 hz2
    rw [dist_eq_norm] at e1 e2
    constructor
    · have := norm_sub_norm_le (fderiv ℝ f z) (fderiv ℝ f p); linarith
    · have := norm_sub_norm_le (f z) (f p); linarith

variable {f : E → E} {φ : ℝ → E → E}

omit [CompleteSpace E] in
/-- Trajectories starting in `closedBall p (a/2)` stay in `closedBall p a` for short times (fencing argument). -/
theorem stays_on {p : E} {a L τ : ℝ}
    (hφ : ∀ v ∈ closedBall p (a / 2), ∀ t, HasDerivAt (fun t => φ t v) (f (φ t v)) t)
    (hφ0 : ∀ v ∈ closedBall p (a / 2), φ 0 v = v) (hL0 : 0 ≤ L) (hL : ∀ z ∈ closedBall p a, ‖f z‖ ≤ L) (hτ : (L + 1) * τ ≤ a / 2)
    {v : E} (hv : v ∈ closedBall p (a / 2)) {t : ℝ} (ht : t ∈ Icc 0 τ) : φ t v ∈ closedBall p a := by
  have hB : ∀ x, HasDerivAt (fun t : ℝ => a / 2 + (L + 1) * t) (L + 1) x := by
    intro x
    simpa using ((hasDerivAt_id x).const_mul (L + 1)).const_add (a / 2)
  have key := image_norm_le_of_norm_deriv_right_lt_deriv_boundary (a := 0) (b := τ)
    (f := fun t => φ t v - p) (f' := fun t => f (φ t v))
    (fun t _ => ((hφ v hv t).sub_const p).continuousAt.continuousWithinAt)
    (fun t _ => ((hφ v hv t).sub_const p).hasDerivWithinAt)
    (B := fun t => a / 2 + (L + 1) * t) (B' := fun _ => L + 1) ?_ hB ?_ ht
  · rw [mem_closedBall, dist_eq_norm]
    have k : ‖φ t v - p‖ ≤ a / 2 + (L + 1) * t := key
    have : (L + 1) * t ≤ (L + 1) * τ := mul_le_mul_of_nonneg_left ht.2 (by linarith)
    linarith
  · show ‖φ 0 v - p‖ ≤ a / 2 + (L + 1) * 0
    rw [hφ0 v hv, mul_zero, add_zero, ← dist_eq_norm]
    exact hv
  · intro x hx hx'
    have hx'' : ‖φ x v - p‖ = a / 2 + (L + 1) * x := hx'
    have hmem : φ x v ∈ closedBall p a := by
      rw [mem_closedBall, dist_eq_norm, hx'']
      have : (L + 1) * x ≤ (L + 1) * τ := mul_le_mul_of_nonneg_left hx.2.le (by linarith)
      linarith
    show ‖f (φ x v)‖ < L + 1
    exact (hL _ hmem).trans_lt (lt_add_one L)

/-- **Short-time differentiability of the flow on an open set**, with the variational solution as derivative. -/
theorem local_diff_on {U : Set E} (H : FlowOn f φ U) {p : E} (hp : p ∈ U) :
    ∃ ρ > (0 : ℝ), ∃ τ > (0 : ℝ), ∀ u ∈ ball p ρ, ∃ J : ℝ → E →L[ℝ] E, Continuous J ∧
      J 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ s ∈ Icc 0 τ, HasDerivWithinAt J ((fderiv ℝ f (φ s u)).comp (J s)) (Icc 0 τ) s) ∧
      ∀ t ∈ Icc 0 τ, HasFDerivAt (φ t) (J t) u := by
  obtain ⟨a, ha, hUa, hloc⟩ := local_constants_on H.isOpen H.cd hp
  have hcl : closedBall p a ⊆ U := fun z hz => hUa (closedBall_subset_closedBall (by linarith) hz)
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ f x := fun x hx =>
    (H.cd.differentiableOn one_ne_zero).differentiableAt (H.isOpen.mem_nhds hx)
  have hcf : ContinuousOn (fderiv ℝ f) U := H.cd.continuousOn_fderiv_of_isOpen H.isOpen le_rfl
  set K : ℝ≥0 := ‖fderiv ℝ f p‖₊ + 1 with hKdef
  have hKr : (K : ℝ) = ‖fderiv ℝ f p‖ + 1 := by rw [hKdef, NNReal.coe_add, coe_nnnorm, NNReal.coe_one]
  have hK0 : (0 : ℝ) < K := by rw [hKr]; positivity
  set L : ℝ := ‖f p‖ + 1 with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hKb : ∀ z ∈ closedBall p a, ‖fderiv ℝ f z‖ ≤ K := fun z hz => by rw [hKr]; exact (hloc z hz).1
  have hLb : ∀ z ∈ closedBall p a, ‖f z‖ ≤ L := fun z hz => (hloc z hz).2
  have hLip : LipschitzOnWith K f (closedBall p a) :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (fun z hz => hdiff z (hcl hz))
      (fun z hz => by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hKb z hz) (convex_closedBall p a)
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
  have hφ' : ∀ v ∈ closedBall p (a / 2), ∀ t, HasDerivAt (fun t => φ t v) (f (φ t v)) t :=
    fun v hv t => H.deriv v (hcl (closedBall_subset_closedBall (by linarith) hv)) t
  have hφ0' : ∀ v ∈ closedBall p (a / 2), φ 0 v = v :=
    fun v hv => H.zero v (hcl (closedBall_subset_closedBall (by linarith) hv))
  refine ⟨a / 4, by positivity, τ, hτ0, fun u hu => ?_⟩
  have hu2 : u ∈ closedBall p (a / 2) := by
    rw [mem_closedBall]; rw [mem_ball] at hu; linarith
  have huU : u ∈ U := hcl (closedBall_subset_closedBall (by linarith) hu2)
  have hαc : Continuous (fun s => φ s u) :=
    continuous_iff_continuousAt.2 fun s => (H.deriv u huU s).continuousAt
  have hαB : ∀ s ∈ Icc 0 τ, φ s u ∈ closedBall p a := fun s hs =>
    stays_on hφ' hφ0' hL0 hLb hτL hu2 hs
  have hAc : Continuous (fun s => fderiv ℝ f (φ s u)) :=
    hcf.comp_continuous hαc (fun s => H.mem u huU s)
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
  obtain ⟨ρ₁, hρ₁, hUc⟩ := unif_near_compact_on (g := fderiv ℝ f)
    ((isCompact_Icc (a := (0 : ℝ)) (b := τ)).image hαc)
    (by
      rintro x ⟨s, -, rfl⟩
      exact hcf.continuousAt (H.isOpen.mem_nhds (H.mem u huU s))) hε0
  set ρ₂ : ℝ := min ρ₁ a with hρ₂
  have hρ₂0 : 0 < ρ₂ := lt_min hρ₁ ha
  have hnbhd : ball u (min (a / 4) (ρ₂ / M)) ∈ 𝓝 u := ball_mem_nhds u (by positivity)
  filter_upwards [hnbhd] with v hv
  rw [mem_ball] at hv
  have hv1 : dist v u < a / 4 := lt_of_lt_of_le hv (min_le_left _ _)
  have hv2 : dist v u < ρ₂ / M := lt_of_lt_of_le hv (min_le_right _ _)
  have hv' : v ∈ closedBall p (a / 2) := by
    rw [mem_closedBall]; rw [mem_ball] at hu
    have := dist_triangle v u p; linarith
  have hvU : v ∈ U := hcl (closedBall_subset_closedBall (by linarith) hv')
  have hβc : Continuous (fun s => φ s v) :=
    continuous_iff_continuousAt.2 fun s => (H.deriv v hvU s).continuousAt
  have hβB : ∀ s ∈ Icc 0 τ, φ s v ∈ closedBall p a := fun s hs =>
    stays_on hφ' hφ0' hL0 hLb hτL hv' hs
  -- Gronwall for the distance
  have hdist := dist_le_of_trajectories_ODE_of_mem (v := fun _ => f) (s := fun _ => closedBall p a) (K := K)
    (f := fun s => φ s v) (g := fun s => φ s u) (a := 0) (b := τ) (δ := dist v u)
    (fun _ _ => hLip) hβc.continuousOn (fun s _ => (H.deriv v hvU s).hasDerivWithinAt)
    (fun s hs => hβB s (Ico_subset_Icc_self hs)) hαc.continuousOn
    (fun s _ => (H.deriv u huU s).hasDerivWithinAt)
    (fun s hs => hαB s (Ico_subset_Icc_self hs))
    (by show dist (φ 0 v) (φ 0 u) ≤ dist v u; rw [H.zero v hvU, H.zero u huU])
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
    have h3 := ((H.deriv v hvU s).hasDerivWithinAt.sub (H.deriv u huU s).hasDerivWithinAt).sub hJh
    convert h3 using 1
    simp
  have hbound : ∀ s ∈ Ico 0 t, ‖f (φ s v) - f (φ s u) - fderiv ℝ f (φ s u) (J s (v - u))‖ ≤
      K * ‖φ s v - φ s u - J s (v - u)‖ + ε * (‖v - u‖ * M) := by
    intro s hs
    have hsI : s ∈ Icc 0 τ := ⟨hs.1, (hs.2.trans_le ht.2).le⟩
    have hd : dist (φ s v) (φ s u) < ρ₂ := by
      rw [dist_eq_norm]
      have h1 : ‖v - u‖ < ρ₂ / M := by rw [← dist_eq_norm]; exact hv2
      rw [lt_div_iff₀ hM0] at h1
      exact lt_of_le_of_lt (hβα s hsI) h1
    have hball : ball (φ s u) ρ₂ ⊆ U := fun z hz => by
      apply hUa
      rw [mem_closedBall]
      have h1 := mem_ball.1 hz
      have h2 : dist (φ s u) p ≤ a := mem_closedBall.1 (hαB s hsI)
      have h3 : ρ₂ ≤ a := min_le_right _ _
      have := dist_triangle z (φ s u) p
      linarith
    have hrem : ‖f (φ s v) - f (φ s u) - fderiv ℝ f (φ s u) (φ s v - φ s u)‖ ≤ ε * ‖φ s v - φ s u‖ := by
      refine Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (s := ball (φ s u) ρ₂)
        (fun z hz => hdiff z (hball hz)) (fun z hz => ?_) (convex_ball _ _) (mem_ball_self hρ₂0)
        (by rw [mem_ball]; exact hd)
      have h1 := hUc (φ s u) ⟨s, hsI, rfl⟩ z (lt_of_lt_of_le (mem_ball.1 hz) (min_le_left _ _))
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
      rw [H.zero v hvU, H.zero u huU, hJ0']
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

end QuantumNLS.ResetMoserFlow

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoserFlow.local_diff_on
