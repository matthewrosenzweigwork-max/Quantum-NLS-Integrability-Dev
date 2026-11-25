import QuantumNLS.Ext025A4HeldDependence

/-! Holomorphic Picard convergence for continuous real time and a common complex
state neighborhood. The time interval is normalized to [0,1]. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Set Metric Filter Topology
open scoped NNReal
namespace QuantumNLS.Ext025GP04AnalyticR30m
open Ext025A4AnalyticIntegral
open Ext025A4AnalyticPicard (analytic_fixedPoint)
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def substitute (G : Time × E → E) (hG : Continuous G) (v : Path E) : Path E :=
  ⟨fun t => G (t, v t), hG.comp (continuous_id.prodMk v.continuous)⟩

private theorem derivative_path {G : Time × E → E} (hG : Continuous G)
    {a : E} {R Λ : ℝ}
    (hd : ∀ t, DifferentiableOn ℂ (fun x => G (t,x)) (ball a R)) (hΛ : 0 ≤ Λ)
    (hl : ∀ t x, x ∈ ball a R → ∀ y, y ∈ ball a R →
      ‖fderiv ℂ (fun z => G (t,z)) x - fderiv ℂ (fun z => G (t,z)) y‖ ≤ Λ * ‖x-y‖)
    (v : Path E) (hv : v ∈ ball (ContinuousMap.const Time a) R) :
    DifferentiableAt ℂ (substitute G hG) v := by
  have hvn : ‖v - ContinuousMap.const Time a‖ < R := by simpa only [mem_ball, dist_eq_norm] using hv
  let B : Time → E →L[ℂ] E := fun t => fderiv ℂ (fun x => G (t,x)) (v t)
  have hvb (t : Time) : v t ∈ ball a R := by
    rw [mem_ball, dist_eq_norm]
    exact ((v - ContinuousMap.const Time a).norm_coe_le_norm t).trans_lt hvn
  have nearby (w : Path E) (hw : ‖w‖ < R - ‖v - ContinuousMap.const Time a‖) (t : Time) :
      v t + w t ∈ ball a R := by
    rw [mem_ball, dist_eq_norm]
    calc ‖v t + w t - a‖ = ‖(v t - a) + w t‖ := by congr 1; abel
      _ ≤ ‖v - ContinuousMap.const Time a‖ + ‖w‖ :=
        (norm_add_le _ _).trans (add_le_add ((v - ContinuousMap.const Time a).norm_coe_le_norm t)
          (w.norm_coe_le_norm t))
      _ < R := by linarith
  have rem (w : Path E) (hw : ‖w‖ < R - ‖v - ContinuousMap.const Time a‖) (t : Time) :
      ‖G (t,v t + w t) - G (t,v t) - B t (w t)‖ ≤ Λ * ‖w t‖ ^ 2 :=
    HolomorphicStageB1.norm_sub_sub_fderiv_le isOpen_ball (hd t) (subset_refl _)
      (convex_ball a R) hΛ (hl t) (hvb t) (nearby w hw t)
  have hB (w : Path E) : Continuous (fun t => B t (w t)) := by
    let q : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
    have hq0 (n : ℕ) : 0 < q n := by dsimp [q]; positivity
    have hq : Tendsto q atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    let Q : ℕ → Time → E := fun n t =>
      (q n : ℂ)⁻¹ • (G (t,v t + (q n : ℂ) • w t) - G (t,v t))
    have hu : TendstoUniformly Q (fun t => B t (w t)) atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      have hqv : Tendsto (fun n => q n * ‖w‖) atTop (𝓝 0) := by simpa using hq.mul_const ‖w‖
      have hqe : Tendsto (fun n => Λ * q n * ‖w‖ ^ 2) atTop (𝓝 0) := by
        simpa using (hq.const_mul Λ).mul_const (‖w‖ ^ 2)
      filter_upwards [hqv.eventually (gt_mem_nhds (sub_pos.mpr hvn)),
        hqe.eventually (gt_mem_nhds hε)] with n hn hn' t
      have hcn : (q n : ℂ) ≠ 0 := by exact_mod_cast (hq0 n).ne'
      have hrem := rem ((q n : ℂ) • w) (by
        rwa [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hq0 n)]) t
      have he : Q n t - B t (w t) =
          (q n : ℂ)⁻¹ • (G (t,v t + (q n : ℂ) • w t) - G (t,v t) -
            B t ((q n : ℂ) • w t)) := by
        simp only [Q, map_smul, smul_sub, smul_smul, inv_mul_cancel₀ hcn, one_smul]
      rw [dist_comm, dist_eq_norm, he, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (hq0 n)]
      change ‖_‖ ≤ Λ * ‖(q n : ℂ) • w t‖ ^ 2 at hrem
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hq0 n)] at hrem
      refine (mul_le_mul_of_nonneg_left hrem (inv_nonneg.mpr (hq0 n).le)).trans_lt ?_
      calc (q n)⁻¹ * (Λ * (q n * ‖w t‖) ^ 2) = Λ * q n * ‖w t‖ ^ 2 := by
            field_simp
        _ ≤ Λ * q n * ‖w‖ ^ 2 := by gcongr; exact w.norm_coe_le_norm t
        _ < ε := hn'
    apply hu.continuous
    exact (Eventually.of_forall (fun n : ℕ => show Continuous (Q n) from by
      have hwc := v.continuous.add (w.continuous.const_smul (q n : ℂ))
      exact ((hG.comp (continuous_id.prodMk hwc)).sub
        (hG.comp (continuous_id.prodMk v.continuous))).const_smul ((q n : ℂ)⁻¹))).frequently
  -- The derivative is bounded pointwise on the smaller ball by Cauchy's estimate.
  have hBbound (K : ℝ) (hK : 0 ≤ K) (hb : ∀ t, ‖B t‖ ≤ K) :
      ∃ D : Path E →L[ℂ] Path E, ∀ w t, D w t = B t (w t) := by
    refine ⟨LinearMap.mkContinuous {
      toFun := fun w => ⟨fun t => B t (w t), hB w⟩
      map_add' := fun w z => by ext t; exact map_add (B t) (w t) (z t)
      map_smul' := fun c w => by ext t; exact map_smul (B t) c (w t) } K ?_, fun _ _ => rfl⟩
    intro w
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    exact ((B t).le_opNorm (w t)).trans (mul_le_mul (hb t) (w.norm_coe_le_norm t) (norm_nonneg _) hK)
  suffices hBound : ∃ K ≥ (0 : ℝ), ∀ t, ‖B t‖ ≤ K by
    obtain ⟨K, hK, hb⟩ := hBound
    obtain ⟨D, hD⟩ := hBbound K hK hb
    suffices h : HasFDerivAt (substitute G hG) D v from h.differentiableAt
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro ε hε
    let δ := min (R - ‖v - ContinuousMap.const Time a‖) (ε / (Λ + 1))
    have hδ : 0 < δ := lt_min (sub_pos.mpr hvn) (div_pos hε (by positivity))
    filter_upwards [ball_mem_nhds (0 : Path E) hδ] with w hw
    have hw' : ‖w‖ < δ := by simpa only [mem_ball, dist_zero_right] using hw
    have hw₁ := hw'.trans_le (min_le_left _ _)
    have hw₂ := (lt_div_iff₀ (show 0 < Λ + 1 by positivity)).mp (hw'.trans_le (min_le_right _ _))
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    change ‖G (t,v t + w t) - G (t,v t) - D w t‖ ≤ ε * ‖w‖
    rw [hD]
    calc _ ≤ Λ * ‖w t‖ ^ 2 := rem w hw₁ t
      _ ≤ Λ * ‖w‖ ^ 2 := by gcongr; exact w.norm_coe_le_norm t
      _ ≤ ε * ‖w‖ := by nlinarith [mul_nonneg (norm_nonneg w) (sub_nonneg.mpr hw₂.le)]
  have hcont (w : E) : Continuous (fun t => B t w) := hB (ContinuousMap.const Time w)
  have hpoint (w : E) : ∃ C, ∀ t, ‖B t w‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_range (hcont w)).isBounded.subset_closedBall (0 : E)
    exact ⟨C, fun t => mem_closedBall_zero_iff.mp (hC ⟨t, rfl⟩)⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hpoint
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩

/-- The parameterized complex Picard operator uses the literal time integral.
The bounds hold on one common complex state ball for every real time. -/
theorem complex_picard {G : Time × E → E} (hG : Continuous G)
    {a : E} {r R δ M Λ : ℝ} (T K : ℝ≥0) (hr : 0 ≤ r) (hrR : r < R)
    (hd : ∀ t, DifferentiableOn ℂ (fun x => G (t,x)) (ball a R)) (hΛ : 0 ≤ Λ)
    (hl : ∀ t x, x ∈ ball a R → ∀ y, y ∈ ball a R →
      ‖fderiv ℂ (fun z => G (t,z)) x - fderiv ℂ (fun z => G (t,z)) y‖ ≤ Λ * ‖x-y‖)
    (hM : ∀ t y, y ∈ closedBall a r → ‖G (t,y)‖ ≤ M)
    (hK : ∀ t, LipschitzOnWith K (fun x => G (t,x)) (closedBall a r))
    (hsize : δ + (T : ℝ) * M ≤ r) (hshort : T*K < 1) :
    ∃ g : E → Path E, AnalyticOnNhd ℂ g (ball a δ) ∧
      ∀ x ∈ ball a δ, g x ∈ closedBall (ContinuousMap.const Time a) r ∧
        (∀ t : Time, g x t = x + (T : ℂ) • ∫ s in (0 : ℝ)..(t : ℝ), extend (substitute G hG (g x)) s) ∧
        ∀ v ∈ closedBall (ContinuousMap.const Time a) r,
          (∀ t : Time, v t = x + (T : ℂ) • ∫ s in (0 : ℝ)..(t : ℝ), extend (substitute G hG v) s) →
          v = g x := by
  let p : E × Path E → Path E := fun q =>
    ContinuousMap.const Time q.1 + (T : ℂ) • primitive (substitute G hG q.2)
  have hpd : DifferentiableOn ℂ p (ball a δ ×ˢ ball (ContinuousMap.const Time a) R) := by
    intro q hq
    have h₁ : DifferentiableAt ℂ (fun q : E × Path E => ContinuousMap.const Time q.1) q :=
      (ContinuousLinearMap.const Time (R := ℂ) (M := E)).differentiableAt.comp q differentiableAt_fst
    have h₂ := (primitive (E := E)).differentiableAt.comp q
      ((derivative_path hG hd hΛ hl q.2 hq.2).comp q differentiableAt_snd)
    exact (h₁.add (h₂.const_smul (T : ℂ))).differentiableWithinAt
  have hmaps (x : E) (hx : x ∈ ball a δ) (v : Path E)
      (hv : v ∈ closedBall (ContinuousMap.const Time a) r) :
      p (x,v) ∈ closedBall (ContinuousMap.const Time a) r := by
    rw [mem_closedBall, dist_eq_norm]
    have hb : ‖substitute G hG v‖ ≤ M :=
      (ContinuousMap.norm_le_of_nonempty _).mpr fun t => hM t _ (path_mem hv t)
    apply (ContinuousMap.norm_le _ hr).mpr
    intro t
    change ‖x + (T : ℂ) • primitive (substitute G hG v) t - a‖ ≤ r
    calc _ = ‖(x-a) + (T : ℂ) • primitive (substitute G hG v) t‖ := by congr 1; abel
      _ ≤ ‖x-a‖ + ‖(T : ℂ) • primitive (substitute G hG v) t‖ := norm_add_le _ _
      _ = ‖x-a‖ + (T : ℝ) * ‖primitive (substitute G hG v) t‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg T.coe_nonneg]
      _ ≤ δ + (T : ℝ)*M := by
        gcongr
        · exact (show ‖x - a‖ < δ by simpa only [mem_ball, dist_eq_norm] using hx).le
        · exact ((primitive (substitute G hG v)).norm_coe_le_norm t).trans ((primitivePath_norm _).trans hb)
      _ ≤ r := hsize
  have hpl (x : E) : LipschitzOnWith (T*K) (fun v => p (x,v))
      (closedBall (ContinuousMap.const Time a) r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro v hv w hw
    have hb : ‖substitute G hG v - substitute G hG w‖ ≤ (K : ℝ) * ‖v-w‖ := by
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro t
      have h := (hK t).dist_le_mul _ (path_mem hv t) _ (path_mem hw t)
      rw [dist_eq_norm, dist_eq_norm] at h
      exact h.trans (mul_le_mul_of_nonneg_left ((v-w).norm_coe_le_norm t) K.coe_nonneg)
    rw [dist_eq_norm, dist_eq_norm]
    have he : p (x,v) - p (x,w) =
        (T : ℂ) • primitive (substitute G hG v - substitute G hG w) := by
      simp only [p, map_sub, smul_sub]
      abel
    rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg T.coe_nonneg, NNReal.coe_mul,
      mul_assoc]
    exact mul_le_mul_of_nonneg_left ((primitivePath_norm _).trans hb) T.coe_nonneg
  obtain ⟨g, hg, hfix, _⟩ := analytic_fixedPoint isOpen_ball hr hrR hshort hpd hmaps (fun x _ => hpl x)
  refine ⟨g, hg, fun x hx => ⟨(hfix x hx).1, ?_, ?_⟩⟩
  · intro t
    exact (congrArg (fun v : Path E => v t) (hfix x hx).2).symm
  · intro v hv hq
    have hve : p (x,v) = v := ContinuousMap.ext fun t => (hq t).symm
    have hl := (hpl x).dist_le_mul v hv (g x) (hfix x hx).1
    rw [hve, (hfix x hx).2] at hl
    have hq' : ((T*K : ℝ≥0) : ℝ) < 1 := by exact_mod_cast hshort
    exact dist_eq_zero.mp (le_antisymm (by nlinarith [dist_nonneg (x := v) (y := g x)])
      dist_nonneg)

/-- Uniform bounds on a complex neighborhood give the derivative estimates
used by Picard on a smaller ball. Real time is continuous on the given
complex neighborhood, with no differentiation in time. -/
theorem complex_initial {G : Time × E → E} {a : E} {R M : ℝ}
    (hR : 0 < R) (hM0 : 0 ≤ M)
    (hc : ContinuousOn G (univ ×ˢ ball a R))
    (hd : ∀ t, DifferentiableOn ℂ (fun x => G (t,x)) (ball a R))
    (hb : ∀ t x, x ∈ ball a R → ‖G (t,x)‖ ≤ M)
    (T : ℝ≥0) (hsize : (T : ℝ) * M ≤ R/8) (hshort : (T : ℝ) * (M * (2/(R/4))) < 1) :
    ∃ g : E → Path E, AnalyticOnNhd ℂ g (ball a (R/8)) ∧
      ∀ x ∈ ball a (R/8), g x ∈ closedBall (ContinuousMap.const Time a) (R/4) ∧
        (∀ t : Time, g x t = x + (T : ℂ) •
          ∫ s in (0 : ℝ)..(t : ℝ), G (projIcc 0 1 zero_le_one s, g x (projIcc 0 1 zero_le_one s))) ∧
        ∀ v ∈ closedBall (ContinuousMap.const Time a) (R/4),
          (∀ t : Time, v t = x + (T : ℂ) •
            ∫ s in (0 : ℝ)..(t : ℝ), G (projIcc 0 1 zero_le_one s, v (projIcc 0 1 zero_le_one s))) →
          v = g x := by
  let H := fun (q : Time × E) => G (q.1, Ext025A4LocalExtension.clip a (R/2) q.2)
  have hH : Continuous H :=
    hc.comp_continuous (continuous_fst.prodMk
      ((Ext025A4LocalExtension.clip_continuous a (by positivity : 0 < R/2)).comp continuous_snd))
      (fun q => ⟨mem_univ _, closedBall_subset_ball (half_lt_self hR)
        (Ext025A4LocalExtension.clip_mem a (by positivity : 0 < R/2) q.2)⟩)
  have he (t : Time) (x : E) (hx : x ∈ closedBall a (R/2)) : H (t,x) = G (t,x) := by
    change G (t, Ext025A4LocalExtension.clip a (R/2) x) = G (t,x)
    rw [Ext025A4LocalExtension.clip_eq (by positivity) hx]
  have hhd (t : Time) : DifferentiableOn ℂ (fun x => H (t,x)) (ball a (R/2)) :=
    ((hd t).mono (ball_subset_ball (half_le_self hR.le))).congr
      (fun x hx => he t x (ball_subset_closedBall hx))
  have hfe (t : Time) (x : E) (hx : x ∈ ball a (R/2)) :
      fderiv ℂ (fun z => H (t,z)) x = fderiv ℂ (fun z => G (t,z)) x :=
    (Filter.EventuallyEq.fderiv_eq (𝕜 := ℂ)
      (mem_of_superset (isOpen_ball.mem_nhds hx) (fun z hz => he t z (ball_subset_closedBall hz))))
  let d := R/4
  have hd0 : 0 < d := by positivity
  let Λ := M * (2/d)^2
  have hΛ : 0 ≤ Λ := by positivity
  let K : ℝ≥0 := ⟨M * (2/d), by positivity⟩
  have hLip (t : Time) (x : E) (hx : x ∈ ball a (R/2)) (y : E) (hy : y ∈ ball a (R/2)) :
      ‖fderiv ℂ (fun z => H (t,z)) x - fderiv ℂ (fun z => H (t,z)) y‖ ≤ Λ * ‖x-y‖ := by
    rw [hfe t x hx, hfe t y hy]
    have hsub : ball a (R/2) ⊆ ball a R := ball_subset_ball (half_le_self hR.le)
    have hdf := HolomorphicStageB2c.differentiableOn_fderiv isOpen_ball (hd t)
    apply (convex_ball a (R/2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (((hdf.differentiableAt (isOpen_ball.mem_nhds (hsub hz))).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt)
      (fun z hz => ?_) hy hx
    rw [ContinuousLinearMap.norm_restrictScalars]
    have h := HolomorphicStageD1.norm_iteratedFDeriv_le_on_ball isOpen_ball (hd t) hd0 hM0
      (subset_refl (ball a R)) (hb t) 2 z
    have hradius : R - ((2 : ℕ) : ℝ) * d = R/2 := by
      dsimp [d]
      ring
    have hz' : z ∈ ball a (R - ((2 : ℕ) : ℝ) * d) := by rwa [hradius]
    have h' := h hz'
    rw [show (2 : ℕ) = 1+1 by rfl, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h'
    exact h'
  have hK (t : Time) : LipschitzOnWith K (fun x => H (t,x)) (closedBall a (R/4)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hsub : closedBall a (R/4) ⊆ ball a (R/2) := closedBall_subset_ball (by linarith)
    rw [dist_eq_norm, dist_eq_norm]
    apply (convex_closedBall a (R/4)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => ((((hhd t).differentiableAt (isOpen_ball.mem_nhds (hsub hz))).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt)
      (fun z hz => ?_) hy hx
    rw [ContinuousLinearMap.norm_restrictScalars, hfe t z (hsub hz)]
    apply ContinuousLinearMap.opNorm_le_bound _ K.2
    intro v
    have hball : ball z d ⊆ ball a R := by
      intro w hw
      rw [mem_ball] at hw ⊢
      have hh := dist_triangle w z a
      have hz' := mem_closedBall.mp hz
      dsimp [d] at hw
      linarith
    have h := HolomorphicCauchyC1.norm_fderiv_apply_le (hd t) hd0 hball
      (fun w hw => hb t w (hball hw)) v
    change ‖fderiv ℂ (fun z => G (t,z)) z v‖ ≤ M*(2/d)*‖v‖
    convert h using 1
    ring
  have hm (t : Time) (x : E) (hx : x ∈ closedBall a (R/4)) : ‖H (t,x)‖ ≤ M := by
    rw [he t x (closedBall_subset_closedBall (by linarith) hx)]
    exact hb t x (closedBall_subset_ball (by linarith) hx)
  have hT : T*K < 1 := by
    apply NNReal.coe_lt_coe.mp
    rw [NNReal.coe_mul, NNReal.coe_one]
    exact hshort
  obtain ⟨g,hg,hq⟩ := complex_picard (δ := R/8) hH T K (by positivity : 0 ≤ R/4)
    (by linarith : R/4 < R/2) hhd hΛ hLip hm hK (by linarith) hT
  have hintegrand (v : Path E) (hv : v ∈ closedBall (ContinuousMap.const Time a) (R/4)) :
      (fun s : ℝ => extend (substitute H hH v) s) =
      fun s => G (projIcc 0 1 zero_le_one s, v (projIcc 0 1 zero_le_one s)) := by
    funext s
    exact he _ _ (closedBall_subset_closedBall (by linarith)
      (path_mem hv (projIcc 0 1 zero_le_one s)))
  refine ⟨g,hg, fun x hx => ⟨(hq x hx).1, ?_, ?_⟩⟩
  · intro t
    simpa only [hintegrand (g x) (hq x hx).1] using (hq x hx).2.1 t
  · intro v hv hvq
    apply (hq x hx).2.2 v hv
    intro t
    simpa only [hintegrand v hv] using hvq t

section RealRestriction

open Ext025A4BanachComplexification
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The holomorphic solution restricts to the actual real solution family by
uniqueness of the normalized integral equation in the common ball. -/
theorem real_initial {f : Time → V → V} {G : Time × Cx V → Cx V}
    {a : V} {R M : ℝ} (hR : 0 < R) (hM0 : 0 ≤ M)
    (hc : ContinuousOn G (univ ×ˢ ball (Cx.ι a) R))
    (hd : ∀ t, DifferentiableOn ℂ (fun x => G (t,x)) (ball (Cx.ι a) R))
    (hb : ∀ t x, x ∈ ball (Cx.ι a) R → ‖G (t,x)‖ ≤ M)
    (he : ∀ t x, x ∈ closedBall a (R/4) → G (t,Cx.ι x) = Cx.ι (f t x))
    (T : ℝ≥0) (hsize : (T : ℝ) * M ≤ R/8) (hshort : (T : ℝ) * (M * (2/(R/4))) < 1)
    {φ : V → Path V}
    (hm : ∀ x ∈ ball a (R/8), φ x ∈ closedBall (ContinuousMap.const Time a) (R/4))
    (hq : ∀ x ∈ ball a (R/8), ∀ t : Time,
      φ x t = x + (T : ℝ) • ∫ s in (0 : ℝ)..(t : ℝ),
        f (projIcc 0 1 zero_le_one s) (φ x (projIcc 0 1 zero_le_one s))) :
    ∀ t : Time, AnalyticOnNhd ℝ (fun x => φ x t) (ball a (R/8)) := by
  obtain ⟨g,hg,hgq⟩ := complex_initial hR hM0 hc hd hb T hsize hshort
  have hcast (x : V) (hx : x ∈ ball a (R/8)) : Cx.ι x ∈ ball (Cx.ι a) (R/8) := by
    simpa only [mem_ball,dist_eq_norm,← Cx.ι_sub,Cx.norm_ι] using hx
  have agree (x : V) (hx : x ∈ ball a (R/8)) (t : Time) : g (Cx.ι x) t = Cx.ι (φ x t) := by
    let v : Path (Cx V) := ⟨fun t => Cx.ι (φ x t),
      (Cx.ιL : V →L[ℝ] Cx V).continuous.comp (φ x).continuous⟩
    have hv : v ∈ closedBall (ContinuousMap.const Time (Cx.ι a)) (R/4) := by
      rw [mem_closedBall, dist_eq_norm]
      apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ R/4)).mpr
      intro t
      change ‖Cx.ι (φ x t) - Cx.ι a‖ ≤ R/4
      simpa only [mem_closedBall, dist_eq_norm, ← Cx.ι_sub,Cx.norm_ι] using path_mem (hm x hx) t
    have hfix := (hgq (Cx.ι x) (hcast x hx)).2.2 v hv
    have hf (s : ℝ) : G (projIcc 0 1 zero_le_one s,v (projIcc 0 1 zero_le_one s)) =
        Cx.ι (f (projIcc 0 1 zero_le_one s) (φ x (projIcc 0 1 zero_le_one s))) :=
      he _ _ (path_mem (hm x hx) _)
    have hfcont : Continuous (fun s : ℝ =>
        G (projIcc 0 1 zero_le_one s,v (projIcc 0 1 zero_le_one s))) := by
      have hproj := continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)
      apply hc.comp_continuous (hproj.prodMk (v.continuous.comp hproj))
      intro s
      exact ⟨mem_univ _, closedBall_subset_ball (by linarith) (path_mem hv _)⟩
    have hfreal : Continuous (fun s : ℝ =>
        f (projIcc 0 1 zero_le_one s) (φ x (projIcc 0 1 zero_le_one s))) := by
      have hh := (Cx.reL : Cx V →L[ℝ] V).continuous.comp hfcont
      simpa only [Function.comp_def, hf, Cx.reL_apply, Cx.re_ι] using hh
    have heq : v = g (Cx.ι x) := hfix (fun ξ => by
      change Cx.ι (φ x ξ) = Cx.ι x + (T : ℂ) • ∫ s in (0 : ℝ)..(ξ : ℝ), _
      conv_lhs => rw [hq x hx ξ]
      rw [← Cx.ιL_apply, map_add, map_smul, Cx.ofReal_smul]
      congr 2
      rw [← (Cx.ιL : V →L[ℝ] Cx V).intervalIntegral_comp_comm
        (hfreal.intervalIntegrable _ _)]
      exact intervalIntegral.integral_congr (fun s _ => (hf s).symm))
    exact (congrArg (fun h : Path (Cx V) => h t) heq).symm
  intro t x hx
  have h := ((ContinuousMap.evalCLM (R := ℂ) (M := Cx V) t).analyticAt _).comp (hg _ (hcast x hx))
  have hreal := (Cx.reL : Cx V →L[ℝ] V).analyticAt _ |>.comp
    ((h.restrictScalars).comp ((Cx.ιL : V →L[ℝ] Cx V).analyticAt x))
  apply hreal.congr
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  change Cx.re (g (Cx.ι y) t) = φ y t
  rw [agree y hy, Cx.re_ι]

end RealRestriction

end QuantumNLS.Ext025GP04AnalyticR30m

#print axioms QuantumNLS.Ext025GP04AnalyticR30m.complex_picard
#print axioms QuantumNLS.Ext025GP04AnalyticR30m.complex_initial
#print axioms QuantumNLS.Ext025GP04AnalyticR30m.real_initial

end


/-! A bounded common holomorphic extension inherits real-time continuity
from the real slice, on a smaller complex ball. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Set Metric Filter Topology
open scoped NNReal
namespace QuantumNLS.Ext025GP04ComplexTimeR30m
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private theorem complex_slice_continuous {T : Type*} [TopologicalSpace T]
    {F : T → ℂ → E} {R M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ t, DifferentiableOn ℂ (F t) (ball 0 R))
    (hb : ∀ t z, z ∈ ball 0 R → ‖F t z‖ ≤ M)
    (hc : ∀ x : ℝ, ‖(x : ℂ)‖ < R → Continuous (fun t => F t x))
    (z : ℂ) (hz : ‖z‖ < R) : Continuous (fun t => F t z) := by
  have hA (n : ℕ) (t : T) : AnalyticOnNhd ℂ (iteratedDeriv n (F t)) (ball 0 R) := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using (hF t).analyticOnNhd isOpen_ball
    | succ n ih =>
      rw [iteratedDeriv_succ]
      exact fun w hw => (ih w hw).deriv
  have hderiv (n : ℕ) (t : T) {x : ℝ} (hx : ‖(x : ℂ)‖ < R) :
      HasDerivAt (fun r : ℝ => iteratedDeriv n (F t) (r : ℂ))
        (iteratedDeriv (n+1) (F t) (x : ℂ)) x := by
    have hx' : (x : ℂ) ∈ ball 0 R := by rwa [mem_ball,dist_zero_right]
    rw [iteratedDeriv_succ]
    have hi := Complex.ofRealCLM.hasDerivAt (x := x)
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] using
      (hA n t _ hx').differentiableAt.hasDerivAt.scomp x hi
  have hcDeriv (n : ℕ) : ∀ x : ℝ, ‖(x : ℂ)‖ < R →
      Continuous (fun t => iteratedDeriv n (F t) (x : ℂ)) := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hc
    | succ n ih =>
      intro x hx
      let d := (R - ‖(x : ℂ)‖) / 4
      have hd : 0 < d := by dsimp [d]; linarith
      let B : ℝ := (Nat.factorial (n+2) : ℝ) * M / d^(n+2)
      have hB : 0 ≤ B := by positivity
      have hxnear (y : ℝ) (hy : y ∈ Icc x (x+d)) :
          ‖(y : ℂ)‖ ≤ ‖(x : ℂ)‖ + d := by
        have h := norm_add_le (x : ℂ) ((y-x : ℝ) : ℂ)
        rw [← Complex.ofReal_add, add_sub_cancel, Complex.norm_real ((y-x : ℝ)),
          Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hy.1)] at h
        linarith [hy.2]
      have hxreal (y : ℝ) (hy : y ∈ Icc x (x+d)) : ‖(y : ℂ)‖ < R := by
        dsimp [d] at *
        linarith [hxnear y hy]
      have hbder (t : T) (y : ℝ) (hy : y ∈ Icc x (x+d)) :
          ‖iteratedDeriv (n+2) (F t) (y : ℂ)‖ ≤ B := by
        have hsub : closedBall (y : ℂ) d ⊆ ball (0 : ℂ) R := by
          intro w hw
          rw [mem_closedBall] at hw
          rw [mem_ball,dist_zero_right]
          have h := dist_triangle w (y : ℂ) 0
          rw [dist_zero_right,dist_zero_right] at h
          have hh := hxnear y hy
          dsimp [d] at hw hh
          linarith
        exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n+2) hd
          ((hF t).diffContOnCl_ball hsub)
          (fun w hw => hb t w (hsub (sphere_subset_closedBall hw)))
      let q : ℕ → ℝ := fun k => d * ((k : ℝ)+1)⁻¹
      have hq (k : ℕ) : 0 < q k := by dsimp [q]; positivity
      have hqd (k : ℕ) : q k ≤ d := by
        dsimp [q]
        have h := (inv_le_one₀ (by positivity : 0 < (k : ℝ)+1)).2
          (show (1 : ℝ) ≤ (k : ℝ)+1 by linarith [Nat.cast_nonneg (α := ℝ) k])
        simpa only [mul_one] using mul_le_mul_of_nonneg_left h hd.le
      have hq0 : Tendsto q atTop (𝓝 0) := by
        have h : Tendsto (fun k : ℕ => ((k : ℝ)+1)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp
            (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
        simpa only [mul_zero] using h.const_mul d
      let Q : ℕ → T → E := fun k t => (q k)⁻¹ •
        (iteratedDeriv n (F t) ((x+q k : ℝ) : ℂ) - iteratedDeriv n (F t) (x : ℂ))
      have hQ (k : ℕ) : Continuous (Q k) :=
        ((ih _ (hxreal _ ⟨by linarith [hq k], by linarith [hqd k]⟩)).sub (ih x hx)).const_smul _
      have err (k : ℕ) (t : T) : dist (iteratedDeriv (n+1) (F t) (x : ℂ)) (Q k t) ≤ B * q k := by
        let U := Icc x (x + q k)
        have hs : U ⊆ Icc x (x+d) := Icc_subset_Icc_right (by linarith [hqd k])
        have h₁ : x ∈ U := ⟨le_rfl, by linarith [hq k]⟩
        have h₂ : x + q k ∈ U := ⟨by linarith [hq k],le_rfl⟩
        have hLip (y : ℝ) (hy : y ∈ U) :
            ‖iteratedDeriv (n+1) (F t) (y : ℂ) - iteratedDeriv (n+1) (F t) (x : ℂ)‖ ≤ B * q k := by
          have h := (convex_Icc x (x+q k)).norm_image_sub_le_of_norm_hasFDerivWithin_le
            (fun w hw => (hderiv (n+1) t (hxreal w (hs hw))).hasDerivWithinAt.hasFDerivWithinAt)
            (fun w hw => by simpa only [ContinuousLinearMap.norm_toSpanSingleton] using hbder t w (hs hw)) h₁ hy
          have hdist : ‖y-x‖ ≤ q k := by
            rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hy.1)]
            linarith [hy.2]
          exact h.trans (mul_le_mul_of_nonneg_left hdist hB)
        have h := (convex_Icc x (x+q k)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
          (φ := ContinuousLinearMap.toSpanSingleton ℝ (iteratedDeriv (n+1) (F t) (x : ℂ)))
          (fun w hw => (hderiv n t (hxreal w (hs hw))).hasDerivWithinAt.hasFDerivWithinAt)
          (fun w hw => by
            have he : ContinuousLinearMap.toSpanSingleton ℝ
                (iteratedDeriv (n+1) (F t) (w : ℂ) - iteratedDeriv (n+1) (F t) (x : ℂ)) =
                ContinuousLinearMap.toSpanSingleton ℝ (iteratedDeriv (n+1) (F t) (w : ℂ)) -
                  ContinuousLinearMap.toSpanSingleton ℝ (iteratedDeriv (n+1) (F t) (x : ℂ)) := by
              apply ContinuousLinearMap.ext
              intro y
              simp [smul_sub]
            rw [← he, ContinuousLinearMap.norm_toSpanSingleton]
            exact hLip w hw) h₁ h₂
        simp only [add_sub_cancel_left, ContinuousLinearMap.toSpanSingleton_apply,
          Real.norm_eq_abs, abs_of_pos (hq k)] at h
        have he : Q k t - iteratedDeriv (n+1) (F t) (x : ℂ) =
            (q k)⁻¹ • (iteratedDeriv n (F t) ((x+q k : ℝ) : ℂ) -
              iteratedDeriv n (F t) (x : ℂ) - q k • iteratedDeriv (n+1) (F t) (x : ℂ)) := by
          simp only [Q, smul_sub, smul_smul, inv_mul_cancel₀ (hq k).ne', one_smul]
        rw [dist_comm, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hq k))]
        exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (hq k).le)).trans_eq (by field_simp)
      have hU : TendstoUniformly Q (fun t => iteratedDeriv (n+1) (F t) (x : ℂ)) atTop := by
        rw [Metric.tendstoUniformly_iff]
        intro ε hε
        have hqB : Tendsto (fun k => B * q k) atTop (𝓝 0) := by simpa only [mul_zero] using hq0.const_mul B
        filter_upwards [hqB.eventually (gt_mem_nhds hε)] with k hk t
        exact (err k t).trans_lt hk
      exact hU.continuous (Eventually.of_forall hQ).frequently
  obtain ⟨r, hzr, hrR⟩ := exists_between hz
  have hr : 0 < r := (norm_nonneg _).trans_lt hzr
  let g : ℕ → T → E := fun n t => ((Nat.factorial n : ℂ)⁻¹) • z^n • iteratedDeriv n (F t) 0
  have hg (n : ℕ) : Continuous (g n) :=
    ((by simpa only [Complex.ofReal_zero] using hcDeriv n 0 (by simpa using hr.trans hrR) :
      Continuous (fun t => iteratedDeriv n (F t) (0 : ℂ))).const_smul (z^n)).const_smul _
  have hs : Summable (fun n : ℕ => M * (‖z‖ / r)^n) :=
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one hr).mpr hzr)).mul_left M
  have hbound (n : ℕ) (t : T) : ‖g n t‖ ≤ M * (‖z‖ / r)^n := by
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
      ((hF t).diffContOnCl_ball (closedBall_subset_ball hrR))
      (fun w hw => hb t w (closedBall_subset_ball hrR (sphere_subset_closedBall hw)))
    have hn : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    dsimp [g]
    rw [norm_smul, norm_smul, norm_inv, Complex.norm_natCast, norm_pow]
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (by positivity)) (by positivity)).trans_eq ?_
    rw [div_pow]
    field_simp
  have hgc := continuous_tsum hg hs hbound
  exact hgc.congr (fun t => by
    simpa only [sub_zero] using (Complex.hasSum_taylorSeries_on_ball (hF t)
      (show z ∈ ball 0 R by simpa [mem_ball,dist_zero_right] using hz)).tsum_eq)

open Ext025A4BanachComplexification

/-- For a local complexification of a real field, time continuity on the
real slice and a uniform holomorphic bound imply joint continuity on a
smaller complex neighborhood. -/
theorem joint_on_smaller {T : Type*} [TopologicalSpace T]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {f : T → V → V} {G : T × Cx V → Cx V} {a : V} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hc : ∀ x ∈ ball a R, Continuous (fun t => f t x))
    (hd : ∀ t, DifferentiableOn ℂ (fun z => G (t,z)) (ball (Cx.ι a) R))
    (hb : ∀ t z, z ∈ ball (Cx.ι a) R → ‖G (t,z)‖ ≤ M)
    (he : ∀ t x, x ∈ ball a R → G (t,Cx.ι x) = Cx.ι (f t x)) :
    ContinuousOn G (univ ×ˢ ball (Cx.ι a) (R/4)) := by
  have time (z : Cx V) (hz : z ∈ ball (Cx.ι a) (R/4)) : Continuous (fun t => G (t,z)) := by
    let w := z - Cx.ι a
    let x := Cx.re w
    let y := Cx.im w
    let P : ℂ → Cx V := fun ζ => Cx.ι (a+x) + ζ • Cx.ι y
    have hnorm : ‖w‖ < R/4 := by simpa only [mem_ball, dist_eq_norm] using hz
    have hx := Cx.norm_re_le w
    have hy := Cx.norm_im_le w
    have hP (ζ : ℂ) (hζ : ζ ∈ ball (0 : ℂ) 2) : P ζ ∈ ball (Cx.ι a) R := by
      rw [mem_ball, dist_eq_norm]
      have ht : ‖ζ‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hζ
      have hsub : P ζ - Cx.ι a = Cx.ι x + ζ • Cx.ι y := by
        dsimp [P]; rw [Cx.ι_add]; abel
      rw [hsub]
      refine (norm_add_le _ _).trans_lt ?_
      rw [norm_smul, Cx.norm_ι, Cx.norm_ι]
      change ‖x‖ + ‖ζ‖ * ‖y‖ < R
      nlinarith [mul_le_mul_of_nonneg_right ht.le (norm_nonneg y)]
    have hreal (r : ℝ) (hr : ‖(r : ℂ)‖ < 2) : Continuous (fun t => G (t,P r)) := by
      have heq : P (r : ℂ) = Cx.ι (a+x+r • y) := by
        simp only [P, Cx.ofReal_smul, Cx.ι_add, Cx.ι_smul]
      have hm : a+x+r • y ∈ ball a R := by
        have h := hP r (by simpa only [mem_ball,dist_zero_right] using hr)
        rw [heq] at h
        simpa only [mem_ball,dist_eq_norm,← Cx.ι_sub,Cx.norm_ι] using h
      exact ((Cx.ιL : V →L[ℝ] Cx V).continuous.comp (hc _ hm)).congr
        (fun t => by rw [heq, he t _ hm]; rfl)
    have hzP : P Complex.I = z := by
      change Cx.ι (a+x) + Complex.I • Cx.ι y = z
      rw [Cx.ι_add]
      have hew : Cx.mk x y = w := by
        apply Cx.ext <;> rfl
      rw [add_assoc, ← Cx.mk_eq, hew]
      dsimp [w]
      abel
    have hdP (t : T) : DifferentiableOn ℂ (fun ζ => G (t,P ζ)) (ball (0 : ℂ) 2) :=
      (hd t).comp (by dsimp [P]; fun_prop) hP
    have ht := complex_slice_continuous hM hdP (fun t ζ hζ => hb t _ (hP ζ hζ))
      hreal Complex.I (by norm_num)
    simpa only [hzP] using ht
  let d := R/4
  have hd0 : 0 < d := by positivity
  let K : ℝ≥0 := ⟨2 * M / d, by positivity⟩
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith' G K
  · intro t _
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm,dist_eq_norm]
    have hsub : ball (Cx.ι a) (R/4) ⊆ ball (Cx.ι a) R := ball_subset_ball (by linarith)
    apply (convex_ball (Cx.ι a) (R/4)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => ((((hd t).differentiableAt (isOpen_ball.mem_nhds (hsub hz))).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt)
      (fun z hz => ?_) hy hx
    rw [ContinuousLinearMap.norm_restrictScalars]
    apply ContinuousLinearMap.opNorm_le_bound _ K.2
    intro v
    have hball : ball z d ⊆ ball (Cx.ι a) R := by
      intro w hw
      rw [mem_ball] at hw hz ⊢
      have hh := dist_triangle w z (Cx.ι a)
      dsimp [d] at hw
      linarith
    exact HolomorphicCauchyC1.norm_fderiv_apply_le (hd t) hd0 hball
      (fun w hw => hb t w (hball hw)) v
  · intro z hz
    exact (time z hz).continuousOn

end QuantumNLS.Ext025GP04ComplexTimeR30m

#print axioms QuantumNLS.Ext025GP04ComplexTimeR30m.joint_on_smaller

end


/-! Construct the real analytic initial-state maps using only the real-time
continuity, common complex extension and uniform bound of the source. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Set Metric Filter Topology Function ODE
open scoped NNReal
namespace QuantumNLS.Ext025GP04RealAnalyticR30m
open Ext025A4AnalyticIntegral Ext025A4BanachComplexification
universe u
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Real-time continuous vector fields with a common bounded holomorphic
state extension have local analytic initial-state maps. The normalized
time coordinate runs over [0,1] and the time-step length is T. -/
theorem real_analytic_flow {f : Time → V → V} {G : Time × Cx V → Cx V}
    {a : V} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hc : ∀ x ∈ ball a R, Continuous (fun t => f t x))
    (hd : ∀ t, DifferentiableOn ℂ (fun z => G (t,z)) (ball (Cx.ι a) R))
    (hb : ∀ t z, z ∈ ball (Cx.ι a) R → ‖G (t,z)‖ ≤ M)
    (he : ∀ t x, x ∈ ball a R → G (t,Cx.ι x) = Cx.ι (f t x))
    (T : ℝ≥0) (hsize : (T : ℝ) * M ≤ R/32)
    (hshort : (T : ℝ) * (M * (2/((R/4)/4))) < 1) :
    ∃ φ : V → Path V,
      (∀ t : Time, AnalyticOnNhd ℝ (fun x => φ x t) (ball a (R/32))) ∧
      ∀ x ∈ ball a (R/32), φ x ∈ closedBall (ContinuousMap.const Time a) (R/16) ∧
        ∀ t : Time, φ x t = x + (T : ℝ) • ∫ s in (0 : ℝ)..(t : ℝ),
          f (projIcc 0 1 zero_le_one s) (φ x (projIcc 0 1 zero_le_one s)) := by
  let F : ℝ → V → V := fun s x => (T : ℝ) • f (projIcc 0 1 zero_le_one s) x
  let Rₙ : ℝ≥0 := ⟨R/16, by positivity⟩
  let rₙ : ℝ≥0 := ⟨R/32, by positivity⟩
  let L : ℝ≥0 := ⟨(T : ℝ)*M, by positivity⟩
  let K : ℝ≥0 := ⟨(T : ℝ)*(2*M/(R/4)), by positivity⟩
  let s : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  have hsub : closedBall a (R/16) ⊆ ball a R := closedBall_subset_ball (by linarith)
  have hιb (x : V) (hx : x ∈ closedBall a (R/16)) : Cx.ι x ∈ closedBall (Cx.ι a) (R/16) := by
    simpa only [mem_closedBall, dist_eq_norm, ← Cx.ι_sub, Cx.norm_ι] using hx
  have hsubc : closedBall (Cx.ι a) (R/16) ⊆ ball (Cx.ι a) R := closedBall_subset_ball (by linarith)
  have hpl : IsPicardLindelof F s a Rₙ rₙ L K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      let k := projIcc 0 1 zero_le_one t
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have hnorm (z : Cx V) (hz : z ∈ closedBall (Cx.ι a) (R/16)) :
          ‖fderiv ℂ (fun w => G (k,w)) z‖ ≤ 2*M/(R/4) := by
        have hball : ball z (R/4) ⊆ ball (Cx.ι a) R := by
          intro w hw
          rw [mem_ball] at hw ⊢
          linarith [dist_triangle w z (Cx.ι a), mem_closedBall.mp hz]
        apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
        intro v
        exact HolomorphicCauchyC1.norm_fderiv_apply_le (hd k) (by positivity) hball
          (fun w hw => hb k w (hball hw)) v
      have hm := (convex_closedBall (Cx.ι a) (R/16)).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z hz => ((((hd k).differentiableAt (isOpen_ball.mem_nhds (hsubc hz))).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt)
        (fun z hz => by rw [ContinuousLinearMap.norm_restrictScalars]; exact hnorm z hz)
        (hιb y hy) (hιb x hx)
      rw [he k x (hsub hx), he k y (hsub hy), ← Cx.ι_sub, ← Cx.ι_sub, Cx.norm_ι, Cx.norm_ι] at hm
      rw [dist_eq_norm,dist_eq_norm]
      change ‖(T : ℝ) • f k x - (T : ℝ) • f k y‖ ≤ (T : ℝ)*(2*M/(R/4))*‖x-y‖
      rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (T : ℝ) from T.2),mul_assoc]
      exact mul_le_mul_of_nonneg_left hm T.2
    · intro x hx
      exact (((hc x (hsub hx)).comp (continuous_projIcc (h := zero_le_one))).const_smul (T : ℝ)).continuousOn
    · intro t ht x hx
      let k := projIcc 0 1 zero_le_one t
      have h := hb k (Cx.ι x) (hsubc (hιb x hx))
      rw [he k x (hsub hx), Cx.norm_ι] at h
      change ‖(T : ℝ) • f k x‖ ≤ (T : ℝ)*M
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (T : ℝ) from T.2)]
      exact mul_le_mul_of_nonneg_left h T.2
    · change ((T : ℝ)*M)*max (1-0) (0-0) ≤ R/16-R/32
      norm_num
      linarith
  classical
  choose α hα hα₀ hαm hαq hαd using fun x : closedBall a (R/32) =>
    Ext025A2.gp04_differential_existence hpl x.2
  let φ : V → Path V := fun x =>
    if hx : x ∈ closedBall a (R/32)
    then ⟨fun t => α ⟨x,hx⟩ t, (hα ⟨x,hx⟩).comp continuous_subtype_val⟩
    else ContinuousMap.const Time x
  have hm (x : V) (hx : x ∈ ball a (R/32)) : φ x ∈ closedBall (ContinuousMap.const Time a) (R/16) := by
    rw [mem_closedBall,dist_eq_norm]
    apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ R/16)).mpr
    intro t
    simp only [φ,dite_eq_left (ball_subset_closedBall hx),ContinuousMap.sub_apply,ContinuousMap.const_apply]
    change ‖α ⟨x,ball_subset_closedBall hx⟩ t - a‖ ≤ R/16
    exact (mem_closedBall_iff_norm.mp (hαm ⟨x,ball_subset_closedBall hx⟩ t))
  have hq (x : V) (hx : x ∈ ball a (R/32)) (t : Time) :
      φ x t = x + (T : ℝ) • ∫ s in (0 : ℝ)..(t : ℝ),
        f (projIcc 0 1 zero_le_one s) (φ x (projIcc 0 1 zero_le_one s)) := by
    simp only [φ,dite_eq_left (ball_subset_closedBall hx)]
    change α ⟨x,ball_subset_closedBall hx⟩ t = _
    rw [hαq ⟨x,ball_subset_closedBall hx⟩ t t.2]
    change x + (∫ s in (0 : ℝ)..(t : ℝ), F s (α ⟨x,ball_subset_closedBall hx⟩ s)) = _
    rw [← intervalIntegral.integral_smul]
    congr 1
    apply intervalIntegral.integral_congr
    intro z hz
    change F z (α ⟨x,ball_subset_closedBall hx⟩ z) =
      (T : ℝ) • f (projIcc 0 1 zero_le_one z) (α ⟨x,ball_subset_closedBall hx⟩ (projIcc 0 1 zero_le_one z))
    dsimp only [F]
    rw [projIcc_of_mem _ (uIcc_subset_Icc (by norm_num) t.2 hz)]
  have hcont := Ext025GP04ComplexTimeR30m.joint_on_smaller hR hM hc hd hb he
  have hsmall : ball (Cx.ι a) (R/4) ⊆ ball (Cx.ι a) R := ball_subset_ball (by linarith)
  have ha := Ext025GP04AnalyticR30m.real_initial (show 0 < R/4 by positivity) hM hcont
    (fun t => (hd t).mono hsmall) (fun t z hz => hb t z (hsmall hz))
    (fun t x hx => he t x (closedBall_subset_ball (by linarith) hx))
    T (by linarith) hshort (φ := φ)
  have h8 : R/4/8 = R/32 := by ring
  have h4 : R/4/4 = R/16 := by ring
  rw [h8,h4] at ha
  exact ⟨φ,ha hm hq,fun x hx => ⟨hm x hx,hq x hx⟩⟩

/-- Local time analyticity for an autonomous analytic field. A signed
multiplier is a frozen initial coordinate of the augmented vector field. -/
theorem autonomous_time_analytic {f : V → V} {γ : ℝ → V} {s ε : ℝ}
    (hε : 0 < ε) (hf : AnalyticAt ℝ f (γ s))
    (hγ : ∀ t ∈ Ioo (s-ε) (s+ε), HasDerivAt γ (f (γ t)) t) :
    AnalyticAt ℝ γ s := by
  let W := ℝ × V
  let a : W := (0,γ s)
  let F : W → W := fun u => (0, u.1 • f u.2)
  have ha : AnalyticAt ℝ (fun q : W => f q.2) a :=
    hf.comp (f := (Prod.snd : W → V)) (x := a) analyticAt_snd
  have hs : AnalyticAt ℝ (fun q : W => q.1 • f q.2) a :=
    (analyticAt_fst : AnalyticAt ℝ (Prod.fst : W → ℝ) a).smul ha
  have hF : AnalyticAt ℝ F a := analyticAt_const.prod hs
  obtain ⟨R,hR,M,hM,K,Λ,hΛ,G,hG,hGd,hGl,hGb,hGk,hGe⟩ :=
    Ext025A4FamilyCharts.local_field_data hF
  let d₀ := min (R/(8*(M+1))) (1/(2*((K : ℝ)+1)))
  have hd₀ : 0 < d₀ := lt_min (by positivity) (by positivity)
  let d : ℝ≥0 := ⟨d₀,hd₀.le⟩
  have hd' : (0 : ℝ) < d := hd₀
  have hsize : R/8 + (d : ℝ) * M ≤ R/2 := by
    have hh : d₀ ≤ R/(8*(M+1)) := min_le_left _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 8*(M+1))).mp hh
    change R/8 + d₀*M ≤ R/2
    nlinarith
  have hsmall : d*K < 1 := by
    apply NNReal.coe_lt_coe.mp
    rw [NNReal.coe_mul,NNReal.coe_one]
    have hh : d₀ ≤ 1/(2*((K : ℝ)+1)) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*((K : ℝ)+1))).mp hh
    change d₀*(K : ℝ) < 1
    nlinarith
  obtain ⟨q,hq,hqm⟩ := local_holomorphic_solution hG d K
    (by positivity : 0 ≤ R/2) (by linarith : R/2 < R) hGd hΛ hGl hGb hsize hGk hsmall
  let e : Time := ⟨1,by norm_num⟩
  let out : ℝ → V := fun w₀ => (Cx.re (q (Cx.ι (w₀,γ s)) e)).2
  have hout : AnalyticAt ℝ out 0 := by
    let start : ℝ → Cx W := fun w₀ => Cx.ι (w₀,γ s)
    let endpoint : Cx W → Cx W := fun z => q z e
    let extract : Cx W →L[ℝ] V := (ContinuousLinearMap.snd ℝ ℝ V).comp Cx.reL
    have hs : AnalyticAt ℝ start 0 :=
      ((Cx.ιL : W →L[ℝ] Cx W).analyticAt a).comp
        (f := fun w₀ : ℝ => (w₀,γ s)) (x := 0) (analyticAt_id.prod analyticAt_const)
    have hq0 : AnalyticAt ℂ endpoint (start 0) :=
      ((ContinuousMap.evalCLM (R := ℂ) (M := Cx W) e).analyticAt _).comp
        (f := q) (x := Cx.ι a) (hq (Cx.ι a) (mem_ball_self (by positivity : 0 < R/8)))
    have hqe : AnalyticAt ℝ (endpoint ∘ start) 0 :=
      (hq0.restrictScalars (𝕜 := ℝ)).comp (f := start) (x := 0) hs
    exact (extract.analyticAt ((endpoint ∘ start) 0)).comp (f := endpoint ∘ start) (x := 0) hqe
  have hγs := hγ s ⟨by linarith,by linarith⟩
  obtain ⟨r,hr,hnear⟩ := Metric.continuousAt_iff.mp hγs.continuousAt (R/4) (by positivity)
  let η := min (R/8) (min ε r / (2*((d : ℝ)+1)))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have heq : out =ᶠ[𝓝 0] fun w₀ => γ (s + (d : ℝ)*w₀) := by
    filter_upwards [ball_mem_nhds (0 : ℝ) hη] with w₀ hw₀
    have hw₀r : |w₀| < R/8 := by
      have hh := (mem_ball.mp hw₀).trans_le (min_le_left _ _)
      simpa only [Real.dist_eq,sub_zero] using hh
    have hw₀η : |w₀| * (2*((d : ℝ)+1)) < min ε r := by
      apply (lt_div_iff₀ (by positivity : 0 < 2*((d : ℝ)+1))).mp
      have hh := (mem_ball.mp hw₀).trans_le (min_le_right _ _)
      simpa only [Real.dist_eq,sub_zero] using hh
    let j := projIcc (-1 : ℝ) 2 (by norm_num)
    let τ : ℝ → ℝ := fun t => s + (d : ℝ)*w₀*t
    have ht (t : ℝ) (hm : t ∈ Icc (-1 : ℝ) 2) : dist (τ t) s < min ε r := by
      have ha : |t| ≤ 2 := abs_le.mpr ⟨by linarith [hm.1],hm.2⟩
      rw [Real.dist_eq,show τ t - s = (d : ℝ)*w₀*t by dsimp [τ]; ring, abs_mul, abs_mul,
        abs_of_nonneg (show 0 ≤ (d : ℝ) from d.2)]
      have hh := mul_le_mul_of_nonneg_left ha (mul_nonneg d.2 (abs_nonneg w₀))
      nlinarith [abs_nonneg w₀]
    have htε (t : ℝ) (hm : t ∈ Icc (-1 : ℝ) 2) : τ t ∈ Ioo (s-ε) (s+ε) := by
      have hh := (ht t hm).trans_le (min_le_left _ _)
      rw [Real.dist_eq,abs_lt] at hh
      exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
    let β : ℝ → W := fun t => (w₀, γ (τ (j t)))
    have hγc : ContinuousOn γ (Ioo (s-ε) (s+ε)) :=
      fun t h => (hγ t h).continuousAt.continuousWithinAt
    have hβ : Continuous β := continuous_const.prodMk
      (hγc.comp_continuous (by dsimp [τ,j]; fun_prop) (fun t => htε (j t) (j t).2))
    have hβ0 : β 0 = (w₀,γ s) := by
      have hj : (j 0 : ℝ) = 0 := by dsimp [j]; rw [projIcc_of_mem _ (by norm_num)]
      simp [β,τ,hj]
    have hβm (t : ℝ) : β t ∈ closedBall a (R/2) := by
      have hγb := hnear ((ht (j t) (j t).2).trans_le (min_le_right _ _))
      rw [mem_closedBall]
      change max (dist w₀ 0) (dist (γ (τ (j t))) (γ s)) ≤ R/2
      rw [Real.dist_eq,sub_zero]
      exact max_le (by linarith) (by linarith)
    have hβd (t : ℝ) (hm : t ∈ Icc (-1 : ℝ) 2) :
        HasDerivWithinAt β ((d : ℝ) • F (β t)) (Icc (-1 : ℝ) 2) t := by
      have he (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 2) : β t = (w₀,γ (τ t)) := by
        have ht' : (j t : ℝ) = t := by dsimp [j]; rw [projIcc_of_mem _ ht]
        simp [β,ht']
      have hτ : HasDerivAt τ ((d : ℝ)*w₀) t := by
        simpa only [τ,id_eq,mul_one] using (((hasDerivAt_id t).const_mul ((d : ℝ)*w₀)).const_add s)
      have hh := (hasDerivAt_const t w₀).prodMk ((hγ _ (htε t hm)).scomp t hτ)
      have hh' : HasDerivAt (fun z => (w₀, γ (τ z))) ((d : ℝ) • F (β t)) t := by
        rw [show (d : ℝ) • F (β t) = ((0 : ℝ), ((d : ℝ)*w₀) • f (γ (τ t))) from by
          rw [he t hm]
          apply Prod.ext
          · change (d : ℝ) • (0 : ℝ) = 0
            exact smul_zero _
          · change (d : ℝ) • (w₀ • f (γ (τ t))) = ((d : ℝ)*w₀) • f (γ (τ t))
            exact (mul_smul _ _ _).symm]
        exact hh
      exact hh'.hasDerivWithinAt.congr (fun z hz => he z hz) (he t hm)
    obtain ⟨v,hv,hfix,hve⟩ := Ext025A4LocalComparison.embedded_fixedPoint
      hG hβ hβ0 hβm hGe hβd
    have hx : Cx.ι ((w₀,γ s) : W) ∈ ball (Cx.ι a) (R/8) := by
      rw [mem_ball,dist_eq_norm,← Cx.ι_sub,Cx.norm_ι]
      change max ‖w₀ - 0‖ ‖γ s - γ s‖ < R/8
      simpa only [sub_zero,sub_self,norm_zero,Real.norm_eq_abs,max_eq_left (abs_nonneg w₀)] using hw₀r
    have hfixq : picard G hG d (Cx.ι ((w₀,γ s) : W),q (Cx.ι ((w₀,γ s) : W))) = q (Cx.ι ((w₀,γ s) : W)) := by
      apply ContinuousMap.ext
      intro t
      exact ((hqm _ hx).2 t).symm
    have hvq := Ext025A4PicardStability.fixedPoint_initial_bound hG d K hGk hsmall
      (hqm _ hx).1 hv hfixq hfix
    have hqv : q (Cx.ι ((w₀,γ s) : W)) = v :=
      sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hvq))
    have hj : (j 1 : ℝ) = 1 := by dsimp [j]; rw [projIcc_of_mem _ (by norm_num)]
    dsimp only [out]
    rw [hqv,hve e,Cx.re_ι]
    change γ (τ (j 1)) = _
    simp [τ,hj]
  have hscaled := hout.congr heq
  have hin : AnalyticAt ℝ (fun t : ℝ => (t-s)/(d : ℝ)) s :=
    (analyticAt_id.sub analyticAt_const).div_const
  have hscaled' : AnalyticAt ℝ (fun w₀ => γ (s + (d : ℝ)*w₀)) ((s-s)/(d : ℝ)) := by
    simpa only [sub_self,zero_div] using hscaled
  have h := hscaled'.comp (f := fun t : ℝ => (t-s)/(d : ℝ)) (x := s) hin
  have he : (fun w₀ => γ (s + (d : ℝ)*w₀)) ∘ (fun t : ℝ => (t-s)/(d : ℝ)) = γ := by
    funext t
    change γ (s+(d : ℝ)*((t-s)/(d : ℝ))) = γ t
    congr 1
    field_simp [hd'.ne'] <;> ring
  rwa [he] at h

/-- Local time analyticity of an actual trajectory of a jointly analytic
nonautonomous field, obtained by adding the real clock. -/
theorem nonautonomous_time_analytic {f : ℝ → V → V} {γ : ℝ → V} {s ε : ℝ}
    (hε : 0 < ε) (hf : AnalyticAt ℝ (uncurry f) (s,γ s))
    (hγ : ∀ t ∈ Ioo (s-ε) (s+ε), HasDerivAt γ (f t (γ t)) t) :
    AnalyticAt ℝ γ s := by
  let F : ℝ × V → ℝ × V := fun u => (1,f u.1 u.2)
  have hF : AnalyticAt ℝ F (s,γ s) := analyticAt_const.prod hf
  have hh := autonomous_time_analytic (γ := fun t => (t,γ t)) (f := F) hε hF
    (fun t ht => (hasDerivAt_id t).prodMk (hγ t ht))
  exact analyticAt_snd.comp hh

end QuantumNLS.Ext025GP04RealAnalyticR30m

#print axioms QuantumNLS.Ext025GP04RealAnalyticR30m.real_analytic_flow
#print axioms QuantumNLS.Ext025GP04RealAnalyticR30m.autonomous_time_analytic
#print axioms QuantumNLS.Ext025GP04RealAnalyticR30m.nonautonomous_time_analytic

end
