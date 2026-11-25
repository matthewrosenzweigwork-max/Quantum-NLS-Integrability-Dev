import Mathlib
import NlsGge.Atomic.G4.G4036Cauchy
import NlsGge.Atomic.G4.G4012

/- G4-036 generic parameter-analyticity lemma (proof development, AUTHOR; not self-reviewed). Pure analysis.
   Joint analyticity of the compact nested Cauchy integral `cauchyOwnCorr` in a complex parameter and the
   spectral variable, from joint analyticity of K and w near the fixed circle. Uses the landed G4012
   parameter-integral theorem twice (inner primitive at fixed angle, then the outer Cauchy integral). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Atomic.G4036Cauchy

namespace NlsGge.Atomic.G4036Param
noncomputable section

/-- Local uniform bound near a parameter point, uniform on the sphere (tube lemma). -/
theorem local_uniform_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set E}
    {H : E × ℂ → ℂ} {c : ℂ} {r : ℝ} (hH : ∀ q ∈ D ×ˢ sphere c r, ContinuousAt H q) {x0 : E}
    (hx0 : D ∈ 𝓝 x0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball x0 ρ ⊆ D ∧ ∃ M : ℝ, ∀ x ∈ ball x0 ρ, ∀ z ∈ sphere c r,
      ‖H (x, z)‖ ≤ M := by
  have hx0D : x0 ∈ D := mem_of_mem_nhds hx0
  have hcont : ContinuousOn (fun z : ℂ => H (x0, z)) (sphere c r) := by
    intro z hz
    exact ((hH (x0, z) ⟨hx0D, hz⟩).comp (f := fun z : ℂ => (x0, z))
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  obtain ⟨M0, hM0⟩ := (isCompact_sphere c r).exists_bound_of_continuousOn hcont
  have hev : ∀ᶠ x in 𝓝 x0, ∀ z ∈ sphere c r, ‖H (x, z)‖ < M0 + 1 := by
    refine (isCompact_sphere c r).eventually_forall_of_forall_eventually (fun y hy => ?_)
    have hc := (hH (x0, y) ⟨hx0D, hy⟩).norm
    have hlt : ‖H (x0, y)‖ < M0 + 1 := by linarith [hM0 y hy]
    exact hc.eventually_lt continuousAt_const hlt
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hev.and hx0)
  exact ⟨ρ, hρ, fun x hx => (hball x hx).2, M0 + 1, fun x hx z hz => (hball x hx).1 z hz |>.le⟩


theorem norm_deriv_circleMap {c : ℂ} {r : ℝ} (hr : 0 < r) (t : ℝ) :
    ‖deriv (circleMap c r) t‖ = r := by
  rw [deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, abs_of_pos hr, mul_one]

section Joint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set E} {c : ℂ} {r : ℝ}
  {K w : E → ℂ → ℂ}

/-- Slice facts: for a fixed parameter in `D` the slice functions are continuous on the sphere. -/
theorem slice_facts (hK : AnalyticOnNhd ℂ (fun q : E × ℂ => K q.1 q.2) (D ×ˢ sphere c r))
    (hw : AnalyticOnNhd ℂ (fun q : E × ℂ => w q.1 q.2) (D ×ˢ sphere c r))
    {x : E} (hx : x ∈ D) :
    ContinuousOn (K x) (sphere c r) ∧ ∀ z ∈ sphere c r, ContinuousAt (w x) z := by
  have hpair : ∀ z : ℂ, AnalyticAt ℂ (fun z : ℂ => (x, z)) z := fun z =>
    analyticAt_const.prod analyticAt_id
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · exact ((hK (x, z) ⟨hx, hz⟩).comp (hpair z)).continuousAt.continuousWithinAt
  · exact ((hw (x, z) ⟨hx, hz⟩).comp (hpair z)).continuousAt

theorem joint_inner_analytic (hr : 0 < r)
    (hK : AnalyticOnNhd ℂ (fun q : E × ℂ => K q.1 q.2) (D ×ˢ sphere c r))
    (hw : AnalyticOnNhd ℂ (fun q : E × ℂ => w q.1 q.2) (D ×ˢ sphere c r))
    (hw0 : ∀ x ∈ D, ∀ z ∈ sphere c r, w x z ≠ 0) (hD : IsOpen D) {θ : ℝ} (hθ : 0 < θ) :
    AnalyticOnNhd ℂ (fun x : E => cU c r (K x) (w x) θ) D := by
  have hG : ∀ q ∈ D ×ˢ sphere c r, AnalyticAt ℂ (fun q : E × ℂ => (K q.1 q.2 - 1) / w q.1 q.2) q :=
    fun q hq => ((hK q hq).sub analyticAt_const).div (hw q hq) (hw0 q.1 hq.1 q.2 hq.2)
  have hrepr : (fun x : E => cU c r (K x) (w x) θ) = fun x : E =>
      ∫ t : ℝ in Ioc 0 θ, deriv (circleMap c r) t *
        ((K x (circleMap c r t) - 1) / w x (circleMap c r t)) := by
    funext x
    unfold cU cG
    exact intervalIntegral.integral_of_le hθ.le
  rw [hrepr]
  refine NlsGge.Atomic.G4.analyticOn_integral_of_locally_dominated
    (μ := volume.restrict (Ioc 0 θ)) hD ?_ ?_ ?_
  · refine Filter.Eventually.of_forall (fun t x hx => ?_)
    have hmem := circleMap_mem_sphere c hr.le t
    have h1 : AnalyticAt ℂ (fun x : E => (K x (circleMap c r t) - 1) / w x (circleMap c r t)) x :=
      AnalyticAt.comp (g := fun q : E × ℂ => (K q.1 q.2 - 1) / w q.1 q.2)
        (f := fun x : E => (x, circleMap c r t))
        (hG (x, circleMap c r t) ⟨hx, hmem⟩) (analyticAt_id.prod analyticAt_const)
    exact analyticAt_const.mul h1
  · intro x hx
    obtain ⟨hKc, hwc⟩ := slice_facts hK hw hx
    have := (deriv_circleMap_continuous c r).mul (cG_continuous hr hKc hwc (hw0 x hx))
    exact this.aestronglyMeasurable
  · intro x0 hx0
    obtain ⟨ρ, hρ, hball, M, hM⟩ := local_uniform_bound
      (H := fun q : E × ℂ => (K q.1 q.2 - 1) / w q.1 q.2) (c := c) (r := r)
      (fun q hq => (hG q hq).continuousAt) (hD.mem_nhds hx0)
    refine ⟨ρ, hρ, hball, fun _ => r * M, integrable_const _, ?_⟩
    intro v hv
    refine Filter.Eventually.of_forall (fun t => ?_)
    rw [norm_mul, norm_deriv_circleMap hr]
    exact mul_le_mul_of_nonneg_left (hM v hv _ (circleMap_mem_sphere c hr.le t)) hr.le


/-- The Cauchy-kernel integrand of `cauchyOwnCorr`, as a function of the parameter pair. -/
def cA (c : ℂ) (r : ℝ) (K w : E → ℂ → ℂ) (θ : ℝ) (q : E × ℂ) : ℂ :=
  cB c r (K q.1) (w q.1) θ * deriv (circleMap c r) θ / (circleMap c r θ - q.2)

theorem joint_cauchy_analytic (hr : 0 < r)
    (hK : AnalyticOnNhd ℂ (fun q : E × ℂ => K q.1 q.2) (D ×ˢ sphere c r))
    (hw : AnalyticOnNhd ℂ (fun q : E × ℂ => w q.1 q.2) (D ×ˢ sphere c r))
    (hw0 : ∀ x ∈ D, ∀ z ∈ sphere c r, w x z ≠ 0) (hD : IsOpen D) :
    AnalyticOnNhd ℂ (fun q : E × ℂ => cauchyOwnCorr c r (K q.1) (w q.1) q.2)
      (D ×ˢ ball c r) := by
  have hdist : ∀ (θ : ℝ) (lam : ℂ), lam ∈ ball c r → circleMap c r θ - lam ≠ 0 := by
    intro θ lam hlam h
    have h1 : circleMap c r θ = lam := sub_eq_zero.mp h
    have h2 := mem_ball.mp hlam
    have h3 : dist (circleMap c r θ) c = r := by
      rw [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
    rw [h1] at h3
    linarith
  have hGa : ∀ q ∈ D ×ˢ sphere c r,
      AnalyticAt ℂ (fun q : E × ℂ => (K q.1 q.2 - 1) / w q.1 q.2) q := fun q hq =>
    ((hK q hq).sub analyticAt_const).div (hw q hq) (hw0 q.1 hq.1 q.2 hq.2)
  have hia : ∀ q ∈ D ×ˢ sphere c r, AnalyticAt ℂ (fun q : E × ℂ => 1 / w q.1 q.2) q := fun q hq =>
    analyticAt_const.div (hw q hq) (hw0 q.1 hq.1 q.2 hq.2)
  have hU : IsOpen (D ×ˢ ball c r) := hD.prod isOpen_ball
  have hEq : EqOn (fun q : E × ℂ => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∫ θ : ℝ in Ioc 0 (2 * Real.pi), cA c r K w θ q)
      (fun q : E × ℂ => cauchyOwnCorr c r (K q.1) (w q.1) q.2) (D ×ˢ ball c r) := by
    intro q _
    simp only []
    rw [cauchyOwnCorr_eq]
    congr 1
    rw [intervalIntegral.integral_of_le (by positivity)]
    rfl
  refine AnalyticOnNhd.congr hU ?_ hEq
  refine analyticOnNhd_const.mul ?_
  refine NlsGge.Atomic.G4.analyticOn_integral_of_locally_dominated
    (μ := volume.restrict (Ioc 0 (2 * Real.pi))) hU ?_ ?_ ?_
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall (fun θ hθ q hq => ?_))
    have hmem := circleMap_mem_sphere c hr.le θ
    have hUa := joint_inner_analytic hr hK hw hw0 hD hθ.1 q.1 hq.1
    have hUq : AnalyticAt ℂ (fun q : E × ℂ => cU c r (K q.1) (w q.1) θ) q :=
      AnalyticAt.comp (g := fun x : E => cU c r (K x) (w x) θ) (f := Prod.fst) hUa analyticAt_fst
    have hwq : AnalyticAt ℂ (fun q : E × ℂ => w q.1 (circleMap c r θ)) q :=
      AnalyticAt.comp (g := fun p : E × ℂ => w p.1 p.2)
        (f := fun q : E × ℂ => (q.1, circleMap c r θ))
        (hw (q.1, circleMap c r θ) ⟨hq.1, hmem⟩) (analyticAt_fst.prod analyticAt_const)
    have hden : AnalyticAt ℂ (fun q : E × ℂ => circleMap c r θ - q.2) q :=
      analyticAt_const.sub analyticAt_snd
    have hB : AnalyticAt ℂ (fun q : E × ℂ => cB c r (K q.1) (w q.1) θ) q := by
      unfold cB
      exact hUq.div hwq (hw0 q.1 hq.1 _ hmem)
    exact (hB.mul analyticAt_const).div hden (hdist θ q.2 hq.2)
  · intro q hq
    obtain ⟨hKc, hwc⟩ := slice_facts hK hw hq.1
    have hBc := cB_continuous hr hKc hwc (hw0 q.1 hq.1)
    have : Continuous (fun θ : ℝ => cA c r K w θ q) :=
      (hBc.mul (deriv_circleMap_continuous c r)).div
        ((continuous_circleMap c r).sub continuous_const) (fun θ => hdist θ q.2 hq.2)
    exact this.aestronglyMeasurable
  · rintro ⟨x0, lam0⟩ ⟨hx0, hlam0⟩
    set δ : ℝ := r - dist lam0 c with hδ
    have hδpos : 0 < δ := by have := mem_ball.mp hlam0; linarith
    obtain ⟨ρ1, hρ1, hb1, M1, hM1⟩ := local_uniform_bound
      (H := fun q : E × ℂ => (K q.1 q.2 - 1) / w q.1 q.2) (c := c) (r := r)
      (fun q hq => (hGa q hq).continuousAt) (hD.mem_nhds hx0)
    obtain ⟨ρ2, hρ2, hb2, M2, hM2⟩ := local_uniform_bound
      (H := fun q : E × ℂ => 1 / w q.1 q.2) (c := c) (r := r)
      (fun q hq => (hia q hq).continuousAt) (hD.mem_nhds hx0)
    have hM1' : 0 ≤ max M1 0 := le_max_right _ _
    have hM2' : 0 ≤ max M2 0 := le_max_right _ _
    refine ⟨min (min ρ1 ρ2) (δ / 2), lt_min (lt_min hρ1 hρ2) (by linarith), ?_,
      fun _ => (r * max M1 0 * (2 * Real.pi)) * max M2 0 * r * (2 / δ), integrable_const _, ?_⟩
    · intro q hq
      have hq' : q ∈ ball (x0, lam0) (min (min ρ1 ρ2) (δ / 2)) := hq
      rw [← ball_prod_same] at hq'
      refine ⟨hb1 (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hq'.1), ?_⟩
      have h1 : dist q.2 lam0 < δ / 2 := lt_of_lt_of_le (mem_ball.mp hq'.2) (min_le_right _ _)
      rw [mem_ball]
      have := dist_triangle q.2 lam0 c
      linarith
    · intro v hv
      have hv' : v ∈ ball (x0, lam0) (min (min ρ1 ρ2) (δ / 2)) := hv
      rw [← ball_prod_same] at hv'
      have hx1 : v.1 ∈ ball x0 ρ1 :=
        ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hv'.1
      have hx2 : v.1 ∈ ball x0 ρ2 :=
        ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hv'.1
      have hxD : v.1 ∈ D := hb1 hx1
      have hl : dist v.2 lam0 < δ / 2 := lt_of_lt_of_le (mem_ball.mp hv'.2) (min_le_right _ _)
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall (fun θ hθ => ?_))
      have hmem := circleMap_mem_sphere c hr.le θ
      -- bound on the inner primitive
      have hU : ‖cU c r (K v.1) (w v.1) θ‖ ≤ (r * max M1 0) * (2 * Real.pi) := by
        unfold cU
        have hb : ∀ t ∈ uIoc (0 : ℝ) θ, ‖deriv (circleMap c r) t * cG c r (K v.1) (w v.1) t‖ ≤
            r * max M1 0 := by
          intro t _
          rw [norm_mul, norm_deriv_circleMap hr]
          exact mul_le_mul_of_nonneg_left
            ((hM1 v.1 hx1 _ (circleMap_mem_sphere c hr.le t)).trans (le_max_left _ _)) hr.le
        refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
        rw [sub_zero, abs_of_pos hθ.1]
        exact mul_le_mul_of_nonneg_left hθ.2 (mul_nonneg hr.le hM1')
      have hwinv : 1 / ‖w v.1 (circleMap c r θ)‖ ≤ max M2 0 := by
        have := hM2 v.1 hx2 _ hmem
        simp only [norm_div, norm_one] at this
        exact this.trans (le_max_left _ _)
      have hlow : δ / 2 ≤ ‖circleMap c r θ - v.2‖ := by
        have h2 : dist (circleMap c r θ) c = r := by
          rw [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
        have h3 := dist_triangle (circleMap c r θ) v.2 c
        have h4 := dist_triangle v.2 lam0 c
        have h5 : dist (circleMap c r θ) v.2 = ‖circleMap c r θ - v.2‖ := dist_eq_norm _ _
        linarith
      have hlow' : 1 / ‖circleMap c r θ - v.2‖ ≤ 2 / δ := by
        rw [div_le_div_iff₀ (lt_of_lt_of_le (by linarith) hlow) hδpos]
        linarith
      have hnorm : ‖cA c r K w θ v‖ = ‖cU c r (K v.1) (w v.1) θ‖ *
          (1 / ‖w v.1 (circleMap c r θ)‖) * ‖deriv (circleMap c r) θ‖ *
          (1 / ‖circleMap c r θ - v.2‖) := by
        unfold cA cB
        rw [norm_div, norm_mul, norm_div]
        ring
      rw [hnorm, norm_deriv_circleMap hr]
      show _ ≤ r * max M1 0 * (2 * Real.pi) * max M2 0 * r * (2 / δ)
      gcongr

end Joint
end
end NlsGge.Atomic.G4036Param
