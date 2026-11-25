import NlsGge.GK38.XiSqKernel
import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

/-- ONLY the omitted domain contains the filled own disc; other cuts remain excluded. -/
theorem a5OwnClosedBall_omittedDomain38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R)
    (n : ℤ) (z : ℂ) (hz : z ∈ closedBall (C n) (R n)) :
    (φ, z) ∈ a5OmittedRootDomain38 n := by
  obtain ⟨c, N, hg, hs⟩ := hf
  refine ⟨hφ, fun m hmn hseg => ?_⟩
  have hmball := (hs.1 m).1 hseg
  have hsep := isolating_geometry_closure_separated38 C R c N hg m n hmn
  have hm : dist z (C m) < R m := mem_ball.mp hmball
  have hn : dist z (C n) ≤ R n := mem_closedBall.mp hz
  have htri : dist (C m) (C n) ≤ dist z (C m) + dist z (C n) := by
    simpa only [dist_comm (C m) z] using dist_triangle (C m) z (C n)
  linarith

theorem a5Chi_own_disc_analytic38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    AnalyticOnNhd ℂ (fun z => a5Chi38 n (φ, z)) (closedBall (C n) (R n)) := by
  intro z hz
  exact AnalyticAt.comp (g := a5Chi38 n) (f := fun w : ℂ => (φ, w))
    (a5Chi_analytic38 n _ (a5OwnClosedBall_omittedDomain38 φ hφ C R hf n z hz))
    (analyticAt_const.prod analyticAt_id)

/-- Genuine integrability is part of the exported Cauchy result. -/
theorem a5Chi_own_circle_zero38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (fun z => z * a5Chi38 n (φ, z) / Complex.I) (C n) (R n) ∧
      circleIntegral (fun z => z * a5Chi38 n (φ, z) / Complex.I) (C n) (R n) = 0 := by
  have hr := isolating_radius_pos38 hf n
  have ha : AnalyticOnNhd ℂ (fun z => z * a5Chi38 n (φ, z) / Complex.I)
      (closedBall (C n) (R n)) :=
    (analyticOnNhd_id.mul (a5Chi_own_disc_analytic38 φ hφ C R hf n)).div_const
  have hi := ContinuousOn.circleIntegrable hr.le
    (ha.continuousOn.mono sphere_subset_closedBall)
  have hz := Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
    (s := (∅ : Set ℂ)) countable_empty ha.continuousOn
    (fun z hz => (ha z (ball_subset_closedBall hz.1)).differentiableAt)
  exact ⟨hi, hz⟩

/-- A fixed actual isolating family gives an actual kernel circle, avoiding ALL cuts. -/
theorem a5Kernel_own_circle_integrable38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (fun z => a5NormalizedKernel38 n (φ, z)) (C n) (R n) := by
  have hr := isolating_radius_pos38 hf n
  have ha : AnalyticOnNhd ℂ (fun z => a5NormalizedKernel38 n (φ, z))
      (sphere (C n) (R n)) := by
    intro z hz
    have hfull : (φ, z) ∈ rootDomain38 := ⟨hφ, fixed_sphere_subset φ C R hf n hz⟩
    exact AnalyticAt.comp (g := a5NormalizedKernel38 n) (f := fun w : ℂ => (φ, w))
      (a5NormalizedKernel_analytic38 n _ hfull) (analyticAt_const.prod analyticAt_id)
  exact ContinuousOn.circleIntegrable hr.le ha.continuousOn

/-- Fixed-circle coordinate, defined on all potentials but only used on its certified local family. -/
def a5LocalXi38 (n : ℤ) (c : ℂ) (r : ℝ) (φ : PotPair) : ℂ :=
  (4 / (Real.pi : ℂ)) * circleIntegral (fun z => a5NormalizedKernel38 n (φ, z)) c r

/-- Exact local analytic divisibility, with both genuine integrabilities earned first. -/
theorem a5LocalXi_identity38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (actionIntegrand38 φ) (C n) (R n) ∧
      CircleIntegrable (fun z => a5NormalizedKernel38 n (φ, z)) (C n) (R n) ∧
      gamma2 φ n * a5LocalXi38 n (C n) (R n) φ = 4 * gkActionC38 φ n := by
  have hiA := action_circle_integrable38 φ hφ C R hf n
  have hiK := a5Kernel_own_circle_integrable38 φ hφ C R hf n
  obtain ⟨hiχ, hzχ⟩ := a5Chi_own_circle_zero38 φ hφ C R hf n
  have hr := isolating_radius_pos38 hf n
  have hiγK : CircleIntegrable (fun z => gamma2 φ n * a5NormalizedKernel38 n (φ, z))
      (C n) (R n) := by
    apply ContinuousOn.circleIntegrable hr.le
    intro z hz
    have hfull : (φ, z) ∈ rootDomain38 :=
      ⟨hφ, fixed_sphere_subset φ C R hf n hz⟩
    have hK := AnalyticAt.comp (g := a5NormalizedKernel38 n)
      (f := fun w : ℂ => (φ, w)) (a5NormalizedKernel_analytic38 n _ hfull)
      (analyticAt_const.prod analyticAt_id)
    exact (analyticAt_const.mul hK).continuousAt.continuousWithinAt
  have hI : circleIntegral (actionIntegrand38 φ) (C n) (R n) =
      gamma2 φ n * circleIntegral (fun z => a5NormalizedKernel38 n (φ, z)) (C n) (R n) := by
    calc
      _ = circleIntegral (fun z => z * a5Chi38 n (φ, z) / Complex.I +
          gamma2 φ n * a5NormalizedKernel38 n (φ, z)) (C n) (R n) :=
        circleIntegral.integral_congr hr.le (fun z hz =>
          a5ActionIntegrand_divisibility38 n (φ, z) ⟨hφ, fixed_sphere_subset φ C R hf n hz⟩)
      _ = circleIntegral (fun z => z * a5Chi38 n (φ, z) / Complex.I) (C n) (R n) +
          circleIntegral (fun z => gamma2 φ n * a5NormalizedKernel38 n (φ, z)) (C n) (R n) :=
        circleIntegral.integral_add hiχ hiγK
      _ = _ := by rw [hzχ, circleIntegral.integral_const_mul, zero_add]
  have haction : gkActionC38 φ n = contourAction38 φ (C n) (R n) :=
    action_contour_independence38 φ hφ (discC φ) C (discR φ) R
      (isolating_family38 φ hφ) hf n
  refine ⟨hiA, hiK, ?_⟩
  rw [haction]
  unfold a5LocalXi38 contourAction38
  rw [hI]
  ring

/-- The actual normalized kernel earns parameter analyticity on a full local open neighbourhood. -/
theorem a5LocalXi_analytic38 (V : Set PotPair) (hVo : IsOpen V) (hVW : V ⊆ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : ∀ φ ∈ V, IsolatingFamily38 φ C R)
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ V) (n : ℤ) :
    AnalyticOnNhd ℂ (a5LocalXi38 n (C n) (R n)) V := by
  have hjoint : AnalyticOnNhd ℂ
      (Function.uncurry (fun φ z => a5NormalizedKernel38 n (φ, z)))
      (V ×ˢ sphere (C n) (R n)) := by
    intro p hp
    exact a5NormalizedKernel_analytic38 n p
      ⟨hVW hp.1, fixed_sphere_subset p.1 C R (hf p.1 hp.1) n hp.2⟩
  have hi := Lib.parametricCircleAnalytic38 PotPair V (C n) (R n)
    (fun φ z => a5NormalizedKernel38 n (φ, z)) hVo (isolating_radius_pos38 (hf φ₀ hφ₀) n) hjoint
  exact analyticOnNhd_const.mul hi.2

/-- This is the concrete full-W local-existence input for the separately proved generic gluing API. -/
theorem a5Xi_local_divisibility38 (n : ℤ) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ V : Set PotPair, IsOpen V ∧ φ₀ ∈ V ∧ V ⊆ gkW ∧
      ∃ g : PotPair → ℂ, AnalyticOnNhd ℂ g V ∧
        ∀ φ ∈ V, gamma2 φ n * g φ = 4 * gkActionC38 φ n := by
  obtain ⟨V, hV, hVW, hVo, _hVc, C, R, hf⟩ := local_isolatingFamily φ₀ hφ₀
  have hφV := mem_of_mem_nhds hV
  exact ⟨V, hVo, hφV, hVW, a5LocalXi38 n (C n) (R n),
    a5LocalXi_analytic38 V hVo hVW C R hf φ₀ hφV n,
    fun φ hφ => (a5LocalXi_identity38 φ (hVW hφ) C R (hf φ hφ) n).2.2⟩

end
end NlsGge.GK38
