import NlsGge.GK38.XiSqPeriod
import NlsGge.GK38.XiSqLocal

set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

def a5CenteredAnalyticTerm38 (n : ℤ) (p : PotPair × ℂ) : ℂ :=
  -(a5Chi38 n p / Complex.I) *
    ((tauN p.1 n - p.2) + gamma2 p.1 n * a5CriticalA38 n p.1)

def a5CenteredKernel38 (n : ℤ) (p : PotPair × ℂ) : ℂ :=
  a5CenteredAnalyticTerm38 n p /
    (4 * (tauN p.1 n - p.2)^2 * a5BoundaryQ38 n p * (1 + a5BoundaryQ38 n p))

theorem a5CenteredIntegrand_divisibility38 (n : ℤ) (p : PotPair × ℂ)
    (hp : p ∈ rootDomain38) :
    (p.2 - tauN p.1 n) * a5LogQuotient38 p.1 p.2 =
      a5CenteredAnalyticTerm38 n p + gamma2 p.1 n * a5CenteredKernel38 n p := by
  let w := tauN p.1 n - p.2
  let q := a5BoundaryQ38 n p
  let s := gamma2 p.1 n
  let a := a5CriticalA38 n p.1
  obtain ⟨hw, hq, hplus, hsq⟩ := a5BoundaryQ_properties38 n p hp
  have hinv := a5InverseRootDecomposition38 w q s hw hq hplus hsq
  have hδ := a5CriticalA_identity38 n p.1 hp.1
  have hdot : lamDot p.1 n - p.2 = w + s * a := by
    dsimp [w, s, a]
    linear_combination hδ
  have hratio := a5Chi_discrimDeriv_ratio38 n p hp
  have hstd : stdRoot38 (tauN p.1 n) (gamma2 p.1 n) p.2 = w * q := rfl
  have hzw : p.2 - tauN p.1 n = -w := by dsimp [w]; ring
  rw [hdot, hstd] at hratio
  have halgebra : (-w) * ((w + s * a) / (Complex.I * (w * q)) * a5Chi38 n p) =
      (-(a5Chi38 n p / Complex.I) * (w + s * a)) * (1 / q) := by
    field_simp [show w ≠ 0 from hw, show q ≠ 0 from hq, Complex.I_ne_zero]
  unfold a5LogQuotient38
  rw [hratio, hzw, halgebra, hinv]
  dsimp [a5CenteredAnalyticTerm38, a5CenteredKernel38]
  change (-(a5Chi38 n p / Complex.I) * (w + s * a)) *
      (1 + s * (1 / (4 * w^2 * q * (1 + q)))) =
    -(a5Chi38 n p / Complex.I) * (w + s * a) +
      s * ((-(a5Chi38 n p / Complex.I) * (w + s * a)) /
        (4 * w^2 * q * (1 + q)))
  ring

theorem a5CenteredAnalyticTerm_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ (a5CenteredAnalyticTerm38 n) (a5OmittedRootDomain38 n) := by
  intro p hp
  have hτ := (tauN_analytic n p.1 hp.1).comp analyticAt_fst
  have hγ := (gamma2_analytic n p.1 hp.1).comp analyticAt_fst
  have ha := (a5CriticalA_analytic38 n p.1 hp.1).comp analyticAt_fst
  exact ((a5Chi_analytic38 n p hp).div_const.neg).mul
    ((hτ.sub analyticAt_snd).add (hγ.mul ha))

theorem a5CenteredKernel_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ (a5CenteredKernel38 n) rootDomain38 := by
  intro p hp
  have homit : p ∈ a5OmittedRootDomain38 n :=
    ⟨hp.1, fun m _ => rootDomain_avoids38 hp m⟩
  have hA := a5CenteredAnalyticTerm_analytic38 n p homit
  have hw := ((tauN_analytic n p.1 hp.1).comp analyticAt_fst).sub analyticAt_snd
  have hq := a5BoundaryQ_analytic38 n p hp
  obtain ⟨hwne, hqne, hplus, _⟩ := a5BoundaryQ_properties38 n p hp
  exact hA.div (((analyticAt_const.mul (hw.pow 2)).mul hq).mul (analyticAt_const.add hq))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hwne)) hqne) hplus)

theorem a5CenteredAnalyticTerm_circle_zero38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (fun z => a5CenteredAnalyticTerm38 n (φ, z)) (C n) (R n) ∧
      circleIntegral (fun z => a5CenteredAnalyticTerm38 n (φ, z)) (C n) (R n) = 0 := by
  have hr := isolating_radius_pos38 hf n
  have ha : AnalyticOnNhd ℂ (fun z => a5CenteredAnalyticTerm38 n (φ, z))
      (closedBall (C n) (R n)) := by
    intro z hz
    exact AnalyticAt.comp (g := a5CenteredAnalyticTerm38 n) (f := fun w : ℂ => (φ, w))
      (a5CenteredAnalyticTerm_analytic38 n _
        (a5OwnClosedBall_omittedDomain38 φ hφ C R hf n z hz))
      (analyticAt_const.prod analyticAt_id)
  refine ⟨ContinuousOn.circleIntegrable hr.le
    (ha.continuousOn.mono sphere_subset_closedBall), ?_⟩
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
    (s := (∅ : Set ℂ)) countable_empty ha.continuousOn
    (fun z hz => (ha z (ball_subset_closedBall hz.1)).differentiableAt)

theorem a5Centered_circle_integrabilities38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (fun z => (z - tauN φ n) * a5LogQuotient38 φ z) (C n) (R n) ∧
      CircleIntegrable (fun z => a5CenteredKernel38 n (φ, z)) (C n) (R n) := by
  have hr := isolating_radius_pos38 hf n
  have hF : AnalyticOnNhd ℂ (fun z => (z - tauN φ n) * a5LogQuotient38 φ z)
      (sphere (C n) (R n)) :=
    (analyticOnNhd_id.sub analyticOnNhd_const).mul
      ((a5LogQuotient_analytic38 φ hφ).mono (fixed_sphere_subset φ C R hf n))
  have hK : AnalyticOnNhd ℂ (fun z => a5CenteredKernel38 n (φ, z))
      (sphere (C n) (R n)) := by
    intro z hz
    exact AnalyticAt.comp (g := a5CenteredKernel38 n) (f := fun w : ℂ => (φ, w))
      (a5CenteredKernel_analytic38 n _ ⟨hφ, fixed_sphere_subset φ C R hf n hz⟩)
      (analyticAt_const.prod analyticAt_id)
  exact ⟨ContinuousOn.circleIntegrable hr.le hF.continuousOn,
    ContinuousOn.circleIntegrable hr.le hK.continuousOn⟩

def a5CenteredLocalXi38 (n : ℤ) (c : ℂ) (r : ℝ) (φ : PotPair) : ℂ :=
  (4 / (Real.pi : ℂ)) * circleIntegral (fun z => a5CenteredKernel38 n (φ, z)) c r

theorem a5CenteredLocalXi_identity38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    gamma2 φ n * a5CenteredLocalXi38 n (C n) (R n) φ = 4 * gkActionC38 φ n := by
  have hr := isolating_radius_pos38 hf n
  obtain ⟨hiQ, hzQ⟩ := a5FixedPeriod_zero38 φ hφ C R hf n
  obtain ⟨hiF, hiK⟩ := a5Centered_circle_integrabilities38 φ hφ C R hf n
  obtain ⟨hiB, hzB⟩ := a5CenteredAnalyticTerm_circle_zero38 φ hφ C R hf n
  have hiτQ : CircleIntegrable (fun z => tauN φ n * a5LogQuotient38 φ z) (C n) (R n) := by
    apply ContinuousOn.circleIntegrable hr.le
    intro z hz
    exact (analyticAt_const.mul ((a5LogQuotient_analytic38 φ hφ) z
      (fixed_sphere_subset φ C R hf n hz))).continuousAt.continuousWithinAt
  have hiγK : CircleIntegrable (fun z => gamma2 φ n * a5CenteredKernel38 n (φ, z))
      (C n) (R n) := by
    apply ContinuousOn.circleIntegrable hr.le
    intro z hz
    have hfull : (φ, z) ∈ rootDomain38 :=
      ⟨hφ, fixed_sphere_subset φ C R hf n hz⟩
    have hK := AnalyticAt.comp (g := a5CenteredKernel38 n)
      (f := fun w : ℂ => (φ, w)) (a5CenteredKernel_analytic38 n _ hfull)
      (analyticAt_const.prod analyticAt_id)
    exact (analyticAt_const.mul hK).continuousAt.continuousWithinAt
  have hcenter : circleIntegral (actionIntegrand38 φ) (C n) (R n) =
      circleIntegral (fun z => (z - tauN φ n) * a5LogQuotient38 φ z) (C n) (R n) := by
    calc
      _ = circleIntegral (fun z => (z - tauN φ n) * a5LogQuotient38 φ z +
          tauN φ n * a5LogQuotient38 φ z) (C n) (R n) := by
        apply circleIntegral.integral_congr hr.le
        intro z _
        unfold actionIntegrand38 a5LogQuotient38
        ring
      _ = _ := by rw [circleIntegral.integral_add hiF hiτQ,
        circleIntegral.integral_const_mul, hzQ, mul_zero, add_zero]
  have hnormalized : circleIntegral (fun z => (z - tauN φ n) * a5LogQuotient38 φ z)
      (C n) (R n) = gamma2 φ n *
        circleIntegral (fun z => a5CenteredKernel38 n (φ, z)) (C n) (R n) := by
    calc
      _ = circleIntegral (fun z => a5CenteredAnalyticTerm38 n (φ, z) +
          gamma2 φ n * a5CenteredKernel38 n (φ, z)) (C n) (R n) :=
        circleIntegral.integral_congr hr.le (fun z hz =>
          a5CenteredIntegrand_divisibility38 n (φ, z)
            ⟨hφ, fixed_sphere_subset φ C R hf n hz⟩)
      _ = _ := by rw [circleIntegral.integral_add hiB hiγK,
        hzB, zero_add, circleIntegral.integral_const_mul]
  have haction := action_contour_independence38 φ hφ (discC φ) C (discR φ) R
    (isolating_family38 φ hφ) hf n
  change gamma2 φ n * a5CenteredLocalXi38 n (C n) (R n) φ =
    4 * contourAction38 φ (discC φ n) (discR φ n)
  rw [haction]
  unfold a5CenteredLocalXi38 contourAction38
  rw [hcenter, hnormalized]
  ring

end
end NlsGge.GK38
