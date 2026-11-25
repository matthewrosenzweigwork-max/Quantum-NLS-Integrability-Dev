import NlsGge.GK38.TauGammaExterior
import NlsGge.GK38.TauGammaAnalyticMoments

/-! Boundary quotient and Cauchy recovery earn joint analyticity across both removable pair roots. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem pair_polynomial_boundary_ne_zero38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ : PotPair) (hφ : φ ∈ gkW)
    (C₀ : ℤ → ℂ) (R₀ : ℤ → ℝ) (hf : IsolatingFamily38 φ C₀ R₀)
    (n : ℤ) (z : ℂ) (hz : z ∈ sphere (C₀ n) (R₀ n)) :
    (tauN38 C R φ n - z) ^ 2 - gamma2N38 C R φ n / 4 ≠ 0 := by
  rw [← pair_polynomial_identity38 C R hsel φ hφ n z]
  obtain ⟨c, N, hg, hs⟩ := hf
  have hminus := (hs.1 n).1 (left_mem_segment ℝ _ _)
  have hplus := (hs.1 n).1 (right_mem_segment ℝ _ _)
  apply mul_ne_zero
  · intro he
    rw [sub_eq_zero.mp he] at hplus
    have hlt := mem_ball.mp hplus
    have heq := mem_sphere.mp hz
    linarith
  · intro he
    rw [sub_eq_zero.mp he] at hminus
    have hlt := mem_ball.mp hminus
    have heq := mem_sphere.mp hz
    linarith

theorem exterior_boundary_quotient38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ : PotPair) (hφ : φ ∈ gkW)
    (C₀ : ℤ → ℂ) (R₀ : ℤ → ℝ) (hf : IsolatingFamily38 φ C₀ R₀)
    (n : ℤ) (z : ℂ) (hz : z ∈ sphere (C₀ n) (R₀ n)) :
    exteriorFactor38 φ n z = -perChar φ z /
      (4 * ((tauN38 C R φ n - z) ^ 2 - gamma2N38 C R φ n / 4)) := by
  have hP := pair_polynomial_boundary_ne_zero38 C R hsel φ hφ C₀ R₀ hf n z hz
  have hF : perChar φ z = -4 *
      ((tauN38 C R φ n - z) ^ 2 - gamma2N38 C R φ n / 4) * exteriorFactor38 φ n z := by
    rw [exterior_perChar_factor38 φ n z, ← pair_polynomial_identity38 C R hsel φ hφ n z]
    ring
  apply (eq_div_iff (mul_ne_zero (by norm_num) hP)).mpr
  linear_combination hF

theorem exterior_cauchy_recovery38 (φ : PotPair) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (n : ℤ) (z : ℂ) (hz : z ∈ ball c r) :
    CircleIntegrable (fun w => exteriorFactor38 φ n w / (w - z)) c r ∧
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral (fun w => exteriorFactor38 φ n w / (w - z)) c r = exteriorFactor38 φ n z := by
  have hQ := (exterior_entire38 φ n).continuousOn.mono (subset_univ (sphere c r))
  have hn : ∀ w ∈ sphere c r, w - z ≠ 0 := by
    intro w hw he
    rw [sub_eq_zero.mp he] at hw
    have hlt := mem_ball.mp hz
    have heq := mem_sphere.mp hw
    linarith
  have hi : CircleIntegrable (fun w => exteriorFactor38 φ n w / (w - z)) c r :=
    ContinuousOn.circleIntegrable hr.le (hQ.div (continuousOn_id.sub continuousOn_const) hn)
  refine ⟨hi, ?_⟩
  have hdiff : Differentiable ℂ (exteriorFactor38 φ n) :=
    fun w => (exterior_entire38 φ n w (mem_univ _)).differentiableAt
  have hD : DiffContOnCl ℂ (exteriorFactor38 φ n) (ball c r) := hdiff.diffContOnCl
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hD.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz

theorem exterior_joint_analytic38 (V : Set PotPair) (C₀ : ℤ → ℂ) (R₀ : ℤ → ℝ)
    (hV : IsOpen V) (hVW : V ⊆ gkW) (hf : ∀ φ ∈ V, IsolatingFamily38 φ C₀ R₀) (n : ℤ) :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => exteriorFactor38 p.1 n p.2)
      (V ×ˢ ball (C₀ n) (R₀ n)) := by
  intro p hp
  let c := C₀ n
  let r := R₀ n
  have hr : 0 < r := isolating_radius_pos38 (hf p.1 hp.1) n
  let S : Set (PotPair × ℂ) := V ×ˢ ball c r
  let F : (PotPair × ℂ) → ℂ → ℂ := fun q w => -perChar q.1 w /
    (4 * ((tauN q.1 n - w) ^ 2 - gamma2 q.1 n / 4)) / (w - q.2)
  have hS : IsOpen S := hV.prod isOpen_ball
  have hF : AnalyticOnNhd ℂ (Function.uncurry F) (S ×ˢ sphere c r) := by
    intro q hq
    have hmap : AnalyticAt ℂ (fun q : (PotPair × ℂ) × ℂ => (q.1.1, q.2)) q :=
      (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
    have hP := AnalyticAt.comp (f := fun q : (PotPair × ℂ) × ℂ => (q.1.1, q.2))
      (g := fun p : PotPair × ℂ => (tauN38 discC discR p.1 n - p.2) ^ 2 - gamma2N38 discC discR p.1 n / 4)
      (pair_polynomial_analytic38 discC discR isolating_selectors_admissible38 n
        (q.1.1, q.2) ⟨hVW hq.1.1, mem_univ _⟩) hmap
    have hχ := AnalyticAt.comp (f := fun q : (PotPair × ℂ) × ℂ => (q.1.1, q.2))
      (g := fun p : PotPair × ℂ => perChar p.1 p.2)
      (analyticOnNhd_perChar_joint38 (q.1.1, q.2) (mem_univ _)) hmap
    have hpn := pair_polynomial_boundary_ne_zero38 discC discR isolating_selectors_admissible38
      q.1.1 (hVW hq.1.1) C₀ R₀ (hf q.1.1 hq.1.1) n q.2 hq.2
    have hzn : q.2 - q.1.2 ≠ 0 := by
      intro he
      have hcircle := hq.2
      rw [sub_eq_zero.mp he] at hcircle
      have hlt := mem_ball.mp hq.1.2
      have heq := mem_sphere.mp hcircle
      linarith
    exact (hχ.neg.div (analyticAt_const.mul hP) (mul_ne_zero (by norm_num) hpn)).div
      (analyticAt_snd.sub (analyticAt_snd.comp analyticAt_fst)) hzn
  have ha := (Lib.parametricCircleAnalytic38 (PotPair × ℂ) S c r F hS hr hF).2
  have hpS : p ∈ S := hp
  have hscaled : AnalyticOnNhd ℂ (fun q => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      circleIntegral (F q) c r) S := analyticOnNhd_const.mul ha
  apply (hscaled p hpS).congr
  filter_upwards [hS.mem_nhds hpS] with q hq
  have hqW := hVW hq.1
  have he : circleIntegral (F q) c r =
      circleIntegral (fun w => exteriorFactor38 q.1 n w / (w - q.2)) c r := by
    apply circleIntegral.integral_congr hr.le
    intro w hw
    dsimp only [F, tauN, gamma2]
    rw [← exterior_boundary_quotient38 discC discR isolating_selectors_admissible38
      q.1 hqW C₀ R₀ (hf q.1 hq.1) n w hw]
  rw [he]
  exact (exterior_cauchy_recovery38 q.1 c r hr n q.2 hq.2).2

end
end NlsGge.GK38
