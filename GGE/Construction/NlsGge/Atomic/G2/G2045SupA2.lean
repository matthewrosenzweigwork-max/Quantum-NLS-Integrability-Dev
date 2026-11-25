import Mathlib

                                                                                      
                                                                                            
                                                                                                                
                                                                                                                 
                                                                                                
                                                                                                         
                                                                                            
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology Real

namespace NlsGge.G2045SupA2
noncomputable section

theorem circleIntegral_inv_subst (h : ℂ → ℂ) (p : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    circleIntegral (fun z : ℂ => z ^ p * h z⁻¹) 0 ρ =
      circleIntegral (fun w : ℂ => (1 / w ^ (p + 2)) * h w) 0 ρ⁻¹ := by
  set r : ℝ := ρ⁻¹ with hr
  have hr0 : 0 < r := inv_pos.2 hρ
  set Φ : ℝ → ℂ := fun θ => deriv (circleMap 0 r) θ •
    ((1 / (circleMap 0 r θ) ^ (p + 2)) * h (circleMap 0 r θ)) with hΦ
  have hper : Function.Periodic Φ (2 * π) := by
    intro θ
    have e := periodic_circleMap 0 r θ
    simp only [hΦ, deriv_circleMap, e]
  have hL : ∀ θ : ℝ, deriv (circleMap 0 ρ) θ • ((circleMap 0 ρ θ) ^ p * h (circleMap 0 ρ θ)⁻¹) =
      Φ (-θ) := by
    intro θ
    have hz : circleMap 0 r (-θ) = (circleMap 0 ρ θ)⁻¹ := by
      simp [circleMap, Complex.exp_neg, hr, mul_comm]
    have hz0 : circleMap 0 ρ θ ≠ 0 := by
      simp [circleMap, hρ.ne']
    simp only [hΦ, deriv_circleMap, smul_eq_mul]
    rw [show circleMap 0 r (-θ) = (circleMap 0 ρ θ)⁻¹ from hz]
    generalize circleMap 0 ρ θ = z at hz0 ⊢
    rw [one_div, inv_pow, inv_inv]
    have e : z⁻¹ * z ^ (p + 2) = z * z ^ p := by
      rw [pow_add]; field_simp
    linear_combination (Complex.I * h z⁻¹) * e.symm
  have hint : circleIntegral (fun z : ℂ => z ^ p * h z⁻¹) 0 ρ = ∫ θ in (0 : ℝ)..2 * π, Φ (-θ) := by
    unfold circleIntegral
    exact intervalIntegral.integral_congr (fun θ _ => hL θ)
  rw [hint, intervalIntegral.integral_comp_neg (fun x => Φ x)]
  have := hper.intervalIntegral_add_eq (-(2 * π)) 0
  simp only [neg_zero]
  rw [show (-(2 * π) : ℝ) + 2 * π = 0 by ring] at this
  rw [this, zero_add]
  rfl

theorem laurent_circle (G : ℂ → ℂ) (hG : AnalyticAt ℂ G 0) (p : ℕ) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, ρ0 < ρ →
      circleIntegral (fun z : ℂ => z ^ p * G z⁻¹) 0 ρ =
        (2 * π * Complex.I / ((p + 1).factorial : ℂ)) * iteratedDeriv (p + 1) G 0 := by
  have hev := Complex.analyticAt_iff_eventually_differentiableAt.1 hG
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨2 / ε, by positivity, fun ρ hρ => ?_⟩
  have hρ0 : 0 < ρ := lt_trans (by positivity) hρ
  have hrε : ρ⁻¹ < ε := by
    have : 2 / ε < ρ := hρ
    rw [inv_lt_comm₀ hρ0 hε]
    calc ε⁻¹ ≤ 2 / ε := by rw [div_eq_mul_inv]; linarith [inv_pos.2 hε]
      _ < ρ := this
  have hr0 : 0 < ρ⁻¹ := inv_pos.2 hρ0
  rw [circleIntegral_inv_subst G p ρ hρ0]
  have hdiff : ∀ z ∈ ball (0 : ℂ) ρ⁻¹ \ (∅ : Set ℂ), DifferentiableAt ℂ G z := by
    intro z hz
    exact hball (lt_trans (mem_ball.1 hz.1) hrε)
  have hcont : ContinuousOn G (closedBall (0 : ℂ) ρ⁻¹) := by
    intro z hz
    exact (hball (lt_of_le_of_lt (mem_closedBall.1 hz) hrε)).continuousAt.continuousWithinAt
  have h := Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
    hr0 (p + 1) Set.countable_empty hcont hdiff
  simp only [sub_zero, smul_eq_mul] at h
  exact h

/-- Large-circle integral of `z^k F` for `F` the derivative of `f = -I z + g(z⁻¹)`. -/
theorem circle_pow_deriv (R : ℝ) (f g F : ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (hf : ∀ z : ℂ, R < ‖z‖ → HasDerivAt f (F z) z)
    (hexp : ∀ z : ℂ, R < ‖z‖ → f z = -Complex.I * z + g z⁻¹) (k : ℕ) (hk : 2 ≤ k) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, ρ0 < ρ →
      circleIntegral (fun z : ℂ => z ^ k * F z) 0 ρ =
        -(2 * π * Complex.I / ((k - 1).factorial : ℂ)) * iteratedDeriv k g 0 := by
  obtain ⟨p, rfl⟩ : ∃ p, k = p + 2 := ⟨k - 2, by omega⟩
  have hg' : AnalyticAt ℂ (deriv g) 0 := hg.deriv
  obtain ⟨ρ0, hρ0, hlau⟩ := laurent_circle (deriv g) hg' p
  have hev := Complex.analyticAt_iff_eventually_differentiableAt.1 hg
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨max (max ρ0 (|R| + 1)) (2 / ε), by positivity, fun ρ hρ => ?_⟩
  have h1 : ρ0 < ρ := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hρ
  have h2 : |R| + 1 < ρ := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hρ
  have h3 : 2 / ε < ρ := lt_of_le_of_lt (le_max_right _ _) hρ
  have hρpos : 0 < ρ := by have := abs_nonneg R; linarith
  have hrε : ρ⁻¹ < ε := by
    rw [inv_lt_comm₀ hρpos hε]
    calc ε⁻¹ ≤ 2 / ε := by rw [div_eq_mul_inv]; linarith [inv_pos.2 hε]
      _ < ρ := h3
  -- on the circle `F z = -I - z⁻² g'(z⁻¹)`
  have hFeq : ∀ z ∈ sphere (0 : ℂ) ρ, F z = -Complex.I - (z⁻¹) ^ 2 * deriv g z⁻¹ := by
    intro z hz
    have hzn : ‖z‖ = ρ := by simpa using hz
    have hRz : R < ‖z‖ := by rw [hzn]; have := le_abs_self R; linarith
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hzn; linarith
    have hgd : DifferentiableAt ℂ g z⁻¹ := by
      refine hball ?_
      rw [dist_zero_right, norm_inv, hzn]
      exact hrε
    have hopen : ∀ᶠ w in 𝓝 z, f w = -Complex.I * w + g w⁻¹ := by
      have : IsOpen {w : ℂ | R < ‖w‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [this.mem_nhds hRz] with w hw using hexp w hw
    have hd2 : HasDerivAt (fun w : ℂ => -Complex.I * w + g w⁻¹)
        (-Complex.I + deriv g z⁻¹ * (-(z ^ 2)⁻¹)) z := by
      have hinv : HasDerivAt (fun w : ℂ => w⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hz0
      have hgc : HasDerivAt g (deriv g z⁻¹) z⁻¹ := hgd.hasDerivAt
      have hcomp := HasDerivAt.comp z hgc hinv
      have hlin : HasDerivAt (fun w : ℂ => -Complex.I * w) (-Complex.I) z := by
        simpa using (hasDerivAt_id z).const_mul (-Complex.I)
      exact hlin.add hcomp
    have hd1 : HasDerivAt f (F z) z := hf z hRz
    have hd1' : HasDerivAt (fun w : ℂ => -Complex.I * w + g w⁻¹) (F z) z :=
      hd1.congr_of_eventuallyEq (hopen.mono fun w hw => hw.symm)
    rw [hd1'.unique hd2]
    simp only [inv_pow]
    ring
  have hsplit : circleIntegral (fun z : ℂ => z ^ (p + 2) * F z) 0 ρ =
      circleIntegral (fun z : ℂ => -Complex.I * z ^ (p + 2) - z ^ p * deriv g z⁻¹) 0 ρ := by
    apply circleIntegral.integral_congr hρpos.le
    intro z hz
    simp only
    rw [hFeq z hz]
    have hz0 : z ≠ 0 := by
      intro h; subst h; simp at hz; linarith
    have e : z ^ (p + 2) * z⁻¹ ^ 2 = z ^ p := by
      rw [pow_add]; field_simp
    linear_combination (-(deriv g z⁻¹)) * e
  rw [hsplit]
  have hc1 : CircleIntegrable (fun z : ℂ => -Complex.I * z ^ (p + 2)) 0 ρ := by
    apply ContinuousOn.circleIntegrable hρpos.le
    fun_prop
  have hc2 : CircleIntegrable (fun z : ℂ => z ^ p * deriv g z⁻¹) 0 ρ := by
    apply ContinuousOn.circleIntegrable hρpos.le
    intro z hz
    have hzn : ‖z‖ = ρ := by simpa using hz
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hzn; linarith
    have hga : AnalyticAt ℂ (deriv g) z⁻¹ := by
      have hh : DifferentiableOn ℂ g (ball 0 ε) := fun w hw => (hball hw).differentiableWithinAt
      exact (hh.analyticOnNhd isOpen_ball).deriv z⁻¹ (by
        rw [mem_ball, dist_zero_right, norm_inv, hzn]; exact hrε)
    exact ((continuousAt_id.pow p).mul (hga.continuousAt.comp (continuousAt_inv₀ hz0))).continuousWithinAt
  rw [circleIntegral.integral_sub hc1 hc2]
  have hz1 : circleIntegral (fun z : ℂ => -Complex.I * z ^ (p + 2)) 0 ρ = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρpos.le
      Set.countable_empty
    · fun_prop
    · intro z _; fun_prop
  have hit : iteratedDeriv (p + 1) (deriv g) 0 = iteratedDeriv (p + 2) g 0 := by
    rw [iteratedDeriv_succ' (n := p + 1)]
  rw [hz1, hlau ρ h1, zero_sub, hit, show p + 2 - 1 = p + 1 by omega, neg_mul]

end
end NlsGge.G2045SupA2
