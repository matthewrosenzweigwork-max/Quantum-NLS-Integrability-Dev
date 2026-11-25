import Mathlib

/- G4-036 generic Cauchy transform lemmas (proof development, AUTHOR; not self-reviewed). Pure analysis, no NLS input. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory

namespace NlsGge.Atomic.G4036Cauchy
noncomputable section

/-- Differentiation under the integral sign for the Cauchy transform of a continuous density on the
circle parametrization, at an interior point. -/
theorem cauchy_transform_hasDerivAt {c : ℂ} {r : ℝ} {G : ℝ → ℂ} (hG : Continuous G) {z : ℂ}
    (hz : z ∈ ball c r) :
    HasDerivAt (fun y : ℂ => ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, G θ / (circleMap c r θ - y))
      (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, G θ / (circleMap c r θ - z) ^ 2) z := by
  have hr : 0 < r := by
    have := mem_ball.mp hz
    exact lt_of_le_of_lt dist_nonneg this
  set δ : ℝ := r - dist z c with hδ
  have hδpos : 0 < δ := by have := mem_ball.mp hz; linarith
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    hG.continuousOn
  have hlow : ∀ y ∈ ball z (δ / 2), ∀ θ : ℝ, δ / 2 ≤ ‖circleMap c r θ - y‖ := by
    intro y hy θ
    have h1 : dist y z < δ / 2 := mem_ball.mp hy
    have h2 : dist (circleMap c r θ) c = r := by
      rw [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
    have h3 := dist_triangle (circleMap c r θ) y c
    have h4 := dist_triangle y z c
    have h5 : dist (circleMap c r θ) y = ‖circleMap c r θ - y‖ := dist_eq_norm _ _
    rw [h5] at h3
    linarith
  have hne : ∀ y ∈ ball z (δ / 2), ∀ θ : ℝ, circleMap c r θ - y ≠ 0 := by
    intro y hy θ h
    have := hlow y hy θ
    rw [h, norm_zero] at this
    linarith
  have hcont : ∀ y ∈ ball z (δ / 2), Continuous (fun θ : ℝ => G θ / (circleMap c r θ - y)) := by
    intro y hy
    exact hG.div ((continuous_circleMap c r).sub continuous_const) (hne y hy)
  have hcont' : ∀ y ∈ ball z (δ / 2),
      Continuous (fun θ : ℝ => G θ / (circleMap c r θ - y) ^ 2) := by
    intro y hy
    exact hG.div (((continuous_circleMap c r).sub continuous_const).pow 2)
      (fun θ => pow_ne_zero 2 (hne y hy θ))
  have hzmem : z ∈ ball z (δ / 2) := mem_ball_self (by linarith)
  have hbd : ∀ y ∈ ball z (δ / 2), ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖G θ / (circleMap c r θ - y) ^ 2‖ ≤ M / (δ / 2) ^ 2 := by
    intro y hy θ hθ
    rw [norm_div, norm_pow]
    have h1 := hlow y hy θ
    have h2 : 0 < δ / 2 := by linarith
    have h3 : (δ / 2) ^ 2 ≤ ‖circleMap c r θ - y‖ ^ 2 := pow_le_pow_left₀ h2.le h1 2
    calc ‖G θ‖ / ‖circleMap c r θ - y‖ ^ 2 ≤ M / ‖circleMap c r θ - y‖ ^ 2 :=
          div_le_div_of_nonneg_right (hM θ hθ) (by positivity)
      _ ≤ M / (δ / 2) ^ 2 := by
          apply div_le_div_of_nonneg_left _ (by positivity) h3
          exact le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, by positivity⟩)
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
    (F := fun (y : ℂ) (θ : ℝ) => G θ / (circleMap c r θ - y))
    (F' := fun (y : ℂ) (θ : ℝ) => G θ / (circleMap c r θ - y) ^ 2)
    (x₀ := z) (s := ball z (δ / 2)) (ball_mem_nhds z (by linarith))
    (Filter.eventually_of_mem (ball_mem_nhds z (by linarith)) (fun y hy => (hcont y hy).aestronglyMeasurable))
    ((hcont z hzmem).intervalIntegrable _ _)
    (hcont' z hzmem).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun θ hθ y hy => hbd y hy θ ?_))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun θ _ y hy => ?_))
  · exact hmain.2
  · rw [uIoc_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)] at hθ
    exact ⟨hθ.1.le, hθ.2⟩
  · have hne' := hne y hy θ
    have h1 : HasDerivAt (fun y : ℂ => circleMap c r θ - y) (-1) y :=
      (hasDerivAt_id y).const_sub (circleMap c r θ)
    have h2 := (h1.inv hne').const_mul (G θ)
    convert h2 using 1
    · funext y'
      simp [div_eq_mul_inv]
    · field_simp


/-- Inner primitive datum on the circle. -/
def cG (c : ℂ) (r : ℝ) (K w : ℂ → ℂ) (θ : ℝ) : ℂ :=
  (K (circleMap c r θ) - 1) / w (circleMap c r θ)

def cU (c : ℂ) (r : ℝ) (K w : ℂ → ℂ) (θ : ℝ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..θ, deriv (circleMap c r) t * cG c r K w t

def cB (c : ℂ) (r : ℝ) (K w : ℂ → ℂ) (θ : ℝ) : ℂ :=
  cU c r K w θ / w (circleMap c r θ)

/-- The literal body of `ownCorrection`, with the chosen circle and the two functions as parameters. -/
def cauchyOwnCorr (c : ℂ) (r : ℝ) (K w : ℂ → ℂ) (lam : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
      (((∫ t : ℝ in (0 : ℝ)..θ,
          deriv (circleMap c r) t *
            ((K (circleMap c r t) - 1) / w (circleMap c r t))) /
          w (circleMap c r θ)) *
        deriv (circleMap c r) θ / (circleMap c r θ - lam)))

theorem cauchyOwnCorr_eq (c : ℂ) (r : ℝ) (K w : ℂ → ℂ) (lam : ℂ) :
    cauchyOwnCorr c r K w lam = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        cB c r K w θ * deriv (circleMap c r) θ / (circleMap c r θ - lam)) := rfl

theorem deriv_circleMap_continuous (c : ℂ) (r : ℝ) : Continuous (deriv (circleMap c r)) := by
  have h : deriv (circleMap c r) = fun θ => circleMap 0 r θ * Complex.I :=
    funext (deriv_circleMap c r)
  rw [h]
  exact (continuous_circleMap 0 r).mul continuous_const

theorem hasDerivAt_circleMap' (c : ℂ) (r : ℝ) (θ : ℝ) :
    HasDerivAt (circleMap c r) (deriv (circleMap c r) θ) θ :=
  (hasDerivAt_circleMap c r θ).differentiableAt.hasDerivAt

section Main

variable {c : ℂ} {r : ℝ} {K w : ℂ → ℂ} {τ g : ℂ}

theorem cw_continuous (hr : 0 < r) (hw : ∀ z ∈ sphere c r, ContinuousAt w z) :
    Continuous (fun θ : ℝ => w (circleMap c r θ)) := by
  rw [continuous_iff_continuousAt]
  intro θ
  exact ContinuousAt.comp (f := circleMap c r) (hw _ (circleMap_mem_sphere c hr.le θ))
    (continuous_circleMap c r).continuousAt

theorem cG_continuous (hr : 0 < r) (hK : ContinuousOn K (sphere c r))
    (hw : ∀ z ∈ sphere c r, ContinuousAt w z) (hw0 : ∀ z ∈ sphere c r, w z ≠ 0) :
    Continuous (cG c r K w) := by
  unfold cG
  refine Continuous.div ?_ (cw_continuous hr hw) (fun θ => hw0 _ (circleMap_mem_sphere c hr.le θ))
  exact (hK.comp_continuous (continuous_circleMap c r)
    (fun θ => circleMap_mem_sphere c hr.le θ)).sub continuous_const

theorem cU_hasDerivAt (hr : 0 < r) (hK : ContinuousOn K (sphere c r))
    (hw : ∀ z ∈ sphere c r, ContinuousAt w z) (hw0 : ∀ z ∈ sphere c r, w z ≠ 0) (θ : ℝ) :
    HasDerivAt (cU c r K w) (deriv (circleMap c r) θ * cG c r K w θ) θ := by
  have hu : Continuous (fun t : ℝ => deriv (circleMap c r) t * cG c r K w t) :=
    (deriv_circleMap_continuous c r).mul (cG_continuous hr hK hw hw0)
  exact (Continuous.integral_hasStrictDerivAt hu 0 θ).hasDerivAt


theorem cw_deriv {y : ℂ} (hw : AnalyticAt ℂ w y)
    (hsq : ∀ᶠ y' in 𝓝 y, w y' ^ 2 = (y' - τ) ^ 2 - g / 4) (hne : w y ≠ 0) :
    deriv w y = (y - τ) / w y := by
  have hd := hw.differentiableAt.hasDerivAt
  have h1 := hd.pow 2
  have h1' := h1.congr_of_eventuallyEq (f₁ := fun y' : ℂ => (y' - τ) ^ 2 - g / 4)
    (hsq.mono fun y' h => h.symm)
  have h2 : HasDerivAt (fun y' : ℂ => (y' - τ) ^ 2 - g / 4) (2 * (y - τ)) y := by
    have := (((hasDerivAt_id y).sub_const τ).pow 2).sub_const (g / 4)
    simpa using this
  have h3 := h1'.unique h2
  field_simp
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at h3
  have h4 : (2 : ℂ) * (w y * deriv w y - (y - τ)) = 0 := by linear_combination h3
  have h5 := (mul_eq_zero.mp h4).resolve_left two_ne_zero
  linear_combination h5

theorem cQ_hasDerivAt (hr : 0 < r) (hK : ContinuousOn K (sphere c r))
    (hwa : ∀ z ∈ sphere c r, AnalyticAt ℂ w z) (hw0 : ∀ z ∈ sphere c r, w z ≠ 0)
    (hsq : ∀ z ∈ sphere c r, ∀ᶠ y in 𝓝 z, w y ^ 2 = (y - τ) ^ 2 - g / 4) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => cB c r K w θ * ((circleMap c r θ - τ) ^ 2 - g / 4))
      (deriv (circleMap c r) θ * (K (circleMap c r θ) - 1) +
        cB c r K w θ * (circleMap c r θ - τ) * deriv (circleMap c r) θ) θ := by
  have hmem := circleMap_mem_sphere c hr.le θ
  have hwc : ∀ z ∈ sphere c r, ContinuousAt w z := fun z hz => (hwa z hz).continuousAt
  have hω0 : w (circleMap c r θ) ≠ 0 := hw0 _ hmem
  have hω : HasDerivAt (fun θ : ℝ => w (circleMap c r θ))
      (deriv (circleMap c r) θ * deriv w (circleMap c r θ)) θ := by
    have := (hwa _ hmem).differentiableAt.hasDerivAt.scomp θ (hasDerivAt_circleMap' c r θ)
    simpa only [smul_eq_mul, Function.comp_def] using this
  have hU := cU_hasDerivAt hr hK hwc hw0 θ
  have hBd : HasDerivAt (cB c r K w) ((deriv (circleMap c r) θ * cG c r K w θ *
      w (circleMap c r θ) - cU c r K w θ * (deriv (circleMap c r) θ * deriv w (circleMap c r θ))) /
      w (circleMap c r θ) ^ 2) θ := hU.div hω hω0
  have hP : HasDerivAt (fun θ : ℝ => (circleMap c r θ - τ) ^ 2 - g / 4)
      (2 * (circleMap c r θ - τ) * deriv (circleMap c r) θ) θ := by
    have := (((hasDerivAt_circleMap' c r θ).sub_const τ).pow 2).sub_const (g / 4)
    simpa using this
  have hQ := hBd.mul hP
  refine hQ.congr_deriv ?_
  have hsqθ := (hsq _ hmem).self_of_nhds
  have hdw := cw_deriv (hwa _ hmem) (hsq _ hmem) hω0
  rw [hdw, ← hsqθ]
  unfold cG cB
  field_simp
  ring


theorem cU_continuous (hr : 0 < r) (hK : ContinuousOn K (sphere c r))
    (hw : ∀ z ∈ sphere c r, ContinuousAt w z) (hw0 : ∀ z ∈ sphere c r, w z ≠ 0) :
    Continuous (cU c r K w) :=
  continuous_iff_continuousAt.2 fun θ => (cU_hasDerivAt hr hK hw hw0 θ).continuousAt

theorem cB_continuous (hr : 0 < r) (hK : ContinuousOn K (sphere c r))
    (hw : ∀ z ∈ sphere c r, ContinuousAt w z) (hw0 : ∀ z ∈ sphere c r, w z ≠ 0) :
    Continuous (cB c r K w) := by
  unfold cB
  exact (cU_continuous hr hK hw hw0).div (cw_continuous hr hw)
    (fun θ => hw0 _ (circleMap_mem_sphere c hr.le θ))

/-- Cauchy-projection / ODE core: analyticity of the compact nested Cauchy integral on the open disc and the
first-order ODE, given a zero period. -/
theorem cauchyOwnCorr_analytic_ode (hr : 0 < r) (hK : AnalyticOnNhd ℂ K (closedBall c r))
    (hwa : ∀ z ∈ sphere c r, AnalyticAt ℂ w z) (hw0 : ∀ z ∈ sphere c r, w z ≠ 0)
    (hsq : ∀ z ∈ sphere c r, ∀ᶠ y in 𝓝 z, w y ^ 2 = (y - τ) ^ 2 - g / 4)
    (hper : (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, deriv (circleMap c r) θ *
      ((K (circleMap c r θ) - 1) / w (circleMap c r θ))) = 0) :
    AnalyticOnNhd ℂ (cauchyOwnCorr c r K w) (ball c r) ∧
      ∀ z ∈ ball c r, ((z - τ) ^ 2 - g / 4) * deriv (cauchyOwnCorr c r K w) z +
        (z - τ) * cauchyOwnCorr c r K w z = K z - 1 := by
  have hKc : ContinuousOn K (sphere c r) := hK.continuousOn.mono sphere_subset_closedBall
  have hwc : ∀ z ∈ sphere c r, ContinuousAt w z := fun z hz => (hwa z hz).continuousAt
  have hBc : Continuous (cB c r K w) := cB_continuous hr hKc hwc hw0
  have hdc := deriv_circleMap_continuous c r
  have hγc := continuous_circleMap c r
  have hKγ : Continuous (fun θ : ℝ => K (circleMap c r θ)) :=
    hKc.comp_continuous hγc (fun θ => circleMap_mem_sphere c hr.le θ)
  have hGc : Continuous (fun θ : ℝ => cB c r K w θ * deriv (circleMap c r) θ) := hBc.mul hdc
  have hB0 : cB c r K w 0 = 0 := by simp [cB, cU]
  have hB2 : cB c r K w (2 * Real.pi) = 0 := by
    have : cU c r K w (2 * Real.pi) = 0 := hper
    simp [cB, this]
  have hTeq : cauchyOwnCorr c r K w = fun y : ℂ => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        (cB c r K w θ * deriv (circleMap c r) θ) / (circleMap c r θ - y) := by
    funext y; exact cauchyOwnCorr_eq c r K w y
  have hFd : ∀ z ∈ ball c r, HasDerivAt (cauchyOwnCorr c r K w)
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        (cB c r K w θ * deriv (circleMap c r) θ) / (circleMap c r θ - z) ^ 2) z := by
    intro z hz
    rw [hTeq]
    exact (cauchy_transform_hasDerivAt hGc hz).const_mul _
  refine ⟨?_, ?_⟩
  · exact DifferentiableOn.analyticOnNhd (fun z hz => (hFd z hz).differentiableAt.differentiableWithinAt)
      isOpen_ball
  · intro z hz
    have hne : ∀ θ : ℝ, circleMap c r θ - z ≠ 0 := by
      intro θ h
      have h1 : circleMap c r θ = z := sub_eq_zero.mp h
      have h2 := mem_ball.mp hz
      have h3 : dist (circleMap c r θ) c = r := by
        rw [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
      rw [h1] at h3
      linarith
    have hinv : Continuous (fun θ : ℝ => (circleMap c r θ - z)⁻¹) :=
      (hγc.sub continuous_const).inv₀ hne
    have hinv2 : Continuous (fun θ : ℝ => ((circleMap c r θ - z) ^ 2)⁻¹) :=
      ((hγc.sub continuous_const).pow 2).inv₀ (fun θ => pow_ne_zero 2 (hne θ))
    rw [(hFd z hz).deriv]
    rw [hTeq]
    simp only []
    -- FTC for f = (cB * P(gamma)) * (gamma - z)⁻¹
    have hQd := cQ_hasDerivAt hr hKc hwa hw0 hsq
    have hV : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => (circleMap c r θ - z)⁻¹)
        (-(deriv (circleMap c r) θ) / (circleMap c r θ - z) ^ 2) θ := fun θ =>
      ((hasDerivAt_circleMap' c r θ).sub_const z).inv (hne θ)
    have hfd : ∀ θ ∈ uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt
        (fun θ : ℝ => (cB c r K w θ * ((circleMap c r θ - τ) ^ 2 - g / 4)) * (circleMap c r θ - z)⁻¹)
        ((deriv (circleMap c r) θ * (K (circleMap c r θ) - 1) +
          cB c r K w θ * (circleMap c r θ - τ) * deriv (circleMap c r) θ) *
            (circleMap c r θ - z)⁻¹ +
          (cB c r K w θ * ((circleMap c r θ - τ) ^ 2 - g / 4)) *
            (-(deriv (circleMap c r) θ) / (circleMap c r θ - z) ^ 2)) θ :=
      fun θ _ => (hQd θ).mul (hV θ)
    have hfc : Continuous (fun θ : ℝ =>
        (deriv (circleMap c r) θ * (K (circleMap c r θ) - 1) +
          cB c r K w θ * (circleMap c r θ - τ) * deriv (circleMap c r) θ) *
            (circleMap c r θ - z)⁻¹ +
          (cB c r K w θ * ((circleMap c r θ - τ) ^ 2 - g / 4)) *
            (-(deriv (circleMap c r) θ) / (circleMap c r θ - z) ^ 2)) := by
      refine Continuous.add (Continuous.mul (Continuous.add (hdc.mul (hKγ.sub continuous_const))
        (((hBc.mul (hγc.sub continuous_const)).mul hdc))) hinv) (Continuous.mul
        (hBc.mul (((hγc.sub continuous_const).pow 2).sub continuous_const)) ?_)
      exact hdc.neg.div ((hγc.sub continuous_const).pow 2) (fun θ => pow_ne_zero 2 (hne θ))
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hfd (hfc.intervalIntegrable _ _)
    have hf0 : (cB c r K w 0 * ((circleMap c r 0 - τ) ^ 2 - g / 4)) * (circleMap c r 0 - z)⁻¹ = 0 := by
      rw [hB0]; simp
    have hf2 : (cB c r K w (2 * Real.pi) * ((circleMap c r (2 * Real.pi) - τ) ^ 2 - g / 4)) *
        (circleMap c r (2 * Real.pi) - z)⁻¹ = 0 := by
      rw [hB2]; simp
    rw [hf0, hf2, sub_zero] at hFTC
    -- the Cauchy integral formula
    have hdiff : DiffContOnCl ℂ (fun ζ : ℂ => K ζ - 1) (ball c r) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball c hr.ne']
      exact (hK.differentiableOn.sub_const 1)
    have hCauchy := hdiff.circleIntegral_sub_inv_smul hz
    simp only [circleIntegral, smul_eq_mul] at hCauchy
    -- assemble
    have hc1 : Continuous (fun θ : ℝ => (cB c r K w θ * deriv (circleMap c r) θ) /
        (circleMap c r θ - z) ^ 2) :=
      hGc.div ((hγc.sub continuous_const).pow 2) (fun θ => pow_ne_zero 2 (hne θ))
    have hc0 : Continuous (fun θ : ℝ => (cB c r K w θ * deriv (circleMap c r) θ) /
        (circleMap c r θ - z)) := hGc.div (hγc.sub continuous_const) hne
    have hcE : Continuous (fun θ : ℝ => deriv (circleMap c r) θ * (K (circleMap c r θ) - 1) /
        (circleMap c r θ - z)) :=
      (hdc.mul (hKγ.sub continuous_const)).div (hγc.sub continuous_const) hne
    have hmain : ((z - τ) ^ 2 - g / 4) * (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        (cB c r K w θ * deriv (circleMap c r) θ) / (circleMap c r θ - z) ^ 2) +
        (z - τ) * (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        (cB c r K w θ * deriv (circleMap c r) θ) / (circleMap c r θ - z)) =
        ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, deriv (circleMap c r) θ * (K (circleMap c r θ) - 1) /
          (circleMap c r θ - z) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add ((hc1.const_mul _).intervalIntegrable _ _)
          ((hc0.const_mul _).intervalIntegrable _ _)]
      have hsplit : (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
          (((z - τ) ^ 2 - g / 4) * ((cB c r K w θ * deriv (circleMap c r) θ) /
            (circleMap c r θ - z) ^ 2) + (z - τ) * ((cB c r K w θ * deriv (circleMap c r) θ) /
            (circleMap c r θ - z)))) =
          ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
          (deriv (circleMap c r) θ * (K (circleMap c r θ) - 1) / (circleMap c r θ - z) -
          ((deriv (circleMap c r) θ * (K (circleMap c r θ) - 1) +
            cB c r K w θ * (circleMap c r θ - τ) * deriv (circleMap c r) θ) *
              (circleMap c r θ - z)⁻¹ +
            (cB c r K w θ * ((circleMap c r θ - τ) ^ 2 - g / 4)) *
              (-(deriv (circleMap c r) θ) / (circleMap c r θ - z) ^ 2))) := by
        refine intervalIntegral.integral_congr (fun θ _ => ?_)
        have h1 := hne θ
        field_simp
        ring
      rw [hsplit, intervalIntegral.integral_sub (hcE.intervalIntegrable _ _) (hfc.intervalIntegrable _ _),
        hFTC, sub_zero]
    have hCauchy' : (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, deriv (circleMap c r) θ *
        (K (circleMap c r θ) - 1) / (circleMap c r θ - z)) =
        2 * (Real.pi : ℂ) * Complex.I * (K z - 1) := by
      rw [← hCauchy]
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      ring
    have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    calc ((z - τ) ^ 2 - g / 4) * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
          (cB c r K w θ * deriv (circleMap c r) θ) / (circleMap c r θ - z) ^ 2) +
        (z - τ) * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
          (cB c r K w θ * deriv (circleMap c r) θ) / (circleMap c r θ - z))
        = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (((z - τ) ^ 2 - g / 4) * (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
          (cB c r K w θ * deriv (circleMap c r) θ) / (circleMap c r θ - z) ^ 2) +
          (z - τ) * (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
          (cB c r K w θ * deriv (circleMap c r) θ) / (circleMap c r θ - z))) := by ring
      _ = K z - 1 := by rw [hmain, hCauchy']; field_simp

end Main

end
end NlsGge.Atomic.G4036Cauchy
