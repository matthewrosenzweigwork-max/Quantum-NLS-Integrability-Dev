import Mathlib

/-!
# Analytic logarithms on the unit disk, even case, Taylor and Cauchy bounds
-/

open Complex Metric Set
open scoped Nat

namespace NlsGge.Analysis

/-- A function `ℓ` with `exp (ℓ ζ) = g ζ` on the open unit ball and `g` differentiable and
nonvanishing there has `HasDerivAt ℓ (deriv g ζ / g ζ) ζ`. -/
theorem hasDerivAt_log_of_exp_eq38 {g ℓ : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball (0:ℂ) 1)) (hne : ∀ ζ ∈ ball (0:ℂ) 1, g ζ ≠ 0)
    (hℓ : DifferentiableOn ℂ ℓ (ball (0:ℂ) 1))
    (hexp : ∀ ζ ∈ ball (0:ℂ) 1, Complex.exp (ℓ ζ) = g ζ) {ζ : ℂ} (hζ : ζ ∈ ball (0:ℂ) 1) :
    HasDerivAt ℓ (deriv g ζ / g ζ) ζ := by
  have hn : ball (0:ℂ) 1 ∈ nhds ζ := isOpen_ball.mem_nhds hζ
  have hℓd : HasDerivAt ℓ (deriv ℓ ζ) ζ := (hℓ.differentiableAt hn).hasDerivAt
  have h1 : HasDerivAt (fun z => Complex.exp (ℓ z)) (Complex.exp (ℓ ζ) * deriv ℓ ζ) ζ :=
    hℓd.cexp
  have h2 : HasDerivAt g (deriv g ζ) ζ := (hg.differentiableAt hn).hasDerivAt
  have h3 : (fun z => Complex.exp (ℓ z)) =ᶠ[nhds ζ] g :=
    Filter.eventually_of_mem hn hexp
  have h4 := h1.unique (h2.congr_of_eventuallyEq h3)
  have hgz := hne ζ hζ
  have : deriv ℓ ζ = deriv g ζ / g ζ := by
    rw [eq_div_iff hgz, ← hexp ζ hζ, mul_comm]; exact h4
  rw [← this]; exact hℓd

/-- Uniqueness of analytic logarithms on the unit ball with prescribed value at `0`. -/
theorem log_unique_ball38 {g ℓ₁ ℓ₂ : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball (0:ℂ) 1)) (hne : ∀ ζ ∈ ball (0:ℂ) 1, g ζ ≠ 0)
    (h₁ : DifferentiableOn ℂ ℓ₁ (ball (0:ℂ) 1)) (h₂ : DifferentiableOn ℂ ℓ₂ (ball (0:ℂ) 1))
    (e₁ : ∀ ζ ∈ ball (0:ℂ) 1, Complex.exp (ℓ₁ ζ) = g ζ)
    (e₂ : ∀ ζ ∈ ball (0:ℂ) 1, Complex.exp (ℓ₂ ζ) = g ζ) (h0 : ℓ₁ 0 = ℓ₂ 0) :
    ∀ ζ ∈ ball (0:ℂ) 1, ℓ₁ ζ = ℓ₂ ζ := by
  have hd : DifferentiableOn ℂ (fun z => ℓ₁ z - ℓ₂ z) (ball (0:ℂ) 1) := h₁.sub h₂
  have hz : (ball (0:ℂ) 1).EqOn (deriv fun z => ℓ₁ z - ℓ₂ z) 0 := by
    intro ζ hζ
    have hn : ball (0:ℂ) 1 ∈ nhds ζ := isOpen_ball.mem_nhds hζ
    have := (hasDerivAt_log_of_exp_eq38 hg hne h₁ e₁ hζ).sub
      (hasDerivAt_log_of_exp_eq38 hg hne h₂ e₂ hζ)
    have h' : HasDerivAt (fun z => ℓ₁ z - ℓ₂ z) _ ζ := this
    rw [h'.deriv]; simp
  intro ζ hζ
  have := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0:ℂ) 1).isPreconnected hd hz hζ
    (mem_ball_self one_pos)
  have h' : ℓ₁ ζ - ℓ₂ ζ = ℓ₁ 0 - ℓ₂ 0 := this
  rw [h0, sub_self] at h'
  exact sub_eq_zero.mp h'

/-- (1) Existence of an analytic logarithm of a nonvanishing holomorphic function on the
open unit disk, with prescribed value at `0`. -/
theorem exists_analytic_log_ball38 {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball (0:ℂ) 1)) (hne : ∀ ζ ∈ ball (0:ℂ) 1, g ζ ≠ 0)
    {ℓ₀ : ℂ} (h0 : Complex.exp ℓ₀ = g 0) :
    ∃ ℓ : ℂ → ℂ, AnalyticOnNhd ℂ ℓ (ball (0:ℂ) 1) ∧
      (∀ ζ ∈ ball (0:ℂ) 1, Complex.exp (ℓ ζ) = g ζ) ∧ ℓ 0 = ℓ₀ := by
  have hq : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball (0:ℂ) 1) := by
    refine DifferentiableOn.div ?_ hg hne
    exact (hg.analyticOnNhd isOpen_ball).deriv.differentiableOn
  obtain ⟨h, hh0, hh⟩ := (hq.isExactOn_ball).with_val_at 0 ℓ₀
  have hhd : DifferentiableOn ℂ h (ball (0:ℂ) 1) := fun z hz => (hh z hz).differentiableAt.differentiableWithinAt
  have hF : DifferentiableOn ℂ (fun z => Complex.exp (h z) / g z) (ball (0:ℂ) 1) :=
    (hhd.cexp).div hg hne
  have hz : (ball (0:ℂ) 1).EqOn (deriv fun z => Complex.exp (h z) / g z) 0 := by
    intro ζ hζ
    have hn : ball (0:ℂ) 1 ∈ nhds ζ := isOpen_ball.mem_nhds hζ
    have h1 := (hh ζ hζ).cexp
    have h2 : HasDerivAt g (deriv g ζ) ζ := (hg.differentiableAt hn).hasDerivAt
    have h3 := h1.div h2 (hne ζ hζ)
    have h3' : HasDerivAt (fun z => Complex.exp (h z) / g z) _ ζ := h3
    rw [h3'.deriv]
    have := hne ζ hζ
    simp only [Pi.zero_apply]
    field_simp
    ring
  have hexp : ∀ ζ ∈ ball (0:ℂ) 1, Complex.exp (h ζ) = g ζ := by
    intro ζ hζ
    have := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0:ℂ) 1).isPreconnected hF hz hζ
      (mem_ball_self one_pos)
    simp only [hh0, h0] at this
    have h0ne := hne 0 (mem_ball_self one_pos)
    rw [div_self h0ne] at this
    rwa [div_eq_one_iff_eq (hne ζ hζ)] at this
  exact ⟨h, hhd.analyticOnNhd isOpen_ball, hexp, hh0⟩

/-- (2) Every analytic logarithm of an even nonvanishing function on the disk is even. -/
theorem log_even_of_even38 {g ℓ : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball (0:ℂ) 1)) (hne : ∀ ζ ∈ ball (0:ℂ) 1, g ζ ≠ 0)
    (hge : ∀ ζ ∈ ball (0:ℂ) 1, g (-ζ) = g ζ)
    (hℓ : DifferentiableOn ℂ ℓ (ball (0:ℂ) 1))
    (hexp : ∀ ζ ∈ ball (0:ℂ) 1, Complex.exp (ℓ ζ) = g ζ) :
    ∀ ζ ∈ ball (0:ℂ) 1, ℓ (-ζ) = ℓ ζ := by
  have hmem : ∀ ζ ∈ ball (0:ℂ) 1, -ζ ∈ ball (0:ℂ) 1 := by
    intro ζ hζ; simpa using hζ
  have hd : DifferentiableOn ℂ (fun z => ℓ (-z)) (ball (0:ℂ) 1) :=
    hℓ.comp differentiableOn_id.neg hmem
  have := log_unique_ball38 hg hne hd hℓ
    (fun ζ hζ => by rw [hexp _ (hmem ζ hζ), hge ζ hζ]) hexp (by simp)
  exact this

/-- Existence of an analytic even logarithm. -/
theorem exists_even_analytic_log_ball38 {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball (0:ℂ) 1)) (hne : ∀ ζ ∈ ball (0:ℂ) 1, g ζ ≠ 0)
    (hge : ∀ ζ ∈ ball (0:ℂ) 1, g (-ζ) = g ζ)
    {ℓ₀ : ℂ} (h0 : Complex.exp ℓ₀ = g 0) :
    ∃ ℓ : ℂ → ℂ, AnalyticOnNhd ℂ ℓ (ball (0:ℂ) 1) ∧
      (∀ ζ ∈ ball (0:ℂ) 1, Complex.exp (ℓ ζ) = g ζ) ∧ ℓ 0 = ℓ₀ ∧
      ∀ ζ ∈ ball (0:ℂ) 1, ℓ (-ζ) = ℓ ζ := by
  obtain ⟨ℓ, ha, he, h00⟩ := exists_analytic_log_ball38 hg hne h0
  exact ⟨ℓ, ha, he, h00, log_even_of_even38 hg hne hge ha.differentiableOn he⟩


/-! ### Taylor expansion -/

/-- (3a) A function differentiable on the open unit ball has a power series on the whole ball. -/
theorem exists_hasFPowerSeriesOnBall_ball38 {ℓ : ℂ → ℂ}
    (hℓ : DifferentiableOn ℂ ℓ (ball (0:ℂ) 1)) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesOnBall ℓ p 0 1 := by
  have key : ∀ r' : NNReal, 0 < r' → (r' : ℝ) < 1 →
      HasFPowerSeriesOnBall ℓ (cauchyPowerSeries ℓ 0 r') 0 r' := by
    intro r' hr' hr1
    exact (hℓ.mono (closedBall_subset_ball hr1)).hasFPowerSeriesOnBall hr'
  have hh : HasFPowerSeriesOnBall ℓ (cauchyPowerSeries ℓ 0 (1/2 : NNReal)) 0 ((1/2 : NNReal) : ENNReal) :=
    key (1/2) (by norm_num) (by norm_num)
  refine ⟨cauchyPowerSeries ℓ 0 (1/2 : NNReal), ?_⟩
  have hex : ∀ r' : NNReal, 0 < r' → ((r' : ℝ) < 1) →
      HasFPowerSeriesOnBall ℓ (cauchyPowerSeries ℓ 0 (1/2 : NNReal)) 0 r' :=
    fun r' hr' hr1 => hh.exchange_radius (key r' hr' hr1)
  refine
    { r_le := ENNReal.le_of_forall_pos_nnreal_lt fun r hr hr1 => ?_
      r_pos := one_pos
      hasSum := fun {y} hy => ?_ }
  · have : (r : ℝ) < 1 := by exact_mod_cast hr1
    exact (hex r hr this).r_le
  · have hy' : ‖y‖₊ < 1 := by
      have : ((‖y‖₊ : NNReal) : ENNReal) < 1 := by
        simpa [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] using hy
      exact_mod_cast this
    obtain ⟨r', h1, h2⟩ := exists_between hy'
    have hr'0 : 0 < r' := lt_of_le_of_lt (zero_le) h1
    have h2' : (r' : ℝ) < 1 := by exact_mod_cast h2
    exact (hex r' hr'0 h2').hasSum (mem_eball_zero_iff.mpr (ENNReal.coe_lt_coe.2 h1))

/-- Odd Taylor coefficients of an even function vanish. -/
theorem iteratedDeriv_odd_eq_zero38 {ℓ : ℂ → ℂ}
    (hev : ∀ ζ ∈ ball (0:ℂ) 1, ℓ (-ζ) = ℓ ζ) (n : ℕ) (hn : Odd n) :
    iteratedDeriv n ℓ 0 = 0 := by
  have h1 : (fun x => ℓ (-x)) =ᶠ[nhds (0:ℂ)] ℓ :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) hev
  have h2 := iteratedDeriv_comp_neg n ℓ 0
  rw [h1.iteratedDeriv_eq, neg_zero, hn.neg_one_pow] at h2
  have : (2:ℂ) * iteratedDeriv n ℓ 0 = 0 := by
    have h3 : iteratedDeriv n ℓ 0 = -iteratedDeriv n ℓ 0 := by simpa using h2
    linear_combination h3
  simpa using this

/-- Even Taylor coefficients `C k = ℓ^{(2(k+1))}(0) / (2(k+1))!`. -/
noncomputable def evenLogCoeff38 (ℓ : ℂ → ℂ) (k : ℕ) : ℂ :=
  iteratedDeriv (2 * (k + 1)) ℓ 0 / ((2 * (k + 1))! : ℂ)

/-- (3b) Taylor expansion of an even function on the unit ball, with summability. -/
theorem hasSum_even_taylor38 {ℓ : ℂ → ℂ}
    (hℓ : DifferentiableOn ℂ ℓ (ball (0:ℂ) 1))
    (hev : ∀ ζ ∈ ball (0:ℂ) 1, ℓ (-ζ) = ℓ ζ) {ζ : ℂ} (hζ : ζ ∈ ball (0:ℂ) 1) :
    HasSum (fun k : ℕ => evenLogCoeff38 ℓ k * ζ ^ (2 * (k + 1))) (ℓ ζ - ℓ 0) := by
  have hS := Complex.hasSum_taylorSeries_on_ball hℓ hζ
  simp only [sub_zero, smul_eq_mul] at hS
  set f : ℕ → ℂ := fun n => ((n ! : ℂ))⁻¹ * (ζ ^ n * iteratedDeriv n ℓ 0) with hf
  have hodd : HasSum (fun k : ℕ => f (2 * k + 1)) 0 := by
    have : (fun k : ℕ => f (2 * k + 1)) = fun _ => 0 := by
      funext k
      simp [hf, iteratedDeriv_odd_eq_zero38 hev (2 * k + 1) (odd_two_mul_add_one k)]
    rw [this]; exact hasSum_zero
  have hsum : Summable f := hS.summable
  have hevens : HasSum (fun k : ℕ => f (2 * k)) (ℓ ζ) := by
    have hs : Summable (fun k : ℕ => f (2 * k)) :=
      hsum.comp_injective (fun a b h => by simpa using h)
    have := hs.hasSum.even_add_odd hodd
    rw [add_zero] at this
    exact this.unique hS ▸ hs.hasSum
  have h2 := (hasSum_nat_add_iff' 1).mpr hevens
  simp only [Finset.range_one, Finset.sum_singleton] at h2
  convert h2 using 1
  · funext k
    simp only [hf, evenLogCoeff38]
    ring_nf
  · simp [hf]

/-- Taylor expansion with `tsum` and summability. -/
theorem even_taylor_tsum38 {ℓ : ℂ → ℂ}
    (hℓ : DifferentiableOn ℂ ℓ (ball (0:ℂ) 1))
    (hev : ∀ ζ ∈ ball (0:ℂ) 1, ℓ (-ζ) = ℓ ζ) {ζ : ℂ} (hζ : ζ ∈ ball (0:ℂ) 1) :
    Summable (fun k : ℕ => evenLogCoeff38 ℓ k * ζ ^ (2 * (k + 1))) ∧
      ℓ ζ = ℓ 0 + ∑' k : ℕ, evenLogCoeff38 ℓ k * ζ ^ (2 * (k + 1)) := by
  have h := hasSum_even_taylor38 hℓ hev hζ
  exact ⟨h.summable, by rw [h.tsum_eq]; ring⟩


/-! ### Cauchy bounds -/

/-- (4a) Cauchy estimate with an explicit bound `M` on the circle of radius `ρ`. -/
theorem norm_evenLogCoeff_le38 {ℓ : ℂ → ℂ}
    (hℓ : DifferentiableOn ℂ ℓ (ball (0:ℂ) 1)) {ρ M : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hM : ∀ z ∈ sphere (0:ℂ) ρ, ‖ℓ z‖ ≤ M) (k : ℕ) :
    ‖evenLogCoeff38 ℓ k‖ ≤ M * (ρ ^ (2 * (k + 1)))⁻¹ := by
  have hsub : closedBall (0:ℂ) ρ ⊆ ball (0:ℂ) 1 := closedBall_subset_ball hρ1
  have hd : DiffContOnCl ℂ ℓ (ball (0:ℂ) ρ) :=
    (hℓ.mono (closure_ball_subset_closedBall.trans hsub)).diffContOnCl
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (2 * (k + 1)) hρ hd hM
  have hfac : (0:ℝ) < ((2 * (k + 1))! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  unfold evenLogCoeff38
  rw [norm_div]
  have hn : ‖(((2 * (k + 1))! : ℕ) : ℂ)‖ = ((2 * (k + 1))! : ℝ) := by
    simp
  rw [hn, div_le_iff₀ hfac]
  calc ‖iteratedDeriv (2 * (k + 1)) ℓ 0‖ ≤ ((2 * (k + 1))! : ℝ) * M / ρ ^ (2 * (k + 1)) := h
    _ = M * (ρ ^ (2 * (k + 1)))⁻¹ * ((2 * (k + 1))! : ℝ) := by ring

/-- The supremum of `‖ℓ‖` over the circle of radius `ρ` (real `iSup`; bounded for continuous `ℓ`). -/
noncomputable def circleSup38 (ℓ : ℂ → ℂ) (ρ : ℝ) : ℝ := ⨆ z : sphere (0:ℂ) ρ, ‖ℓ z‖

/-- (4b) Cauchy bound with the supremum over the circle. -/
theorem norm_evenLogCoeff_le_circleSup38 {ℓ : ℂ → ℂ}
    (hℓ : DifferentiableOn ℂ ℓ (ball (0:ℂ) 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (k : ℕ) :
    ‖evenLogCoeff38 ℓ k‖ ≤ circleSup38 ℓ ρ * (ρ ^ (2 * (k + 1)))⁻¹ := by
  have hsub : sphere (0:ℂ) ρ ⊆ ball (0:ℂ) 1 :=
    (sphere_subset_closedBall).trans (closedBall_subset_ball hρ1)
  have hc : ContinuousOn (fun z => ‖ℓ z‖) (sphere (0:ℂ) ρ) :=
    (hℓ.continuousOn.mono hsub).norm
  have hbdd : BddAbove (Set.range fun z : sphere (0:ℂ) ρ => ‖ℓ z‖) := by
    have := (isCompact_sphere (0:ℂ) ρ).image_of_continuousOn hc
    obtain ⟨B, hB⟩ := this.bddAbove
    exact ⟨B, by rintro _ ⟨z, rfl⟩; exact hB ⟨z, z.2, rfl⟩⟩
  exact norm_evenLogCoeff_le38 hℓ hρ hρ1 (fun z hz => le_ciSup hbdd ⟨z, hz⟩) k

end NlsGge.Analysis
