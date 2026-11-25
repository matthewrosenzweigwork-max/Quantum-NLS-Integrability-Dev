import NlsGge.GK38.Lib.WeaklyAnalyticTaylor

/-!
# Weakly analytic and locally bounded implies analytic (library piece L3a of campaign E01)

Grébert–Kappeler book, Appendix A, Theorem A.3 (GKP Theorem 19.3): a map `f : U → F` between
complex Banach spaces that is *weakly analytic* (`ζ ↦ L f (u + ζ h)` analytic near `0` for every
`u ∈ U`, `h ∈ E`, `L ∈ F*`) and locally bounded is analytic.

Local re-proof from Mathlib (E01-D8).  Route, in four files:

1. `WeaklyAnalyticLine`: one-variable Cauchy estimates and the Dunford step
   (`differentiableAt_of_forall_dual`): scalar analyticity plus boundedness gives vector
   differentiability along each line.
2. `WeaklyAnalyticGateaux`: continuity (Lipschitz bound on small balls), and the directional
   derivative `dirD k f` is again line-differentiable, locally bounded and additive in `k`
   (`dirD_add`, via a second-order Cauchy estimate: this is the several-variable step, with no
   Osgood/Hartogs theorem and no integrals).
3. `WeaklyAnalyticTaylor`: iterated directional derivatives `iterDirD n f x` are multilinear
   (by induction from `dirD_add`; the polarization identity is not needed, nor is symmetry) and
   satisfy the iterated Cauchy bound.
4. This file: `HasFPowerSeriesOnBall` for the series `∑ (n!)⁻¹ iterDirD n f x`, using Mathlib's Taylor
   series theorem for the one-variable functions `ζ ↦ f (x + ζ y)`.

Deviation from the plan statement: `CompleteSpace E` is not needed (only `CompleteSpace F`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Metric Set Filter Topology Function
open scoped NNReal ENNReal Nat

namespace NlsGge.GK38.Lib

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Weak analyticity in the sense of Grébert–Kappeler (book Appendix A): for every `x ∈ U`,
`h ∈ E`, `ℓ ∈ F*`, the scalar function `ζ ↦ ℓ (f (x + ζ h))` is analytic at `0`. -/
def WeaklyAnalyticOn (f : E → F) (U : Set E) : Prop :=
  ∀ x ∈ U, ∀ h : E, ∀ ℓ : F →L[ℂ] ℂ, AnalyticAt ℂ (fun ζ : ℂ => ℓ (f (x + ζ • h))) 0

section Series

variable [CompleteSpace F] {U : Set E} {f : E → F}

theorem iteratedDeriv_line (hU : IsOpen U) :
    ∀ (n : ℕ) {f : E → F}, LineGood U f → ∀ {x : E}, x ∈ U → ∀ y : E,
      iteratedDeriv n (fun ζ : ℂ => f (x + ζ • y)) 0 = iterDirD n f x (fun _ => y) := by
  intro n
  induction n with
  | zero => intro f _ x _ y; simp [iterDirD]
  | succ n ih =>
    intro f hf x hx y
    rw [iteratedDeriv_succ']
    have hc : ContinuousAt (fun t : ℂ => x + t • y) 0 := by fun_prop
    have hev : ∀ᶠ t : ℂ in 𝓝 0, x + t • y ∈ U := hc.eventually (hU.mem_nhds (by simpa using hx))
    have : deriv (fun ζ : ℂ => f (x + ζ • y)) =ᶠ[𝓝 0] fun ζ : ℂ => dirD y f (x + ζ • y) := by
      filter_upwards [hev] with t ht using (hf.1.hasDerivAt ht).deriv
    rw [Filter.EventuallyEq.iteratedDeriv_eq n this]
    exact ih (hf.dirD hU y) hx y

/-- The Taylor series of a `LineGood` map at `x`, built from `iterDirD`. -/
def lineTaylorSeries (hU : IsOpen U) (hf : LineGood U f) {x : E} (hx : x ∈ U) {r M : ℝ} (hr : 0 < r)
    (hrU : closedBall x r ⊆ U) (hM : ∀ z ∈ closedBall x r, ‖f z‖ ≤ M) :
    FormalMultilinearSeries ℂ E F := fun n =>
  ((n ! : ℂ)⁻¹) • (iterDirDML hU hf hx n).mkContinuous (M * (n : ℝ) ^ n / r ^ n) (fun m => by
    have h := norm_iterDirD_le hU (x := x) n hf r M hr.le hrU hM m
    have hrn : 0 < r ^ n := pow_pos hr n
    show ‖iterDirD n f x m‖ ≤ _
    rw [div_mul_eq_mul_div, le_div_iff₀ hrn]
    linarith)

theorem lineTaylorSeries_apply (hU : IsOpen U) (hf : LineGood U f) {x : E} (hx : x ∈ U) {r M : ℝ}
    (hr : 0 < r) (hrU : closedBall x r ⊆ U) (hM : ∀ z ∈ closedBall x r, ‖f z‖ ≤ M) (n : ℕ)
    (y : Fin n → E) :
    lineTaylorSeries hU hf hx hr hrU hM n y = ((n ! : ℂ)⁻¹) • iterDirD n f x y := rfl

theorem norm_taylorSeries_le (hU : IsOpen U) (hf : LineGood U f) {x : E} (hx : x ∈ U) {r M : ℝ}
    (hr : 0 < r) (hrU : closedBall x r ⊆ U) (hM : ∀ z ∈ closedBall x r, ‖f z‖ ≤ M) (n : ℕ) :
    ‖lineTaylorSeries hU hf hx hr hrU hM n‖ * (r / Real.exp 1) ^ n ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_closedBall_self hr.le))
  have hrn : 0 < r ^ n := pow_pos hr n
  have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h1 : ‖lineTaylorSeries hU hf hx hr hrU hM n‖ ≤ ((n ! : ℝ))⁻¹ * (M * (n : ℝ) ^ n / r ^ n) := by
    unfold lineTaylorSeries
    rw [norm_smul]
    have : ‖((n ! : ℂ)⁻¹)‖ = ((n ! : ℝ))⁻¹ := by simp
    rw [this]
    gcongr
    exact MultilinearMap.mkContinuous_norm_le _ (by positivity) _
  have hexp : (n : ℝ) ^ n / (n ! : ℝ) ≤ Real.exp 1 ^ n := by
    have := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
    have h2 : Real.exp (n : ℝ) = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
    rwa [h2] at this
  have hen : 0 < Real.exp 1 ^ n := by positivity
  calc ‖lineTaylorSeries hU hf hx hr hrU hM n‖ * (r / Real.exp 1) ^ n
      ≤ ((n ! : ℝ))⁻¹ * (M * (n : ℝ) ^ n / r ^ n) * (r / Real.exp 1) ^ n := by gcongr
    _ = M * ((n : ℝ) ^ n / (n ! : ℝ)) / Real.exp 1 ^ n := by
      rw [div_pow]; field_simp
    _ ≤ M * Real.exp 1 ^ n / Real.exp 1 ^ n := by gcongr
    _ = M := by field_simp

theorem hasFPowerSeriesOnBall_taylorSeries (hU : IsOpen U) (hf : LineGood U f) {x : E} (hx : x ∈ U)
    {r M : ℝ} (hr : 0 < r) (hrU : closedBall x r ⊆ U) (hM : ∀ z ∈ closedBall x r, ‖f z‖ ≤ M) :
    HasFPowerSeriesOnBall f (lineTaylorSeries hU hf hx hr hrU hM) x
      (((r / Real.exp 1).toNNReal : ℝ≥0) : ℝ≥0∞) := by
  have hrpos : 0 < r / Real.exp 1 := by positivity
  have hcoe : (((r / Real.exp 1).toNNReal : ℝ≥0) : ℝ) = r / Real.exp 1 :=
    Real.coe_toNNReal _ hrpos.le
  refine ⟨FormalMultilinearSeries.le_radius_of_bound _ M (fun n => ?_), ?_, ?_⟩
  · rw [hcoe]; exact norm_taylorSeries_le hU hf hx hr hrU hM n
  · exact_mod_cast (Real.toNNReal_pos.mpr hrpos)
  · intro y hy
    rw [Metric.eball_coe, mem_ball_zero_iff, hcoe] at hy
    have he : (2 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    have hy2 : 2 * ‖y‖ < r := by
      have : ‖y‖ * Real.exp 1 < r := by rwa [lt_div_iff₀ (Real.exp_pos 1)] at hy
      nlinarith [norm_nonneg y]
    set g : ℂ → F := fun ζ => f (x + ζ • y) with hg
    have hmem : ∀ ζ : ℂ, ζ ∈ ball (0 : ℂ) 2 → x + ζ • y ∈ U := by
      intro ζ hζ
      rw [mem_ball_zero_iff] at hζ
      apply hrU
      rw [mem_closedBall_iff_norm]
      have : x + ζ • y - x = ζ • y := by abel
      rw [this, norm_smul]
      nlinarith [norm_nonneg y]
    have hdiff : DifferentiableOn ℂ g (ball (0 : ℂ) 2) := fun ζ hζ =>
      (hf.1.at (hmem ζ hζ)).differentiableWithinAt
    have h1 : (1 : ℂ) ∈ ball (0 : ℂ) 2 := by simp
    have hs := Complex.hasSum_taylorSeries_on_ball hdiff h1
    have e : g 1 = f (x + y) := by simp [hg]
    rw [e] at hs
    convert hs using 2 with n
    rw [lineTaylorSeries_apply, ← iteratedDeriv_line hU n hf hx y]
    simp only [sub_zero, one_pow, one_smul]
    rfl

theorem LineGood.analyticAt (hU : IsOpen U) (hf : LineGood U f) {x : E} (hx : x ∈ U) :
    AnalyticAt ℂ f x := by
  obtain ⟨r, hr, M, hrU, hM⟩ := exists_ball_of_locBdd hU hf.2 hx
  have hr2 : 0 < r / 2 := by positivity
  have hsub : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  exact (hasFPowerSeriesOnBall_taylorSeries hU hf hx hr2 (hsub.trans hrU)
    (fun z hz => hM z (hsub hz))).analyticAt

end Series

section Main

variable [CompleteSpace F] {U : Set E} {f : E → F}

/-- Weak analyticity and local boundedness give line differentiability (Dunford step). -/
theorem lineDiff_of_weak (hU : IsOpen U) (hw : WeaklyAnalyticOn f U) (hb : LocBdd U f) :
    LineDiff U f := by
  intro x hx h
  obtain ⟨r, hr, M, hrU, hM⟩ := exists_ball_of_locBdd hU hb hx
  have hLD : ∀ ℓ : F →L[ℂ] ℂ, LineDiff U (fun y => ℓ (f y)) := fun ℓ x hx h =>
    (hw x hx h ℓ).differentiableAt
  set δ : ℝ := r / (‖h‖ + 1) with hδ
  have hδpos : 0 < δ := by positivity
  have hmem : ∀ w : ℂ, ‖w‖ < δ → x + w • h ∈ ball x r := by
    intro w hw
    rw [mem_ball_iff_norm]
    have : x + w • h - x = w • h := by abel
    rw [this, norm_smul]
    have hh : 0 ≤ ‖h‖ := norm_nonneg h
    calc ‖w‖ * ‖h‖ ≤ δ * ‖h‖ := by gcongr
      _ = r * (‖h‖ / (‖h‖ + 1)) := by rw [hδ]; field_simp
      _ < r := by
        have : ‖h‖ / (‖h‖ + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
        nlinarith
  refine differentiableAt_of_forall_dual (z₀ := 0) (δ := δ) (M := M) hδpos (fun ℓ w hw => ?_)
    (fun w hw => ?_)
  · exact (hLD ℓ).at (hrU (hmem w (by simpa using hw)))
  · exact hM _ (hmem w (by simpa using hw))

/-- **Grébert–Kappeler book Thm A.3 (1 ⇒ 2); GKP Thm 19.3.**  A weakly analytic and locally
bounded map on an open subset of a complex normed space into a complex Banach space is analytic. -/
theorem analyticOnNhd_of_weak_of_locBdd (hU : IsOpen U) (hw : WeaklyAnalyticOn f U)
    (hb : ∀ x ∈ U, ∃ r > 0, ∃ C : ℝ, ∀ y ∈ Metric.ball x r, ‖f y‖ ≤ C) : AnalyticOnNhd ℂ f U :=
  fun _ hx => LineGood.analyticAt hU ⟨lineDiff_of_weak hU hw hb, hb⟩ hx

/-- Analytic maps are weakly analytic (book Thm A.3, 2 ⇒ 1, first half). -/
theorem weaklyAnalyticOn_of_analyticOnNhd (hf : AnalyticOnNhd ℂ f U) : WeaklyAnalyticOn f U := by
  intro x hx h ℓ
  have hline : AnalyticAt ℂ (fun ζ : ℂ => x + ζ • h) 0 :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have h0 : (fun ζ : ℂ => x + ζ • h) 0 = x := by simp
  exact (ℓ.analyticAt _).comp (((hf x hx).comp_of_eq hline h0)) |>.congr (by
    exact Eventually.of_forall fun _ => rfl)

/-- Analytic maps are locally bounded (book Thm A.3, 2 ⇒ 1, second half). -/
theorem locBdd_of_analyticOnNhd (hf : AnalyticOnNhd ℂ f U) : LocBdd U f := by
  intro x hx
  have hc : ContinuousAt f x := (hf x hx).continuousAt
  have : ∀ᶠ y in 𝓝 x, ‖f y‖ ≤ ‖f x‖ + 1 := by
    have := hc.tendsto.norm.eventually (gt_mem_nhds (lt_add_one ‖f x‖))
    exact this.mono fun y hy => hy.le
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff_ball.mp this
  exact ⟨r, hr, ‖f x‖ + 1, h⟩

/-- **Holomorphy implies analyticity for maps on a complex Banach space.**  (Mathlib has this only
for maps defined on `ℂ`.) A complex Fréchet differentiable map on an open subset of a complex
normed space into a complex Banach space is analytic. -/
theorem analyticOnNhd_of_differentiableOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    AnalyticOnNhd ℂ f U := by
  have hcont : ContinuousOn f U := hf.continuousOn
  refine analyticOnNhd_of_weak_of_locBdd hU ?_ ?_
  · intro x hx h ℓ
    set phi : ℂ → ℂ := fun ζ => ℓ (f (x + ζ • h)) with hphi
    have hc : Continuous (fun ζ : ℂ => x + ζ • h) := by fun_prop
    have hopen : IsOpen {ζ : ℂ | x + ζ • h ∈ U} := hU.preimage hc
    have hmem : (0 : ℂ) ∈ {ζ : ℂ | x + ζ • h ∈ U} := by simpa using hx
    have hd : DifferentiableOn ℂ phi {ζ : ℂ | x + ζ • h ∈ U} := by
      intro ζ hζ
      have h1 : DifferentiableAt ℂ f (x + ζ • h) :=
        (hf _ hζ).differentiableAt (hU.mem_nhds hζ)
      have h2 : DifferentiableAt ℂ (fun ζ : ℂ => x + ζ • h) ζ := by fun_prop
      exact (ℓ.differentiableAt.comp ζ (h1.comp ζ h2)).differentiableWithinAt
    exact hd.analyticAt (hopen.mem_nhds hmem)
  · intro x hx
    have hc : ContinuousAt f x := hcont.continuousAt (hU.mem_nhds hx)
    have : ∀ᶠ y in 𝓝 x, ‖f y‖ ≤ ‖f x‖ + 1 := by
      have := hc.tendsto.norm.eventually (gt_mem_nhds (lt_add_one ‖f x‖))
      exact this.mono fun y hy => hy.le
    obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff_ball.mp this
    exact ⟨r, hr, ‖f x‖ + 1, h⟩

end Main

end

end NlsGge.GK38.Lib
