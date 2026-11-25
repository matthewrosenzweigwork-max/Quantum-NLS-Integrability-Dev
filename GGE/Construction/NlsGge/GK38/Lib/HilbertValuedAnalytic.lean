import NlsGge.GK38.Lib.WeaklyAnalytic

/-!
# Hilbert-space-valued maps: coordinatewise analytic and locally bounded implies analytic
(library piece L3b of campaign E01)

Grébert–Kappeler book, Appendix A, Theorem A.5 (GKP Theorem 19.4): let `f : U → ℓ²(ℤ, ℂ)` be a map
on an open subset of a complex normed space whose coordinates `x ↦ f x n` are analytic and which is
locally bounded.  Then `f` is analytic, and `df(h) = ∑ₙ dfₙ(h) eₙ`.

Proof (book Thm A.5): by the Riesz representation `ℓ = ⟪w, ·⟫` with `w ∈ ℓ²`, the finite sections
`ℓ_S = ⟪∑_{n ∈ S} wₙ eₙ, ·⟫` converge to `ℓ` in operator norm (`‖ℓ - ℓ_S‖ = ‖w - ∑_S wₙ eₙ‖`).  On
a disc where `f` is bounded by `C`, `ζ ↦ ℓ_S (f (x + ζ h))` is a finite sum of analytic functions
and converges uniformly to `ζ ↦ ℓ (f (x + ζ h))` (error `≤ C ‖w - P_S w‖`), so the limit is analytic
by Weierstrass (`TendstoLocallyUniformlyOn.differentiableOn`).  This is weak analyticity;
`analyticOnNhd_of_weak_of_locBdd` (L3a) finishes.

Also: `LocBdd` from `ContinuousOn` (L3A-2 of the L3a review), needed by L3c; Weierstrass for
`ℓ²`-valued maps along a disc.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Metric Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace NlsGge.GK38.Lib

noncomputable section

/-! ### Continuity gives local boundedness (review item L3A-2 (a)) -/

section LocBdd

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] {U : Set E} {f : E → F}

/-- A map continuous on an open set is locally bounded there. -/
theorem locBdd_of_continuousOn (hU : IsOpen U) (hf : ContinuousOn f U) : LocBdd U f := by
  intro x hx
  have hc : ContinuousAt f x := hf.continuousAt (hU.mem_nhds hx)
  have : ∀ᶠ y in 𝓝 x, ‖f y‖ ≤ ‖f x‖ + 1 := by
    have := hc.tendsto.norm.eventually (gt_mem_nhds (lt_add_one ‖f x‖))
    exact this.mono fun y hy => hy.le
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff_ball.mp this
  exact ⟨r, hr, ‖f x‖ + 1, h⟩

end LocBdd

/-! ### Weierstrass for `ℓ²`-valued maps on a disc -/

section Disc

/-- Finite section of `w ∈ ℓ²(ℤ)`: `∑_{n ∈ S} wₙ eₙ`. -/
def section2 (S : Finset ℤ) (w : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 :=
  ∑ n ∈ S, lp.single 2 n (w n)

theorem tendsto_section2 (w : lp (fun _ : ℤ => ℂ) 2) :
    Tendsto (fun S : Finset ℤ => section2 S w) atTop (𝓝 w) :=
  lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := (2 : ℝ≥0∞)) (by simp) w

theorem inner_section2 (S : Finset ℤ) (w v : lp (fun _ : ℤ => ℂ) 2) :
    ⟪section2 S w, v⟫_ℂ = ∑ n ∈ S, ⟪w n, v n⟫_ℂ := by
  unfold section2
  rw [sum_inner]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [lp.inner_single_left]

/-- Weierstrass step for `ℓ²`-valued maps: if the coordinates of `g` are differentiable on an open
set `D ⊆ ℂ` and `g` is bounded on `D`, every continuous linear functional of `g` is differentiable
on `D`. -/
theorem differentiableOn_dual_comp {D : Set ℂ} (hD : IsOpen D) {g : ℂ → lp (fun _ : ℤ => ℂ) 2}
    (hc : ∀ n : ℤ, DifferentiableOn ℂ (fun ζ => g ζ n) D) {C : ℝ} (hC : ∀ ζ ∈ D, ‖g ζ‖ ≤ C)
    (ℓ : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] ℂ) : DifferentiableOn ℂ (fun ζ => ℓ (g ζ)) D := by
  set w : lp (fun _ : ℤ => ℂ) 2 := (InnerProductSpace.toDual ℂ (lp (fun _ : ℤ => ℂ) 2)).symm ℓ
    with hw
  have hℓ : ∀ v, ℓ v = ⟪w, v⟫_ℂ := fun v => by
    rw [hw, InnerProductSpace.toDual_symm_apply]
  set F : Finset ℤ → ℂ → ℂ := fun S ζ => ∑ n ∈ S, ⟪w n, g ζ n⟫_ℂ with hF
  have hFd : ∀ S, DifferentiableOn ℂ (F S) D := by
    intro S
    refine DifferentiableOn.fun_sum fun n _ => ?_
    exact (innerSL ℂ (w n)).differentiable.comp_differentiableOn (hc n)
  have hFℓ : ∀ S ζ, ⟪section2 S w, g ζ⟫_ℂ = F S ζ := fun S ζ => inner_section2 S w (g ζ)
  have hT : TendstoUniformlyOn F (fun ζ => ℓ (g ζ)) atTop D := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hC0 : 0 ≤ max C 0 := le_max_right _ _
    have hC' : ∀ ζ ∈ D, ‖g ζ‖ ≤ max C 0 := fun ζ hζ => (hC ζ hζ).trans (le_max_left _ _)
    have h1 : ∀ᶠ S : Finset ℤ in atTop, ‖section2 S w - w‖ < ε / (max C 0 + 1) := by
      have := (tendsto_section2 w)
      rw [tendsto_iff_norm_sub_tendsto_zero] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    filter_upwards [h1] with S hS ζ hζ
    rw [dist_eq_norm, hℓ, ← hFℓ, ← inner_sub_left]
    calc ‖⟪w - section2 S w, g ζ⟫_ℂ‖ ≤ ‖w - section2 S w‖ * ‖g ζ‖ := norm_inner_le_norm _ _
      _ ≤ ‖section2 S w - w‖ * max C 0 := by
        rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left (hC' ζ hζ) (norm_nonneg _)
      _ ≤ ‖section2 S w - w‖ * (max C 0 + 1) := by
        gcongr; linarith
      _ < ε / (max C 0 + 1) * (max C 0 + 1) := by
        exact mul_lt_mul_of_pos_right hS (by linarith)
      _ = ε := by field_simp
  exact TendstoLocallyUniformlyOn.differentiableOn hT.tendstoLocallyUniformlyOn
    (Filter.Eventually.of_forall hFd) hD

end Disc

/-! ### The theorem -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Coordinatewise analytic and locally bounded implies weakly analytic. -/
theorem weaklyAnalyticOn_of_coords_of_locBdd {f : E → lp (fun _ : ℤ => ℂ) 2} {U : Set E}
    (hU : IsOpen U) (hc : ∀ n : ℤ, AnalyticOnNhd ℂ (fun x => f x n) U)
    (hb : ∀ x ∈ U, ∃ r > 0, ∃ C : ℝ, ∀ y ∈ Metric.ball x r, ‖f y‖ ≤ C) :
    WeaklyAnalyticOn f U := by
  intro x hx h ℓ
  obtain ⟨r, hr, C, hrU, hC⟩ := exists_ball_of_locBdd hU hb hx
  set D : Set ℂ := {ζ : ℂ | x + ζ • h ∈ ball x r} with hD
  have hcont : Continuous (fun ζ : ℂ => x + ζ • h) := by fun_prop
  have hDo : IsOpen D := (Metric.isOpen_ball (x := x) (ε := r)).preimage hcont
  have h0 : (0 : ℂ) ∈ D := by simpa [hD] using (mem_ball_self hr : x ∈ ball x r)
  have hline : ∀ n : ℤ, DifferentiableOn ℂ (fun ζ : ℂ => f (x + ζ • h) n) D := by
    intro n ζ hζ
    have h1 : DifferentiableAt ℂ (fun y => f y n) (x + ζ • h) :=
      ((hc n) _ (hrU hζ)).differentiableAt
    have h2 : DifferentiableAt ℂ (fun ζ : ℂ => x + ζ • h) ζ := by fun_prop
    exact (h1.comp ζ h2).differentiableWithinAt
  have hd := differentiableOn_dual_comp hDo hline (fun ζ hζ => hC _ hζ) ℓ
  exact (hd.analyticAt (hDo.mem_nhds h0))

/-- **Grébert–Kappeler book Thm A.5; GKP Thm 19.4.**  A locally bounded map `f` from an open set
of a complex normed space into `ℓ²(ℤ, ℂ)` whose coordinates are analytic is analytic. -/
theorem analyticOnNhd_of_coords_of_locBdd (f : E → lp (fun _ : ℤ => ℂ) 2) {U : Set E}
    (hU : IsOpen U) (hc : ∀ n : ℤ, AnalyticOnNhd ℂ (fun x => f x n) U)
    (hb : ∀ x ∈ U, ∃ r > 0, ∃ C : ℝ, ∀ y ∈ Metric.ball x r, ‖f y‖ ≤ C) :
    AnalyticOnNhd ℂ f U :=
  analyticOnNhd_of_weak_of_locBdd hU (weaklyAnalyticOn_of_coords_of_locBdd hU hc hb) hb

/-- The coordinates of an analytic `ℓ²(ℤ)`-valued map are analytic (the easy converse). -/
theorem analyticOnNhd_coord_of_analyticOnNhd {f : E → lp (fun _ : ℤ => ℂ) 2} {U : Set E}
    (hf : AnalyticOnNhd ℂ f U) (n : ℤ) : AnalyticOnNhd ℂ (fun x => f x n) U := fun x hx =>
  ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).analyticAt (f x)).comp (hf x hx)

/-- Book Thm A.5 as an equivalence. -/
theorem analyticOnNhd_iff_coords_of_locBdd (f : E → lp (fun _ : ℤ => ℂ) 2) {U : Set E}
    (hU : IsOpen U)
    (hb : ∀ x ∈ U, ∃ r > 0, ∃ C : ℝ, ∀ y ∈ Metric.ball x r, ‖f y‖ ≤ C) :
    AnalyticOnNhd ℂ f U ↔ ∀ n : ℤ, AnalyticOnNhd ℂ (fun x => f x n) U :=
  ⟨fun hf n => analyticOnNhd_coord_of_analyticOnNhd hf n,
    fun hc => analyticOnNhd_of_coords_of_locBdd f hU hc hb⟩

/-- **Derivative formula.**  For `f` differentiable at `x`, the `n`-th coordinate of `df(h)` is
`d fₙ (h)`, and `df(h) = ∑ₙ dfₙ(h) eₙ` in `ℓ²`. -/
theorem fderiv_coord_apply {f : E → lp (fun _ : ℤ => ℂ) 2} {x : E} (hf : DifferentiableAt ℂ f x)
    (h : E) (n : ℤ) : fderiv ℂ f x h n = fderiv ℂ (fun y => f y n) x h := by
  have := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  exact (congrArg (fun L => L h) this).symm

theorem fderiv_coord {f : E → lp (fun _ : ℤ => ℂ) 2} {x : E} (hf : DifferentiableAt ℂ f x)
    (h : E) :
    HasSum (fun n : ℤ => lp.single 2 n (fderiv ℂ (fun y => f y n) x h)) (fderiv ℂ f x h) := by
  have := lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := (2 : ℝ≥0∞)) (by simp) (fderiv ℂ f x h)
  simpa only [fderiv_coord_apply hf h] using this

end Main

end

end NlsGge.GK38.Lib
