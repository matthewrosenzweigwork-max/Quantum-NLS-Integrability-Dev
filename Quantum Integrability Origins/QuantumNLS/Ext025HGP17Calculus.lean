import Mathlib

/-! # EXT-025 GP-17 operator calculus (haiku_inventory, 2026-11-17)

General circle-integral lemmas used by the resolvent-contour packaging (G1) and the
compact-resolvent route (G2) of the repaired contract FIN-EXT025-GP-17 (corrected),
`ops/contracts/OWNER_CONTRACT_REPAIRS_2026-11-16.md`.

Contents (Banach-valued integrands unless stated):
* `continuous_circleWeight`: the circle integrand `θ ↦ circleMap'(θ) • f(circleMap θ)` is continuous;
* `circleIntegral_clm_apply`: a continuous linear map passes through a circle integral;
* `interval_fubini`, `circle_fubini`: Fubini for interval and circle integrals of continuous functions;
* `circle_inv_inside`, `circle_inv_outside`: `∮ (w - z)⁻¹ • x` for `z` inside / `w` outside a circle;
* `integral_mem_of_closed_submodule`: an interval integral of a continuous function with values in a
  closed complex subspace lies in that subspace.

No `sorry`, no new axioms. Author: haiku_inventory (EXT-025 GP-17 packaging). -/

noncomputable section
set_option autoImplicit false

open Set Metric MeasureTheory intervalIntegral Complex Real Function

namespace QuantumNLS.Ext025HGP17Calculus

/-- Continuity of the circle-integrand weight `θ ↦ (d/dθ) circleMap c r θ • f (circleMap c r θ)`
for a radius `r > 0` and a function `f` continuous on the circle. -/
theorem continuous_circleWeight {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {f : ℂ → G} {c : ℂ} {r : ℝ} (hr : 0 < r) (hf : ContinuousOn f (sphere c r)) :
    Continuous (fun θ : ℝ => deriv (circleMap c r) θ • f (circleMap c r θ)) := by
  have hmem : ∀ θ : ℝ, circleMap c r θ ∈ sphere c r := fun θ => by
    simpa [abs_of_pos hr] using circleMap_mem_sphere' c r θ
  have h1 : Continuous (fun θ : ℝ => f (circleMap c r θ)) :=
    hf.comp_continuous (continuous_circleMap c r) hmem
  have h2 : Continuous (fun θ : ℝ => deriv (circleMap c r) θ) := by
    simp only [deriv_circleMap]
    fun_prop
  exact h2.smul h1

/-- A continuous linear map commutes with a circle integral of a function continuous on the circle. -/
theorem circleIntegral_clm_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G] (A : F →L[ℂ] G) {f : ℂ → F} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : ContinuousOn f (sphere c r)) :
    A (circleIntegral f c r) = circleIntegral (fun z => A (f z)) c r := by
  unfold circleIntegral
  rw [← A.intervalIntegral_comp_comm ((continuous_circleWeight hr hf).intervalIntegrable _ _)]
  congr 1
  funext θ
  simp only [map_smul]

/-- Fubini for interval integrals of a function continuous on the square `[a,b] × [a,b]`. -/
theorem interval_fubini {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ → H}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc a b ×ˢ Icc a b)) :
    (∫ x in a..b, ∫ y in a..b, g x y) = ∫ y in a..b, ∫ x in a..b, g x y := by
  simp only [intervalIntegral.integral_of_le hab]
  have hint : Integrable (Function.uncurry g)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  exact integral_integral_swap hint

/-- Fubini for two circle integrals of a function continuous on the product of the two circles. -/
theorem circle_fubini {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) {g : ℂ → ℂ → H}
    (hg : ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (sphere c₁ r₁ ×ˢ sphere c₂ r₂)) :
    circleIntegral (fun z => circleIntegral (fun w => g z w) c₂ r₂) c₁ r₁ =
      circleIntegral (fun w => circleIntegral (fun z => g z w) c₁ r₁) c₂ r₂ := by
  have hmem₁ : ∀ θ : ℝ, circleMap c₁ r₁ θ ∈ sphere c₁ r₁ := fun θ => by
    simpa [abs_of_pos h₁] using circleMap_mem_sphere' c₁ r₁ θ
  have hmem₂ : ∀ θ : ℝ, circleMap c₂ r₂ θ ∈ sphere c₂ r₂ := fun θ => by
    simpa [abs_of_pos h₂] using circleMap_mem_sphere' c₂ r₂ θ
  have hc1 : Continuous (fun p : ℝ × ℝ => (circleMap c₁ r₁ p.1, circleMap c₂ r₂ p.2)) :=
    ((continuous_circleMap c₁ r₁).comp continuous_fst).prodMk
      ((continuous_circleMap c₂ r₂).comp continuous_snd)
  have hmaps : MapsTo (fun p : ℝ × ℝ => (circleMap c₁ r₁ p.1, circleMap c₂ r₂ p.2))
      univ (sphere c₁ r₁ ×ˢ sphere c₂ r₂) := fun p _ => ⟨hmem₁ p.1, hmem₂ p.2⟩
  have hgc : ContinuousOn
      (fun p : ℝ × ℝ => g (circleMap c₁ r₁ p.1) (circleMap c₂ r₂ p.2)) univ :=
    hg.comp hc1.continuousOn hmaps
  have hd1 : ContinuousOn (fun p : ℝ × ℝ => deriv (circleMap c₁ r₁) p.1) univ := by
    have : Continuous (fun p : ℝ × ℝ => deriv (circleMap c₁ r₁) p.1) := by
      simp only [deriv_circleMap]
      fun_prop
    exact this.continuousOn
  have hd2 : ContinuousOn (fun p : ℝ × ℝ => deriv (circleMap c₂ r₂) p.2) univ := by
    have : Continuous (fun p : ℝ × ℝ => deriv (circleMap c₂ r₂) p.2) := by
      simp only [deriv_circleMap]
      fun_prop
    exact this.continuousOn
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => deriv (circleMap c₁ r₁) p.1 •
        deriv (circleMap c₂ r₂) p.2 • g (circleMap c₁ r₁ p.1) (circleMap c₂ r₂ p.2))
      (Icc (0 : ℝ) (2 * π) ×ˢ Icc (0 : ℝ) (2 * π)) :=
    (hd1.smul (hd2.smul hgc)).mono (subset_univ _)
  have hF := interval_fubini (a := 0) (b := 2 * π) (by positivity)
    (g := fun θ₁ θ₂ => deriv (circleMap c₁ r₁) θ₁ •
      deriv (circleMap c₂ r₂) θ₂ • g (circleMap c₁ r₁ θ₁) (circleMap c₂ r₂ θ₂)) hcont
  simp only [circleIntegral]
  calc (∫ θ₁ in (0 : ℝ)..2 * π, deriv (circleMap c₁ r₁) θ₁ •
          ∫ θ₂ in (0 : ℝ)..2 * π, deriv (circleMap c₂ r₂) θ₂ • g (circleMap c₁ r₁ θ₁) (circleMap c₂ r₂ θ₂))
      = ∫ θ₁ in (0 : ℝ)..2 * π, ∫ θ₂ in (0 : ℝ)..2 * π, deriv (circleMap c₁ r₁) θ₁ •
          deriv (circleMap c₂ r₂) θ₂ • g (circleMap c₁ r₁ θ₁) (circleMap c₂ r₂ θ₂) := by
        congr 1
        funext θ₁
        rw [intervalIntegral.integral_smul]
    _ = ∫ θ₂ in (0 : ℝ)..2 * π, ∫ θ₁ in (0 : ℝ)..2 * π, deriv (circleMap c₁ r₁) θ₁ •
          deriv (circleMap c₂ r₂) θ₂ • g (circleMap c₁ r₁ θ₁) (circleMap c₂ r₂ θ₂) := hF
    _ = ∫ θ₂ in (0 : ℝ)..2 * π, deriv (circleMap c₂ r₂) θ₂ •
          ∫ θ₁ in (0 : ℝ)..2 * π, deriv (circleMap c₁ r₁) θ₁ •
            g (circleMap c₁ r₁ θ₁) (circleMap c₂ r₂ θ₂) := by
        congr 1
        funext θ₂
        rw [← intervalIntegral.integral_smul]
        congr 1
        funext θ₁
        rw [smul_comm]

/-- Cauchy integral of `(w - z)⁻¹ • x` over a circle, for `z` inside the circle. -/
theorem circle_inv_inside {c z : ℂ} {r : ℝ} (hz : z ∈ ball c r) {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G] (x : G) :
    circleIntegral (fun w => (w - z)⁻¹ • x) c r = (2 * π * Complex.I) • x := by
  rw [circleIntegral.integral_smul_const, circleIntegral.integral_sub_inv_of_mem_ball hz]

/-- Cauchy integral of `(w - z)⁻¹ • x` over a circle, for `w` outside the closed disc. -/
theorem circle_inv_outside {c w : ℂ} {r : ℝ} (hr : 0 ≤ r) (hw : w ∉ closedBall c r)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G] (x : G) :
    circleIntegral (fun z => (w - z)⁻¹ • x) c r = 0 := by
  have hne : ∀ z ∈ closedBall c r, w - z ≠ 0 := fun z hz h => hw (by
    rw [sub_eq_zero] at h
    exact h ▸ hz)
  apply circleIntegral_eq_zero_of_differentiable_on_off_countable (s := ∅) hr countable_empty
  · exact (((continuousOn_const.sub continuousOn_id).inv₀ (fun z hz => hne z hz)).smul
      continuousOn_const)
  · intro z hz
    exact (((differentiableAt_const w).sub differentiableAt_id).inv
      (hne z (ball_subset_closedBall hz.1))).smul_const x

/-- An interval integral of a continuous function with values in a closed complex subspace
lies in that subspace. -/
theorem integral_mem_of_closed_submodule {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (K : Submodule ℂ F) (hK : IsClosed (K : Set F)) {a b : ℝ} (hab : a < b)
    {g : ℝ → F} (hg : ContinuousOn g (Icc a b)) (hmem : ∀ θ ∈ Icc a b, g θ ∈ K) :
    (∫ θ in a..b, g θ) ∈ K := by
  have hconv : Convex ℝ (K : Set F) := by
    intro x hx y hy s t hs ht _
    show s • x + t • y ∈ K
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact K.add_mem (K.smul_mem _ hx) (K.smul_mem _ hy)
  have hvol : volume (Ioc a b) = ENNReal.ofReal (b - a) := Real.volume_Ioc
  have hpos : (volume (Ioc a b)).toReal = b - a := by
    rw [hvol, ENNReal.toReal_ofReal (sub_nonneg.2 hab.le)]
  have h0 : volume (Ioc a b) ≠ 0 := by
    rw [hvol]
    exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
  have ht : volume (Ioc a b) ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.ofReal_ne_top
  have hfs : ∀ᵐ θ ∂(volume.restrict (Ioc a b)), g θ ∈ K :=
    ae_restrict_of_forall_mem measurableSet_Ioc (fun θ hθ => hmem θ (Ioc_subset_Icc_self hθ))
  have hfi : IntegrableOn g (Ioc a b) volume :=
    (hg.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have havg : (⨍ θ in Ioc a b, g θ) ∈ K :=
    Convex.set_average_mem hconv hK h0 ht hfs hfi
  have hne : volume.real (Ioc a b) ≠ 0 := by
    show (volume (Ioc a b)).toReal ≠ 0
    rw [hpos]
    exact (sub_pos.2 hab).ne'
  have hint : (∫ θ in a..b, g θ) = volume.real (Ioc a b) • (⨍ θ in Ioc a b, g θ) := by
    rw [intervalIntegral.integral_of_le hab.le, setAverage_eq, smul_smul,
      mul_inv_cancel₀ hne, one_smul]
  rw [hint, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact K.smul_mem _ havg

end QuantumNLS.Ext025HGP17Calculus
