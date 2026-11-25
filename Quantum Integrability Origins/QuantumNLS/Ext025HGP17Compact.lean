import Mathlib
import QuantumNLS.Ext025HGP17Resolvent

/-! # EXT-025 GP-17 operator part, route (iii) (haiku_inventory, 2026-11-17)

Repaired contract FIN-EXT025-GP-17 (corrected), route (iii): "a proved compact resolvent".
The finite-rank conclusion for the contour projection of a closed operator `T` whose resolvent
is compact at one point `z₀` of the resolvent set.

Chain proved here:
* `compactSub`: the compact operators form a closed complex subspace of `E →L E`;
* `contour_compact`: the contour integral of compact-operator-valued resolvent is compact, hence so
  is `contourProj` (a contour integral of compact operators is compact);
* `compact_of_one_point`: compactness of `R z₀` for one `z₀ ∈ ρ` gives compactness of `R z` for all
  `z ∈ ρ`, by the resolvent identity;
* `finite_rank_of_compact_idem`: a compact idempotent has finite-dimensional range;
* `route_iii_contour`: compact resolvent at one point ⇒ the contour projection is an idempotent of
  finite rank.

No `sorry`, no new axioms. Author: haiku_inventory (EXT-025 GP-17 packaging). -/

noncomputable section
set_option autoImplicit false

open Set Metric MeasureTheory intervalIntegral Complex Real Function
open QuantumNLS.Ext025HGP17Calculus QuantumNLS.Ext025HGP17Resolvent

namespace QuantumNLS.Ext025HGP17Compact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The compact continuous linear maps, as a complex submodule of `E →L[ℂ] E`. -/
def compactSub : Submodule ℂ (E →L[ℂ] E) where
  carrier := {f | IsCompactOperator ⇑f}
  add_mem' hf hg := hf.add hg
  zero_mem' := isCompactOperator_zero
  smul_mem' c _ hf := hf.smul c

/-- The compact operators form a closed set (Mathlib). -/
theorem isClosed_compactSub : IsClosed (SetLike.coe (compactSub (E := E))) :=
  isClosed_setOfPred_isCompactOperator

/-- The contour projection of a resolvent family that is compact on the circle is compact. -/
theorem contour_compact {T : E →ₗ.[ℂ] E} {ρ : Set ℂ} {R : ℂ → E →L[ℂ] E}
    (hR : ClosedResolvent T ρ R) {c : ℂ} {r : ℝ} (h : 0 < r) (hs : sphere c r ⊆ ρ)
    (hcomp : ∀ z ∈ sphere c r, IsCompactOperator ⇑(R z)) :
    IsCompactOperator ⇑(contourProj R c r) := by
  have hR1 : ContinuousOn R (sphere c r) := hR.diff.continuousOn.mono hs
  have hint : circleIntegral R c r ∈ compactSub :=
    integral_mem_of_closed_submodule compactSub isClosed_compactSub (a := 0) (b := 2 * π)
      (by positivity)
      (g := fun θ => deriv (circleMap c r) θ • R (circleMap c r θ))
      (continuous_circleWeight h hR1).continuousOn
      (fun θ _ => compactSub.smul_mem _
        (show R (circleMap c r θ) ∈ compactSub from
          hcomp _ (circleMap_mem_sphere_of_pos h θ)))
  exact compactSub.smul_mem _ hint

/-- Compactness at one point of the resolvent set gives compactness at every point of it. -/
theorem compact_of_one_point {T : E →ₗ.[ℂ] E} {ρ : Set ℂ} {R : ℂ → E →L[ℂ] E}
    (hR : ClosedResolvent T ρ R) {z₀ z : ℂ} (hz₀ : z₀ ∈ ρ) (hz : z ∈ ρ)
    (hc₀ : IsCompactOperator ⇑(R z₀)) : IsCompactOperator ⇑(R z) := by
  have hfun : ⇑(R z) = fun u => R z₀ u + (z₀ - z) • R z (R z₀ u) := by
    funext u
    have := resolvent_identity hR hz hz₀ u
    rw [← this]
    abel
  rw [hfun]
  have h2 : IsCompactOperator (⇑(R z) ∘ ⇑(R z₀)) := hc₀.clm_comp (R z)
  have h3 : IsCompactOperator ((z₀ - z) • (⇑(R z) ∘ ⇑(R z₀))) := h2.smul (z₀ - z)
  exact hc₀.add h3

/-- A compact idempotent on a Banach space has finite-dimensional range. -/
theorem finite_rank_of_compact_idem (P : E →L[ℂ] E) (hid : P * P = P)
    (hc : IsCompactOperator ⇑P) :
    FiniteDimensional ℂ (LinearMap.range P.toLinearMap) := by
  set W := LinearMap.range P.toLinearMap with hW
  have hfix : ∀ x : E, x ∈ W → P x = x := by
    rintro x ⟨y, rfl⟩
    show P (P y) = P y
    rw [← ContinuousLinearMap.mul_apply, hid]
  have hWclosed : IsClosed (W : Set E) := by
    have hset : (W : Set E) = {x | P x = x} := by
      ext x
      constructor
      · intro hx
        exact hfix x hx
      · intro hx
        exact ⟨x, hx⟩
    rw [hset]
    exact isClosed_eq P.continuous continuous_id
  have hV : ∀ x : W, (⇑P ∘ ⇑W.subtypeL) x ∈ (W : Set E) := fun x => ⟨(x : E), rfl⟩
  have hc2 : IsCompactOperator (⇑P ∘ ⇑W.subtypeL) := hc.comp_clm W.subtypeL
  have hc3 := hc2.codRestrict (V := W) (fun x => hV x) hWclosed
  have hid' : IsCompactOperator (id : W → W) := by
    have heq : (Set.codRestrict (⇑P ∘ ⇑W.subtypeL) (W : Set E) hV : W → (W : Set E)) = id := by
      funext x
      apply Subtype.ext
      exact (hfix x.1 x.2)
    rw [← heq]
    exact hc3
  exact FiniteDimensional.of_isCompactOperator_id hid'

/-- Route (iii): a resolvent that is compact at one point `z₀ ∈ ρ` gives a contour projection
`P = (2πi)⁻¹ ∮ R` that is an idempotent (G1) of finite rank. -/
theorem route_iii_contour {T : E →ₗ.[ℂ] E} {ρ : Set ℂ} {R : ℂ → E →L[ℂ] E}
    (hR : ClosedResolvent T ρ R) {c : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hann : closedBall c r₂ \ ball c r₁ ⊆ ρ) {z₀ : ℂ} (hz₀ : z₀ ∈ ρ)
    (hc₀ : IsCompactOperator ⇑(R z₀)) :
    contourProj R c r₁ * contourProj R c r₁ = contourProj R c r₁ ∧
      FiniteDimensional ℂ (LinearMap.range (contourProj R c r₁).toLinearMap) := by
  have hs1 : sphere c r₁ ⊆ ρ := fun z hz => hann (sphere_inner_sub h₁₂.le hz)
  have hid := (contour_projection_G1 hR h₁ h₁₂ hann).2.1
  have hcomp : ∀ z ∈ sphere c r₁, IsCompactOperator ⇑(R z) :=
    fun z hz => compact_of_one_point hR hz₀ (hs1 hz) hc₀
  have hcP := contour_compact hR h₁ hs1 hcomp
  exact ⟨hid, finite_rank_of_compact_idem _ hid hcP⟩

end QuantumNLS.Ext025HGP17Compact

#print axioms QuantumNLS.Ext025HGP17Compact.route_iii_contour
#print axioms QuantumNLS.Ext025HGP17Compact.finite_rank_of_compact_idem
#print axioms QuantumNLS.Ext025HGP17Resolvent.contour_projection_G1
#print axioms QuantumNLS.Ext025HGP17Resolvent.contour_projection_bounded
#print axioms QuantumNLS.Ext025HGP17Resolvent.contourProj_mul_eq
