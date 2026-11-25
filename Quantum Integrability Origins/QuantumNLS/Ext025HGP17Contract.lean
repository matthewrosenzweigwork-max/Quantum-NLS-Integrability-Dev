import Mathlib
import QuantumNLS.Ext025HGP17Argument
import QuantumNLS.Ext025HGP17Rouche
import QuantumNLS.Ext025HGP17Compact
import QuantumNLS.Ext025HGP17Consumers

/-! # EXT-025 GP-17 full contract (haiku_inventory, 2026-11-17)

`contract_GP17_full`: the repaired GP-17 contract FIN-EXT025-GP-17 (corrected),
`ops/contracts/OWNER_CONTRACT_REPAIRS_2026-11-16.md`, packaged as one proposition with six conjuncts:

1. scalar argument principle with multiplicities (`Ext025HGP17Argument.argument_principle`);
2. scalar Rouché by integer-valued continuity (`Ext025HGP17Rouche.rouche`);
3. operator part, closed operators through the resolvent: the contour projection is independent of
   the radius, idempotent, maps `T.domain` into itself, and commutes with `T` on `T.domain`
   (`Ext025HGP17Resolvent.contour_projection_G1`);
4. operator part, bounded case as a corollary (`Ext025HGP17Resolvent.contour_projection_bounded`);
5. route (i) (`Ext025HGP17Routes.route_i`), route (ii) (`Ext025HGP17Routes.route_ii`, frozen rank
   continuation), and route (iii) (`Ext025HGP17Compact.route_iii_contour`, compact resolvent at one
   point) as finite-rank conclusions.

OWNER CHOICE and SOURCE AMBIGUITY (recorded, not resolved). The convention "algebraic multiplicity
of an isolated spectral set := rank of its Riesz projection" (Kato's convention) is an explicit
OWNER CHOICE, addendum 2026-11-17T20:00Z to `ops/contracts/OWNER_DECISIONS_EXT025_GP14_GP04_GP17_2026-11-17.md`.
Source intent is NOT demonstrated: review record r81 found the source does not show that this general
definition was intended, and the generalized-eigenspace alternative does not imply finite Riesz rank
(counterexample `C ⊕ L²(0,1)`, `T = 0 ⊕ V`). This contract proposition therefore states the
consequences of the chosen convention; it does not claim that the source adopts it. Route (i) is
tautological under the convention (its hypothesis is finite Riesz rank). Routes (ii) and (iii) are
genuine theorems about operators.

Sign convention (correspondence point). The resolvent here is `R z = (z - T)⁻¹`, i.e. `(z - T) R z = 1`.
With the integrator's stated `(T - z) R z = 1` the same formula `(2πi)⁻¹ ∮ R` is minus the Riesz
projection and is not idempotent; the idempotent statement fixes the convention used here.

No `sorry`, no new axioms. Author: haiku_inventory (EXT-025 GP-17 packaging, 2026-11-17). -/

noncomputable section
set_option autoImplicit false

open Set Metric MeasureTheory Complex Real Function
open QuantumNLS.Ext025HGP17Resolvent QuantumNLS.Ext025HGP17Routes

namespace QuantumNLS.Ext025HGP17Contract

/-- The repaired GP-17 contract, packaged. The statement is stated for an arbitrary complex Banach
space `E` and the owner-choice convention recorded in the module docstring. -/
theorem contract_GP17_full {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] :
    -- (1) scalar argument principle with multiplicities
    (∀ {c : ℂ} {R R' : ℝ}, 0 < R → R < R' → ∀ {f : ℂ → ℂ},
      DifferentiableOn ℂ f (ball c R') → (∀ z ∈ sphere c R, f z ≠ 0) →
      ∃ Z : Finset ℂ, (∀ a ∈ Z, a ∈ ball c R) ∧ (∀ z ∈ ball c R, (f z = 0 ↔ z ∈ Z)) ∧
        circleIntegral (fun z => deriv f z / f z) c R =
          (2 * π * Complex.I) * ∑ a ∈ Z, (analyticOrderNatAt f a : ℂ)) ∧
    -- (2) scalar Rouché (strict form on the circle)
    (∀ {c : ℂ} {R R' : ℝ}, 0 < R → R < R' → ∀ {f g : ℂ → ℂ},
      DifferentiableOn ℂ f (ball c R') → DifferentiableOn ℂ g (ball c R') →
      (∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) →
      ∀ {Zf Zg : Finset ℂ}, (∀ a ∈ Zf, a ∈ ball c R) → (∀ z ∈ ball c R, (f z = 0 ↔ z ∈ Zf)) →
        (∀ a ∈ Zg, a ∈ ball c R) → (∀ z ∈ ball c R, (g z = 0 ↔ z ∈ Zg)) →
        ∑ a ∈ Zf, analyticOrderNatAt f a = ∑ b ∈ Zg, analyticOrderNatAt g b) ∧
    -- (3) operator part, closed operators given through the resolvent (G1)
    (∀ {T : E →ₗ.[ℂ] E} {ρ : Set ℂ} {R : ℂ → E →L[ℂ] E}, ClosedResolvent T ρ R →
      ∀ {c : ℂ} {r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → closedBall c r₂ \ ball c r₁ ⊆ ρ →
        contourProj R c r₁ = contourProj R c r₂ ∧
        contourProj R c r₁ * contourProj R c r₁ = contourProj R c r₁ ∧
        (∀ v, contourProj R c r₁ v ∈ T.domain) ∧
        (∀ v (hv : v ∈ T.domain) (hPv : contourProj R c r₁ v ∈ T.domain),
          T.toFun ⟨contourProj R c r₁ v, hPv⟩ = contourProj R c r₁ (T.toFun ⟨v, hv⟩))) ∧
    -- (4) operator part, bounded case (corollary)
    (∀ {ρ : Set ℂ} {R : ℂ → E →L[ℂ] E} (T : E →L[ℂ] E), IsOpen ρ →
      DifferentiableOn ℂ R ρ → (∀ z ∈ ρ, ∀ v, T (R z v) = z • R z v - v) →
      (∀ z ∈ ρ, ∀ x, R z (T x) = z • R z x - x) →
      ∀ {c : ℂ} {r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → closedBall c r₂ \ ball c r₁ ⊆ ρ →
        contourProj R c r₁ * contourProj R c r₁ = contourProj R c r₁ ∧
        ∀ v, T (contourProj R c r₁ v) = contourProj R c r₁ (T v)) ∧
    -- (5i) route (i): finite total algebraic multiplicity (= finite Riesz rank under the convention)
    (∀ (P : E →L[ℂ] E), HasFiniteAlgMult P →
      FiniteDimensional ℂ (LinearMap.range P.toLinearMap)) ∧
    -- (5ii) route (ii): finite rank at a base parameter propagates by continuity
    (∀ {X : Type} [TopologicalSpace X] [PreconnectedSpace X] (P : X → E →L[ℂ] E),
      Continuous P → (∀ (x : X) (v : E), P x (P x v) = P x v) →
      ∀ (x₀ : X) [FiniteDimensional ℂ (LinearMap.range (P x₀).toLinearMap)] (x : X),
        HasFiniteAlgMult (P x) ∧ algMult (P x) = algMult (P x₀)) ∧
    -- (5iii) route (iii): a compact resolvent at one point gives a finite-rank idempotent projection
    (∀ {T : E →ₗ.[ℂ] E} {ρ : Set ℂ} {R : ℂ → E →L[ℂ] E}, ClosedResolvent T ρ R →
      ∀ {c : ℂ} {r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → closedBall c r₂ \ ball c r₁ ⊆ ρ →
        ∀ {z₀ : ℂ}, z₀ ∈ ρ → IsCompactOperator ⇑(R z₀) →
          contourProj R c r₁ * contourProj R c r₁ = contourProj R c r₁ ∧
          FiniteDimensional ℂ (LinearMap.range (contourProj R c r₁).toLinearMap)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c R R' hR hRR f hd hs
    exact QuantumNLS.Ext025HGP17Argument.argument_principle hR hRR hd hs
  · intro c R R' hR hRR f g hf hg hlt Zf Zg hZf hZf' hZg hZg'
    exact QuantumNLS.Ext025HGP17Rouche.rouche hR hRR hf hg hlt hZf hZf' hZg hZg'
  · intro T ρ R hR c r₁ r₂ h₁ h₁₂ hann
    exact contour_projection_G1 hR h₁ h₁₂ hann
  · intro ρ R T hρ hd hl hr c r₁ r₂ h₁ h₁₂ hann
    exact contour_projection_bounded T hρ hd hl hr h₁ h₁₂ hann
  · intro P h
    exact route_i P h
  · intro X _ _ P hc hid x₀ _ x
    exact route_ii P hc hid x₀ x
  · intro T ρ R hR c r₁ r₂ h₁ h₁₂ hann z₀ hz₀ hc₀
    exact QuantumNLS.Ext025HGP17Compact.route_iii_contour hR h₁ h₁₂ hann hz₀ hc₀

end QuantumNLS.Ext025HGP17Contract

#print axioms QuantumNLS.Ext025HGP17Contract.contract_GP17_full
