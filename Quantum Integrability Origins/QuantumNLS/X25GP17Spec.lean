import QuantumNLS.Ext025HGP17Contract
/-! integrator-authored trusted spec for EXT-025 GP-17 (owner Riesz-rank convention): headline statement(s) copied verbatim from Ext025HGP17Contract (QuantumNLS.Ext025HGP17Contract). -/
noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory Complex Real Function
open QuantumNLS.Ext025HGP17Resolvent QuantumNLS.Ext025HGP17Routes
namespace QuantumNLS.X25GP17Spec
open QuantumNLS.Ext025HGP17Contract


set_option maxHeartbeats 8000000 in
theorem contract_GP17_full_spec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] :
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
  first
  | exact QuantumNLS.Ext025HGP17Contract.contract_GP17_full
  | (apply QuantumNLS.Ext025HGP17Contract.contract_GP17_full <;> assumption)

end QuantumNLS.X25GP17Spec

namespace QuantumNLS.X25GP17Pins
open Complex Real
open QuantumNLS.Ext025HGP17Resolvent QuantumNLS.Ext025HGP17Routes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
theorem pin_contourProj (R : ℂ → E →L[ℂ] E) (c : ℂ) (r : ℝ) :
    QuantumNLS.Ext025HGP17Resolvent.contourProj R c r = (2 * π * Complex.I)⁻¹ • circleIntegral R c r := rfl
theorem pin_algMult (P : E →L[ℂ] E) :
    QuantumNLS.Ext025HGP17Routes.algMult P = Module.finrank ℂ (LinearMap.range P.toLinearMap) := rfl
theorem pin_HasFiniteAlgMult (P : E →L[ℂ] E) :
    QuantumNLS.Ext025HGP17Routes.HasFiniteAlgMult P ↔ FiniteDimensional ℂ (LinearMap.range P.toLinearMap) := Iff.rfl
theorem pin_ClosedResolvent (T : E →ₗ.[ℂ] E) (ρ : Set ℂ) (R : ℂ → E →L[ℂ] E) :
    QuantumNLS.Ext025HGP17Resolvent.ClosedResolvent T ρ R ↔
      IsOpen ρ ∧ DifferentiableOn ℂ R ρ ∧ IsClosed (T.graph : Set (E × E)) ∧
      ∃ hdom : (∀ z ∈ ρ, ∀ v : E, R z v ∈ T.domain),
        (∀ (z : ℂ) (hz : z ∈ ρ) (v : E), T.toFun ⟨R z v, hdom z hz v⟩ = z • R z v - v) ∧
        (∀ z ∈ ρ, ∀ (x : E) (hx : x ∈ T.domain), R z (T.toFun ⟨x, hx⟩) = z • R z x - x) :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩, fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩⟩
end QuantumNLS.X25GP17Pins
#print axioms QuantumNLS.X25GP17Pins.pin_ClosedResolvent
#print axioms QuantumNLS.X25GP17Spec.contract_GP17_full_spec
