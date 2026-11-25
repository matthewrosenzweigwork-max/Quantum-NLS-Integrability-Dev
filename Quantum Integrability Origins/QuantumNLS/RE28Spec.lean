import QuantumNLS.ChartFrequencies

/-! integrator-authored trusted spec for R-E28AD0D3 `lem:frequency` (core/DYNAMICS_LEMMAS.tex:329).
Φ₁, Φ₂ : H → ℓ²(ℤ) global C¹ strong canonical diffeomorphisms (C¹ with C¹ inverse, derivative a
continuous real-linear isomorphism at every point, preserving Ω = 2 Im⟨·,·⟩ of DEF-015) with
|Φ₁(u)_n|² = |Φ₂(u)_n|² for all u, n. If a physical flow Ψ is coordinate rotation in chart 1 with
frequencies depending only on the actions, (Φ₁(Ψ_t u))_n = e^{−itω_n(|Φ₁u|²)} (Φ₁u)_n, then the same holds
in chart 2 with the same ω, and the active frequencies (those at coordinates with Φ₂(u)_n ≠ 0) are
uniquely determined. All predicates written out here. -/

open QuantumNLS.RephasingFlow

namespace QuantumNLS.RE28Spec

def C1Canonical {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Φ : H → E) : Prop :=
  ContDiff ℝ 1 Φ ∧ (∃ Ψ : E → H, (∀ z, Ψ (Φ z) = z) ∧ (∀ w, Φ (Ψ w) = w) ∧ ContDiff ℝ 1 Ψ) ∧
  (∀ z, ∃ e : H ≃L[ℝ] E, (e : H → E) = fderiv ℝ Φ z) ∧
  (∀ z h k, SymplecticBracket.omega (fderiv ℝ Φ z h) (fderiv ℝ Φ z k) = SymplecticBracket.omega h k)

def RotFlow {H : Type*} (Φ : H → E) (Ψ : ℝ → H → H) (ω : ℤ → (ℤ → ℝ) → ℝ) : Prop :=
  ∀ (t : ℝ) (u : H) (n : ℤ), Φ (Ψ t u) n =
    Complex.exp (-Complex.I * ((t * ω n (fun m => ‖Φ u m‖ ^ 2) : ℝ) : ℂ)) * Φ u n

def Spec : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Φ₁ Φ₂ : H → E),
    C1Canonical Φ₁ → C1Canonical Φ₂ → (∀ u n, ‖Φ₁ u n‖ ^ 2 = ‖Φ₂ u n‖ ^ 2) →
    ∀ (Ψ : ℝ → H → H) (ω : ℤ → (ℤ → ℝ) → ℝ), RotFlow Φ₁ Ψ ω →
      RotFlow Φ₂ Ψ ω ∧ ∀ ω', RotFlow Φ₂ Ψ ω' → ∀ (u : H) (n : ℤ), Φ₂ u n ≠ 0 →
        ω' n (fun m => ‖Φ₂ u m‖ ^ 2) = ω n (fun m => ‖Φ₂ u m‖ ^ 2)

theorem spec : Spec := by
  intro H _ _ Φ₁ Φ₂ h₁ h₂ hact Ψ ω hf
  obtain ⟨c1, i1, d1, s1⟩ := h₁
  obtain ⟨c2, i2, d2, s2⟩ := h₂
  exact QuantumNLS.ChartFrequencies.lem_frequency ⟨c1, i1, d1, s1⟩ ⟨c2, i2, d2, s2⟩ hact Ψ ω hf

end QuantumNLS.RE28Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.RE28Spec.spec
  IO.println s!"RE28Spec.spec axioms: {ax}"
