import QuantumNLS.StrongSymplectic

/-! integrator-authored trusted spec for DEF-016 "Strong symplectic diffeomorphism"
(DEFINITIONS_LEDGER.md:335; definitions.tex:97-99). For complex Hilbert spaces H, E (in particular the
physical L²(𝕋_L) and the sequence space ℓ²(ℤ)), a map Φ : H → E is strongly symplectic iff it is a real
differentiable diffeomorphism (bijective with differentiable inverse), its derivative at every u is a bounded
real-linear isomorphism, and Ω(DΦ(u)h, DΦ(u)k) = Ω(h,k) for all tangent vectors, with Ω(h,k) = 2 Im⟨h,k⟩
(DEF-015, written here literally; on ℓ²(ℤ) the same formula — the sequence-side interpretation accepted by
Terra r91). The spec states the author's predicate is exactly this, and records non-vacuity (identity),
closure under composition and inverses. -/

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.DEF016Spec

variable {H E F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Literal DEF-016 with Ω(h,k) = 2 Im⟨h,k⟩. -/
def sSS (Φ : H → E) : Prop :=
  (∃ Ψ : E → H, (∀ x, Ψ (Φ x) = x) ∧ (∀ y, Φ (Ψ y) = y) ∧ Differentiable ℝ Ψ) ∧
  Differentiable ℝ Φ ∧
  (∀ u, ∃ e : H ≃L[ℝ] E, (e : H → E) = fderiv ℝ Φ u) ∧
  (∀ u h k, 2 * (inner ℂ (fderiv ℝ Φ u h) (fderiv ℝ Φ u k)).im = 2 * (inner ℂ h k).im)

theorem sSS_iff (Φ : H → E) : sSS Φ ↔ StrongSymplectic.IsStronglySymplectic Φ :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

theorem spec :
    (∀ Φ : H → E, sSS Φ ↔ StrongSymplectic.IsStronglySymplectic Φ) ∧
    sSS (id : H → H) ∧
    (∀ (Φ : H → E) (Ψ : E → F), sSS Φ → sSS Ψ → sSS (Ψ ∘ Φ)) ∧
    (∀ Φ : H → E, sSS Φ → ∃ Ψ : E → H, sSS Ψ ∧ (∀ x, Ψ (Φ x) = x) ∧ (∀ y, Φ (Ψ y) = y)) := by
  refine ⟨sSS_iff, (sSS_iff _).2 StrongSymplectic.isStronglySymplectic_id,
    fun Φ Ψ h1 h2 => (sSS_iff _).2 (((sSS_iff _).1 h1).comp ((sSS_iff _).1 h2)), fun Φ h => ?_⟩
  obtain ⟨Ψ, hΨ, hl, hr⟩ := ((sSS_iff _).1 h).symm
  exact ⟨Ψ, (sSS_iff _).2 hΨ, hl, hr⟩

end QuantumNLS.DEF016Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.DEF016Spec.spec
  IO.println s!"DEF016Spec.spec axioms: {ax}"
