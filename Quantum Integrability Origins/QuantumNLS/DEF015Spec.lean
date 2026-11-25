import QuantumNLS.SymplecticBracket

/-! integrator-authored trusted spec for DEF-015 (definitions.tex:93): physical symplectic form and
Poisson bracket on the real Hilbert space underlying a complex Hilbert space (inner product linear in
the second slot), instantiated on the physical space `L2T L` (DEF-001). -/

open InnerProductSpace ComplexConjugate
open QuantumNLS.SymplecticBracket QuantumNLS.PhysicalTensor

namespace QuantumNLS.DEF015Spec

attribute [local instance] InnerProductSpace.complexToReal

/-- Clauses: Ω = 2 Im⟨·,·⟩; ∇F characterized (existence and uniqueness) by dF[h] = 2 Re⟨∇F,h⟩;
X_F = −i∇F; {F,G} = dF[X_G]; complex-bilinear extension; normalization {z, z̄} = −i. -/
def Spec : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    (∀ h k : H, omega h k = 2 * (inner ℂ h k).im) ∧
    (∀ (F : H → ℝ) (u h : H), fderiv ℝ F u h = 2 * (inner ℂ (SymplecticBracket.gradient F u) h).re) ∧
    (∀ (F : H → ℝ) (u g : H), (∀ h, fderiv ℝ F u h = 2 * (inner ℂ g h).re) → g = SymplecticBracket.gradient F u) ∧
    (∀ (F : H → ℝ) (u : H), hamField F u = (-Complex.I) • SymplecticBracket.gradient F u) ∧
    (∀ (F G : H → ℝ) (u : H), pbR F G u = fderiv ℝ F u (hamField G u)) ∧
    (∀ (F G : H → ℂ) (u : H), pbC F G u =
        ((pbR (fun v => (F v).re) (fun v => (G v).re) u
          - pbR (fun v => (F v).im) (fun v => (G v).im) u : ℝ) : ℂ)
        + Complex.I * ((pbR (fun v => (F v).im) (fun v => (G v).re) u
          + pbR (fun v => (F v).re) (fun v => (G v).im) u : ℝ) : ℂ)) ∧
    (∀ e : H, ‖e‖ = 1 → ∀ u : H,
        pbC (fun v => inner ℂ e v) (fun v => conj (inner ℂ e v)) u = -Complex.I)

theorem spec : Spec := by
  intro H _ _ _
  refine ⟨fun h k => rfl, ?_, ?_, fun F u => rfl, fun F G u => rfl, ?_, ?_⟩
  · intro F u h
    rw [fderiv_eq_two_inner_gradient, re_inner_coord]
  · intro F u g hg
    have hd : ∀ h, (inner ℂ (g - SymplecticBracket.gradient F u) h).re = 0 := by
      intro h
      have h1 := hg h
      rw [fderiv_eq_two_inner_gradient, ← re_inner_coord] at h1
      rw [inner_sub_left, Complex.sub_re]
      linarith
    have h0 := hd (g - SymplecticBracket.gradient F u)
    exact sub_eq_zero.mp (re_inner_self_nonpos (𝕜 := ℂ).mp (le_of_eq h0))
  · intro F G u
    apply Complex.ext <;> simp [pbC]
  · intro e he u
    exact pbC_coord_conj he u

/-- Physical instance (DEF-001 carrier). -/
theorem spec_phys (L : ℝ) [Fact (0 < L)] {e : L2T L} (he : ‖e‖ = 1) (u : L2T L) :
    pbC (fun v : L2T L => inner ℂ e v) (fun v => conj (inner ℂ e v)) u = -Complex.I :=
  pbC_coord_conj_phys L he u

end QuantumNLS.DEF015Spec

open Lean in
#eval show CoreM Unit from do
  for n in [``QuantumNLS.DEF015Spec.spec, ``QuantumNLS.DEF015Spec.spec_phys] do
    let ax ← Lean.collectAxioms n
    IO.println s!"{n} axioms: {ax}"
