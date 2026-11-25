import QuantumNLS.ContactFormTheorem

/-! integrator-authored trusted spec for R-98129FE7 `contact:thm:form` (A01.tex:37-46), all printed
clauses with pairings written out: for c ≥ 0 the form (DEF-005, `ContactForm.q`) on H¹_sym is densely
defined, closed, Hermitian and nonnegative; its associated self-adjoint nonnegative operator is unique;
(H+I)⁻¹ is compact; and the exact domain is the distributional one tested against ALL smooth periodic
φ: Σ_j ∫ conj(∂_jφ) ∂_jψ + 2c Σ_{i<j} ∫ conj(φ|_{x_i=x_j}) T_ijψ dy_ij = ∫ conj(φ) f, with Hψ = f. -/

open MeasureTheory ComplexConjugate
open scoped InnerProductSpace
open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.PhysicalTensor
open QuantumNLS.CollisionTrace QuantumNLS.ProductWeakDerivatives QuantumNLS.CollisionIdentification
open QuantumNLS.ContactForm QuantumNLS.ContactOperator

namespace QuantumNLS.R981Spec

def Spec : Prop :=
  ∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (c : ℝ) (hc : 0 ≤ c),
    DenseRange (valSym : (PhysH1.sym : Submodule ℂ (PhysH1 L N)) →L[ℂ] SymL2 L N) ∧
    (∀ u : ℕ → PhysH1 L N, (∀ n, u n ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))) →
      (∀ ε > 0, ∃ n₀ : ℕ, ∀ m n, n₀ ≤ m → n₀ ≤ n → formNormSq c (u m - u n) < ε) →
      ∃ x : PhysH1 L N, x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) ∧
        Filter.Tendsto (fun n => formNormSq c (u n - x)) Filter.atTop (nhds 0)) ∧
    ((∀ φ ψ : PhysH1 L N, conj (q c φ ψ) = q c ψ φ) ∧ ∀ ψ : PhysH1 L N, 0 ≤ (q c ψ ψ).re) ∧
    (∃! T : SymL2 L N →ₗ.[ℂ] SymL2 L N, IsSelfAdjoint T ∧
      (∀ ψ f : SymL2 L N, (∃ h : ψ ∈ T.domain, T ⟨ψ, h⟩ = f) ↔
        ∃ x : VSym L N, (valSym x : SymL2 L N) = ψ ∧
          ∀ φ : VSym L N, q c φ.1 x.1 = ⟪(valSym φ : SymL2 L N), f⟫_ℂ) ∧
      ∀ ψ : T.domain, 0 ≤ (⟪(ψ : SymL2 L N), T ψ⟫_ℂ).re) ∧
    (IsCompactOperator (Rop c hc : SymL2 L N →L[ℂ] SymL2 L N) ∧
      (∀ g : SymL2 L N, ∃ h : Rop c hc g ∈ (Hop (L := L) (N := N) c hc).domain,
        Hop c hc ⟨Rop c hc g, h⟩ + Rop c hc g = g) ∧
      ∀ ψ : (Hop (L := L) (N := N) c hc).domain,
        Rop c hc (Hop c hc ψ + (ψ : SymL2 L N)) = ψ) ∧
    (∀ ψ f : SymL2 L N,
      ((∃ h : ψ ∈ (Hop (L := L) (N := N) c hc).domain, Hop c hc ⟨ψ, h⟩ = f) ↔
        ∃ x : VSym L N, (valSym x : SymL2 L N) = ψ ∧
          ∀ (φ : (Fin N → ℝ) → ℂ), IsTorusTest L φ →
            (∑ j : Fin N, ∫ y, conj (liftK (L := L) (pderiv j φ) y) *
                (gradientCLM j x.1 : _ → ℂ) y ∂(torusPiMeasure L N)) +
            ((2 * c : ℝ) : ℂ) * ∑ p : Pair N,
              ∫ y, conj (liftK (L := L) φ (diagPoint p.1.1 p.1.2 y.1 y.2)) *
                (productTrace p.1.1 p.1.2 (ne_of_lt p.2) x.1 : _ → ℂ) y
                ∂((volume : Measure (AddCircle L)).prod
                    (Measure.pi fun _ : Rest N p.1.1 p.1.2 => (volume : Measure (AddCircle L)))) =
              ∫ y, conj (liftK (L := L) φ y) * ((f : L2TN L N) : _ → ℂ) y ∂(torusPiMeasure L N)))

theorem spec : Spec := by
  intro L _ N c hc
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := QuantumNLS.ContactFormTheorem.contact_thm_form (L := L) (N := N) hc
  refine ⟨h1, h2, h3, h4, h5, fun ψ f => ?_⟩
  refine (h6 ψ f).1.trans ?_
  refine exists_congr fun x => and_congr Iff.rfl ?_
  exact ⟨fun h φ hφ => h φ hφ, fun h φ hφ => h φ hφ⟩

end QuantumNLS.R981Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R981Spec.spec
  IO.println s!"R981Spec.spec axioms: {ax}"
