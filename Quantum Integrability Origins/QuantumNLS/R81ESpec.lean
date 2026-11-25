import QuantumNLS.ContactFormFamily

/-! integrator-authored trusted spec for R-81E86877 `basis:lem:forms` (periodic_basis.tex:87-91):
the forms h_c = Σ_j‖∂_jψ‖² + 2c Σ_{j<k} b_jk[ψ], b_jk[ψ] = ∫|T_jkψ|² dy_jk over the remaining N−1
coordinates, define for c ≥ 0 a nonnegative self-adjoint family H(c) (the operator associated with the
closed form), increasing in c, with compact free resolvent; and c ↦ (H(c)+1)⁻¹ is globally Lipschitz in
operator norm with a constant depending only on N and L (chosen before c, b). -/

open MeasureTheory
open scoped InnerProductSpace
open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.PhysicalTensor
open QuantumNLS.CollisionTrace QuantumNLS.ProductWeakDerivatives QuantumNLS.CollisionIdentification
open QuantumNLS.ContactForm QuantumNLS.ContactOperator QuantumNLS.ContactFormTheorem

namespace QuantumNLS.R81ESpec

def Spec : Prop :=
  ∀ (L : ℝ) [Fact (0 < L)] (N : ℕ),
    -- the form, with b_jk the physical collision integral
    (∀ (c : ℝ) (ψ : PhysH1 L N), q c ψ ψ =
        ((∑ j : Fin N, ‖gradientCLM j ψ‖ ^ 2 + 2 * c * ∑ p : Pair N,
          ∫ y, ‖(productTrace (L := L) p.1.1 p.1.2 (ne_of_lt p.2) ψ :
            (AddCircle L × (Rest N p.1.1 p.1.2 → AddCircle L)) → ℂ) y‖ ^ 2
            ∂((volume : Measure (AddCircle L)).prod
              (Measure.pi fun _ : Rest N p.1.1 p.1.2 => (volume : Measure (AddCircle L)))) : ℝ) : ℂ)) ∧
    -- nonnegative self-adjoint family defined through the closed forms
    (∀ (c : ℝ) (hc : 0 ≤ c),
      (∀ ψ : PhysH1 L N, 0 ≤ (q c ψ ψ).re) ∧
      IsSelfAdjoint (Hop (L := L) (N := N) c hc) ∧ IsAssociated c (Hop (L := L) (N := N) c hc) ∧
      (∀ ψ : (Hop (L := L) (N := N) c hc).domain, 0 ≤ (⟪(ψ : SymL2 L N), Hop c hc ψ⟫_ℂ).re) ∧
      (∀ g : SymL2 L N, ∃ h : Rop c hc g ∈ (Hop (L := L) (N := N) c hc).domain,
        Hop c hc ⟨Rop c hc g, h⟩ + Rop c hc g = g)) ∧
    -- increasing in c (form order; resolvents decrease)
    (∀ (c c' : ℝ) (hc : 0 ≤ c) (hc' : 0 ≤ c'), c ≤ c' →
      (∀ ψ : PhysH1 L N, (q c ψ ψ).re ≤ (q c' ψ ψ).re) ∧
      ∀ f : SymL2 L N, (⟪Rop c' hc' f, f⟫_ℂ).re ≤ (⟪Rop c hc f, f⟫_ℂ).re) ∧
    -- compact free resolvent
    IsCompactOperator (Rop 0 le_rfl : SymL2 L N →L[ℂ] SymL2 L N) ∧
    -- globally Lipschitz with a constant depending only on N, L
    (∃ K : ℝ, 0 ≤ K ∧ ∀ (c b : ℝ) (hc : 0 ≤ c) (hb : 0 ≤ b),
      ‖(Rop c hc : SymL2 L N →L[ℂ] SymL2 L N) - Rop b hb‖ ≤ K * |c - b|)

theorem spec : Spec := by
  intro L _ N
  obtain ⟨ha, -, hfam, hmono, ⟨hcomp, -⟩, hK, hlip⟩ :=
    QuantumNLS.ContactFormFamily.form_family (L := L) (N := N)
  refine ⟨ha, fun c hc => ?_, hmono, hcomp, ⟨_, hK, hlip⟩⟩
  obtain ⟨-, h1, h2, h3, h4, h5, -⟩ := hfam c hc
  exact ⟨h1, h2, h3, h4, h5⟩

end QuantumNLS.R81ESpec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R81ESpec.spec
  IO.println s!"R81ESpec.spec axioms: {ax}"
