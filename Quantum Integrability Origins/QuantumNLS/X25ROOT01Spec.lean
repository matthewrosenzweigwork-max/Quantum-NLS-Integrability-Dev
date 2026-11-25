import QuantumNLS.Ext025AApplications
/-! integrator-authored trusted spec for EXT-025 ROOT-01 (review record r4 ACCEPT): headline statement(s) copied verbatim from Ext025AApplications (QuantumNLS.Ext025A). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped InnerProductSpace ComplexConjugate LinearPMap ENNReal ComplexOrder
namespace QuantumNLS.X25ROOT01Spec
open QuantumNLS.Ext025A
open ContactOperator ContactFormTheorem
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}
open TraceClass TraceIdeal TraceCompact
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
open QuantumNLS.Fourier
variable (L : ℝ) [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem FIN_EXT025_ROOT_01_spec :
    ∃ U : Lp ℂ 2 (volume : Measure (AddCircle L)) ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2,
      (∀ u n, U u n = coeff L (u : AddCircle L → ℂ) n) ∧
      (∀ u : Lp ℂ 2 (volume : Measure (AddCircle L)),
        hsNormSq L 0 (fun n => U u n) = ‖u‖ ^ 2) ∧
      (∀ u : Lp ℂ 2 (volume : Measure (AddCircle L)),
        HasSum (fun n : ℤ => coeff L (u : AddCircle L → ℂ) n • modeLp L n) u) ∧
      ∀ n : ℤ, ∀ x : ℝ, mode L n (x : AddCircle L) =
        (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * n * x / L) := by
  exact QuantumNLS.Ext025A.«FIN-EXT025-ROOT-01» L

end QuantumNLS.X25ROOT01Spec
#print axioms QuantumNLS.X25ROOT01Spec.FIN_EXT025_ROOT_01_spec
