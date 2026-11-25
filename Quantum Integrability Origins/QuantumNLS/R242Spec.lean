import QuantumNLS.ContactProductExact
/-! integrator-authored trusted spec for R-242DB77D contact:prop:product (review record r27 PASS): headline statement(s) copied verbatim from ContactProductExact (QuantumNLS.ContactProductExact). -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
open MeasureTheory QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor
  QuantumNLS.ProductEnergyPreparation QuantumNLS.CollisionTrace
  QuantumNLS.CollisionIdentification QuantumNLS.ContactForm QuantumNLS.ChargeEnergy
  QuantumNLS.ContactProductIntegrals QuantumNLS.ProductWeakDerivatives
namespace QuantumNLS.R242Spec
open QuantumNLS.ContactProductExact
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem contact_prop_product_spec (u : L2T L) (hH : OneH1 u) (c : ℝ) (N : ℕ) :
    ∃ Ψ : PhysH1 L N,
      Ψ.val = prodState u N ∧
      Ψ ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) ∧
      ‖Ψ.val‖ ^ 2 = (‖u‖ ^ 2) ^ N ∧
      (∫ x, ‖Ψ.val x‖ ^ 2 ∂(torusPiMeasure L N)) = (‖u‖ ^ 2) ^ N ∧
      PiSquareFubini Ψ.val ∧
      (∀ j : Fin N,
        HasWeakPartial j Ψ.val (gradientCLM j Ψ) ∧
        ‖gradientCLM j Ψ‖ ^ 2 = (‖u‖ ^ 2) ^ (N - 1) * kinetic (u : AddCircle L → ℂ) ∧
        (∫ x, ‖gradientCLM j Ψ x‖ ^ 2 ∂(torusPiMeasure L N)) =
          (‖u‖ ^ 2) ^ (N - 1) * kinetic (u : AddCircle L → ℂ) ∧
        PiSquareFubini (gradientCLM j Ψ)) ∧
      (∀ (i j : Fin N) (hij : i ≠ j),
        ‖productTrace i j hij Ψ‖ ^ 2 =
          (‖u‖ ^ 2) ^ (N - 2) * quartic (u : AddCircle L → ℂ) ∧
        (∫ y, ‖productTrace i j hij Ψ y‖ ^ 2 ∂(dyij (L := L) i j)) =
          (‖u‖ ^ 2) ^ (N - 2) * quartic (u : AddCircle L → ℂ) ∧
        (∫ t, ∫ y, ‖productTrace i j hij Ψ (t,y)‖ ^ 2
          ∂(Measure.pi fun _ : Rest N i j => (volume : Measure (AddCircle L)))
          ∂(volume : Measure (AddCircle L))) =
          (‖u‖ ^ 2) ^ (N - 2) * quartic (u : AddCircle L → ℂ) ∧
        SquareFubini (volume : Measure (AddCircle L))
          (Measure.pi fun _ : Rest N i j => (volume : Measure (AddCircle L)))
          (productTrace i j hij Ψ)) ∧
      (q c Ψ Ψ).re =
        (∑ j, ‖gradientCLM j Ψ‖ ^ 2) +
          2 * c * ∑ p : Pair N, ∫ y,
            ‖productTrace p.1.1 p.1.2 (ne_of_lt p.2) Ψ y‖ ^ 2
              ∂(dyij (L := L) p.1.1 p.1.2) ∧
      q c Ψ Ψ = ((N * (‖u‖ ^ 2) ^ (N - 1) * kinetic (u : AddCircle L → ℂ) +
        c * N * ((N : ℝ) - 1) * (‖u‖ ^ 2) ^ (N - 2) *
          quartic (u : AddCircle L → ℂ) : ℝ) : ℂ) ∧
      (N = 1 → q c Ψ Ψ = ((kinetic (u : AddCircle L → ℂ) : ℝ) : ℂ)) := by
  exact QuantumNLS.ContactProductExact.contact_prop_product u hH c N

end QuantumNLS.R242Spec
#print axioms QuantumNLS.R242Spec.contact_prop_product_spec
