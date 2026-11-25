import QuantumNLS.TerraMultiRound55KernelFubini

/-! Product-measure splitting of the two child orthants. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.TerraMultiRound55ChildFubini
open QuantumNLS.TerraMultiRound54RootFubini

variable {ι κ : Type} [Fintype ι] [Fintype κ]

def childAssembly : ((ι → ℝ) × (κ → ℝ)) ≃ᵐ ((ι ⊕ κ) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => ℝ)).symm

theorem childAssembly_preserving :
    MeasurePreserving (childAssembly (ι := ι) (κ := κ))
      ((Measure.pi (fun _ : ι => positiveMeasure)).prod
       (Measure.pi (fun _ : κ => positiveMeasure)))
      (Measure.pi (fun _ : ι ⊕ κ => positiveMeasure)) := by
  exact measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ κ => positiveMeasure)

/-- Split an integrable child kernel into its left and right orthants.
The integrability hypothesis is for this reusable support lemma only. -/
theorem child_fubini (F : ((ι ⊕ κ) → ℝ) → ℂ)
    (hF : Integrable F (Measure.pi (fun _ : ι ⊕ κ => positiveMeasure))) :
    (∫ sub, F sub ∂(Measure.pi (fun _ : ι ⊕ κ => positiveMeasure))) =
      ∫ left : ι → ℝ, ∫ right : κ → ℝ,
        F (childAssembly (left, right)) ∂(Measure.pi (fun _ => positiveMeasure))
        ∂(Measure.pi (fun _ => positiveMeasure)) := by
  have hp := childAssembly_preserving (ι := ι) (κ := κ)
  have hi : Integrable (F ∘ childAssembly)
      ((Measure.pi (fun _ : ι => positiveMeasure)).prod
       (Measure.pi (fun _ : κ => positiveMeasure))) := hp.integrable_comp_of_integrable hF
  rw [← hp.integral_comp' F]
  exact integral_prod (fun p => F (childAssembly p)) hi

#print axioms childAssembly_preserving
#print axioms child_fubini
end QuantumNLS.TerraMultiRound55ChildFubini
