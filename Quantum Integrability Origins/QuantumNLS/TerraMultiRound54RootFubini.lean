import QuantumNLS.TerraMultiRound54MeasureSplit

/-! Fubini at the root coordinate for an integrable orthant integrand. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound54RootFubini

variable {ι : Type} [Fintype ι]

def positiveMeasure : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

instance : SigmaFinite positiveMeasure := by
  unfold positiveMeasure
  infer_instance

def optionAssembly : ((ι → ℝ) × ℝ) ≃ᵐ (Option ι → ℝ) :=
  (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)).symm

/-- The root and the remaining coordinates carry exactly the orthant
product measure. -/
theorem optionAssembly_preserving :
    MeasurePreserving (optionAssembly (ι := ι))
      ((Measure.pi (fun _ : ι => positiveMeasure)).prod positiveMeasure)
      (Measure.pi (fun _ : Option ι => positiveMeasure)) := by
  refine ⟨(optionAssembly (ι := ι)).measurable, ?_⟩
  exact Measure.pi_map_piOptionEquivProd (fun _ : Option ι => positiveMeasure)

/-- For an integrable orthant integrand, separate the root variable and
integrate it last. The integrability hypothesis concerns only this general
support lemma and is not supplied as a conclusion of REG-007. -/
theorem option_root_fubini (F : (Option ι → ℝ) → ℂ)
    (hF : Integrable F (Measure.pi (fun _ : Option ι => positiveMeasure))) :
    (∫ t, F t ∂(Measure.pi (fun _ : Option ι => positiveMeasure))) =
      ∫ root : ℝ, ∫ sub : ι → ℝ,
        F (optionAssembly (sub, root)) ∂(Measure.pi (fun _ : ι => positiveMeasure))
        ∂positiveMeasure := by
  have hp := optionAssembly_preserving (ι := ι)
  have hi : Integrable (F ∘ optionAssembly) ((Measure.pi (fun _ : ι => positiveMeasure)).prod positiveMeasure) :=
    hp.integrable_comp_of_integrable hF
  rw [← hp.integral_comp' F]
  change Integrable (fun p => F (optionAssembly p)) _ at hi
  exact integral_prod_symm (fun p => F (optionAssembly p)) hi

/-- The parent-tree orthant integral can be split into the root time and
all child times whenever its actual integrand is integrable. -/
theorem parent_root_fubini (l r : BinaryTree Unit)
    (F : (Fin (2 * (BinaryTree.node () l r).numNodes + 1) → ℝ) → ℂ)
    (hF : Integrable F (Measure.pi (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) =>
      positiveMeasure))) :
    (∫ t, F t ∂(Measure.pi (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) =>
      positiveMeasure))) =
      ∫ root : ℝ, ∫ sub : (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) → ℝ,
        F ((MeasurableEquiv.piCongrLeft
          (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) => ℝ)
          (QuantumNLS.TerraMultiRound54IndexSplit.splitEquiv l r)) (optionAssembly (sub, root)))
          ∂(Measure.pi (fun _ => positiveMeasure)) ∂positiveMeasure := by
  let e := MeasurableEquiv.piCongrLeft
    (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) => ℝ)
    (QuantumNLS.TerraMultiRound54IndexSplit.splitEquiv l r)
  have hp : MeasurePreserving e
      (Measure.pi (fun _ : Option (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) => positiveMeasure))
      (Measure.pi (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) => positiveMeasure)) :=
    QuantumNLS.TerraMultiRound54MeasureSplit.orthant_split_measure l r
  have hi : Integrable (F ∘ e)
      (Measure.pi (fun _ : Option (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) => positiveMeasure)) :=
    hp.integrable_comp_of_integrable hF
  calc
    _ = ∫ t, F (e t) ∂(Measure.pi (fun _ : Option (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) => positiveMeasure)) :=
      (hp.integral_comp' F).symm
    _ = _ := option_root_fubini (F ∘ e) hi

#print axioms parent_root_fubini
#print axioms optionAssembly_preserving
#print axioms option_root_fubini
end QuantumNLS.TerraMultiRound54RootFubini
