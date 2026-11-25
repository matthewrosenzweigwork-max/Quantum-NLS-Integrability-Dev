import QuantumNLS.TerraMultiRound55ChildFubini

/-! Concrete child-slice integrability for recursive Fubini. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.TerraMultiRound55PhysicalChildren
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound54RootFubini
open QuantumNLS.TerraMultiRound54MeasureSplit
open QuantumNLS.TerraMultiRound48TreeFubini
open QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound55KernelFubini
open QuantumNLS.TerraMultiRound55ChildFubini
open QuantumNLS.RiccatiSobolevBanach

variable {L : ℝ} [Fact (0 < L)]

def parentTime (l r : BinaryTree Unit)
    (sub : (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) → ℝ)
    (root : ℝ) : Fin (2 * (BinaryTree.node () l r).numNodes + 1) → ℝ :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) => ℝ)
    (QuantumNLS.TerraMultiRound54IndexSplit.splitEquiv l r)) (optionAssembly (sub, root))

/-- For almost every spatial and root point the actual joint tree kernel
is integrable on the combined child orthant. -/
theorem physical_children_integrable {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (l r : BinaryTree Unit) (Y : ℝ) :
    ∀ᵐ x : AddCircle L, ∀ᵐ root ∂positiveMeasure,
      Integrable (fun sub => treeIntegrand hk
        (factorField (L := L) k u (.node () l r))
        (finiteFactorPaths (.node () l r)) Y (parentTime l r sub root, x))
      (Measure.pi (fun _ : Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1) =>
        positiveMeasure)) := by
  filter_upwards [physical_kernel_parent_root hk u l r Y] with x hx
  let e := MeasurableEquiv.piCongrLeft
    (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) => ℝ)
    (QuantumNLS.TerraMultiRound54IndexSplit.splitEquiv l r)
  let F := fun t => treeIntegrand hk (factorField (L := L) k u (.node () l r))
    (finiteFactorPaths (.node () l r)) Y (t, x)
  have hi : Integrable (F ∘ e)
      (Measure.pi (fun _ : Option (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) => positiveMeasure)) :=
    (orthant_split_measure l r).integrable_comp_of_integrable hx
  have hj := (optionAssembly_preserving (ι := Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1))).integrable_comp_of_integrable hi
  exact hj.prod_left_ae


/-- Both child integrations may be separated for the concrete physical
kernel, with the integrability premise proved above. -/
theorem physical_children_fubini {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (l r : BinaryTree Unit) (Y : ℝ) :
    ∀ᵐ x : AddCircle L, ∀ᵐ root ∂positiveMeasure,
      (∫ sub, treeIntegrand hk (factorField (L := L) k u (.node () l r))
        (finiteFactorPaths (.node () l r)) Y (parentTime l r sub root, x) ∂
        (Measure.pi (fun _ : Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1) =>
          positiveMeasure))) =
      ∫ left : Fin (2 * l.numNodes + 1) → ℝ,
        ∫ right : Fin (2 * r.numNodes + 1) → ℝ,
          treeIntegrand hk (factorField (L := L) k u (.node () l r))
            (finiteFactorPaths (.node () l r)) Y
            (parentTime l r (childAssembly (left, right)) root, x)
            ∂(Measure.pi (fun _ => positiveMeasure))
            ∂(Measure.pi (fun _ => positiveMeasure)) := by
  filter_upwards [physical_children_integrable hk u l r Y] with x hx
  filter_upwards [hx] with root hroot
  exact child_fubini (fun sub => treeIntegrand hk
    (factorField (L := L) k u (.node () l r))
    (finiteFactorPaths (.node () l r)) Y (parentTime l r sub root, x)) hroot

#print axioms physical_children_integrable
#print axioms physical_children_fubini
end QuantumNLS.TerraMultiRound55PhysicalChildren
