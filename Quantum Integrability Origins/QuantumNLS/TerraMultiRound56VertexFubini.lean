import QuantumNLS.TerraMultiRound56VertexIntegrable
import QuantumNLS.TerraMultiRound55ParentTime

/-! Fubini for the unpaired kernel at each spatial point. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.TerraMultiRound56VertexFubini
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound54RootFubini
open QuantumNLS.TerraMultiRound54MeasureSplit
open QuantumNLS.TerraMultiRound55ChildFubini
open QuantumNLS.TerraMultiRound55PhysicalChildren
open QuantumNLS.TerraMultiRound56KernelSplit
open QuantumNLS.TerraMultiRound56VertexIntegrable
open QuantumNLS.RiccatiSobolevBanach

variable {L : ℝ} [Fact (0 < L)]

/-- Root Fubini for the unpaired vertex kernel, at every spatial point. -/
theorem vertex_root_fubini {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (l r : BinaryTree Unit) (Y : ℝ) (x : AddCircle L) :
    (∫ time, vertexKernel hk u (.node () l r) Y time x ∂
      (Measure.pi (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) => positiveMeasure))) =
    ∫ root : ℝ, ∫ sub : (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) → ℝ,
      vertexKernel hk u (.node () l r) Y (parentTime l r sub root) x
      ∂(Measure.pi (fun _ => positiveMeasure)) ∂positiveMeasure := by
  exact parent_root_fubini l r (fun time => vertexKernel hk u (.node () l r) Y time x)
    (vertexKernel_integrable hk u (.node () l r) Y x)

/-- For each spatial point, almost every root slice has integrable children. -/
theorem vertex_children_integrable {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (l r : BinaryTree Unit) (Y : ℝ) (x : AddCircle L) :
    ∀ᵐ root ∂positiveMeasure,
      Integrable (fun sub => vertexKernel hk u (.node () l r) Y (parentTime l r sub root) x)
      (Measure.pi (fun _ : Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1) => positiveMeasure)) := by
  let e := MeasurableEquiv.piCongrLeft
    (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) => ℝ)
    (QuantumNLS.TerraMultiRound54IndexSplit.splitEquiv l r)
  let F := fun time => vertexKernel hk u (.node () l r) Y time x
  have hi : Integrable (F ∘ e)
      (Measure.pi (fun _ : Option (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) => positiveMeasure)) :=
    (orthant_split_measure l r).integrable_comp_of_integrable (vertexKernel_integrable hk u (.node () l r) Y x)
  have hj := (optionAssembly_preserving (ι := Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1))).integrable_comp_of_integrable hi
  exact hj.prod_left_ae

/-- Fubini separates the two child orthants for almost every root time. -/
theorem vertex_children_fubini {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (l r : BinaryTree Unit) (Y : ℝ) (x : AddCircle L) :
    ∀ᵐ root ∂positiveMeasure,
      (∫ sub, vertexKernel hk u (.node () l r) Y (parentTime l r sub root) x ∂
        (Measure.pi (fun _ : Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1) => positiveMeasure))) =
      ∫ left : Fin (2 * l.numNodes + 1) → ℝ,
        ∫ right : Fin (2 * r.numNodes + 1) → ℝ,
          vertexKernel hk u (.node () l r) Y (parentTime l r (childAssembly (left, right)) root) x
          ∂(Measure.pi (fun _ => positiveMeasure)) ∂(Measure.pi (fun _ => positiveMeasure)) := by
  filter_upwards [vertex_children_integrable hk u l r Y x] with root hroot
  exact child_fubini (fun sub => vertexKernel hk u (.node () l r) Y (parentTime l r sub root) x) hroot

#print axioms vertex_root_fubini
#print axioms vertex_children_integrable
#print axioms vertex_children_fubini
end QuantumNLS.TerraMultiRound56VertexFubini
