import QuantumNLS.TerraMultiRound54IndexSplit
import Mathlib.MeasureTheory.Integral.Pi

/-! Measure-preserving reindexing of the tree orthant. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound54MeasureSplit
open QuantumNLS.TerraMultiRound54IndexSplit

/-- The orthant measure is invariant under the proved root/child indexing
bijection. -/
theorem orthant_split_measure (l r : BinaryTree Unit) :
    MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) => ℝ)
        (splitEquiv l r))
      (Measure.pi (fun _ : Option (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) =>
        volume.restrict (Ioi (0 : ℝ))))
      (Measure.pi (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) =>
        volume.restrict (Ioi (0 : ℝ)))) := by
  exact measurePreserving_piCongrLeft (fun _ => volume.restrict (Ioi (0 : ℝ))) (splitEquiv l r)

/-- Reindex any Bochner integral on the parent orthant; this equality does
not assert Fubini or identify the tree integrand. -/
theorem orthant_integral_reindex (l r : BinaryTree Unit)
    (F : (Fin (2 * (BinaryTree.node () l r).numNodes + 1) → ℝ) → ℂ) :
    (∫ t, F t ∂(Measure.pi (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) =>
      volume.restrict (Ioi (0 : ℝ))))) =
    ∫ t : Option (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) → ℝ,
      F (fun i => t ((splitEquiv l r).symm i)) ∂
      (Measure.pi (fun _ => volume.restrict (Ioi (0 : ℝ)))) := by
  have h := (orthant_split_measure l r).integral_comp' F
  have he (t : Option (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) → ℝ) :
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) => ℝ)
        (splitEquiv l r)) t = fun i => t ((splitEquiv l r).symm i) := by
    funext i
    have hi := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) (splitEquiv l r) t ((splitEquiv l r).symm i)
    rw [(splitEquiv l r).apply_symm_apply] at hi
    exact hi
  simpa only [Function.comp_def, he] using h.symm

#print axioms orthant_split_measure
#print axioms orthant_integral_reindex
end QuantumNLS.TerraMultiRound54MeasureSplit
