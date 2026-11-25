import QuantumNLS.TerraMultiRound55TreeFactors

/-! Pointwise physical factors and Fubini for the concrete joint kernel. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set ComplexConjugate
namespace QuantumNLS.TerraMultiRound55KernelFubini
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound54RootFubini
open QuantumNLS.TerraMultiRound48TreeFubini
open QuantumNLS.TerraMultiRound49SobolevBridge
open QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev

variable {L : ℝ} [Fact (0 < L)]

/-- Every indexed factor evaluates to the correct physical representative. -/
theorem vertexField_rep {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (t : BinaryTree Unit) (i : Fin (2 * t.numNodes + 1)) (x : ℝ) :
    contRep hk (vertexField (L := L) k u t i) (x : AddCircle L) =
      if internalAt t (indexedVertex t i) then
        starRingEnd ℂ (physRep L (k : ℝ) u x)
      else physRep L (k : ℝ) u x := by
  unfold vertexField
  split
  · exact physicalToHk_conj_rep hk u x
  · exact physicalToHk_rep hk u x

/-- Joint integrability supplies almost-everywhere orthant integrability
for the actual paired kernel, so root Fubini needs no extra assumption. -/
theorem physical_kernel_parent_root {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (l r : BinaryTree Unit) (Y : ℝ) :
    ∀ᵐ x : AddCircle L, Integrable
      (fun t => treeIntegrand hk (factorField (L := L) k u (.node () l r))
        (finiteFactorPaths (.node () l r)) Y (t, x))
      (Measure.pi (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) =>
        positiveMeasure)) := by
  exact (physical_kernel_integrable hk u (.node () l r) Y).prod_left_ae


/-- Root-time Fubini for the physical-factor parent kernel, for almost
every spatial point, with integrability discharged from the joint kernel. -/
theorem physical_kernel_root_fubini {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (l r : BinaryTree Unit) (Y : ℝ) :
    ∀ᵐ x : AddCircle L,
      (∫ t, treeIntegrand hk (factorField (L := L) k u (.node () l r))
        (finiteFactorPaths (.node () l r)) Y (t, x) ∂
          (Measure.pi (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) =>
            positiveMeasure))) =
      ∫ root : ℝ, ∫ sub : (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) → ℝ,
        treeIntegrand hk (factorField (L := L) k u (.node () l r))
          (finiteFactorPaths (.node () l r)) Y
          ((MeasurableEquiv.piCongrLeft
            (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) => ℝ)
            (QuantumNLS.TerraMultiRound54IndexSplit.splitEquiv l r))
              (optionAssembly (sub, root)), x)
          ∂(Measure.pi (fun _ => positiveMeasure)) ∂positiveMeasure := by
  filter_upwards [physical_kernel_parent_root hk u l r Y] with x hx
  exact parent_root_fubini l r (fun t => treeIntegrand hk
    (factorField (L := L) k u (.node () l r))
    (finiteFactorPaths (.node () l r)) Y (t, x)) hx

#print axioms vertexField_rep
#print axioms physical_kernel_parent_root
#print axioms physical_kernel_root_fubini
end QuantumNLS.TerraMultiRound55KernelFubini
