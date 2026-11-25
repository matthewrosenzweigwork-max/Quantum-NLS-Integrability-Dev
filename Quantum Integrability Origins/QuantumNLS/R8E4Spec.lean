import QuantumNLS.UnconditionalBetheBasis
/-! integrator-authored trusted spec for R-8E4D05E7 (the complete normalized Bethe basis; Terra r133 ACCEPT): BCB1's
BasisConclusion (nonvanishing, density, orthogonality, Hamiltonian eigenrelation, normalization, orthonormality,
normalized density) now holds UNCONDITIONALLY for L > 0, N ≥ 1, c > 0 (and c = κ/N), with the physical Hilbert basis
indexed by MArr N; statements copied verbatim from UBB1. -/
namespace R8E4Spec
open Set Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate NNReal
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
  QuantumNLS.HighMomentsRank QuantumNLS.NormalizedTransfer QuantumNLS.HighMomentsTransfer
  QuantumNLS.HighMomentsDerivative QuantumNLS.BetheCoefficientTransform QuantumNLS.HighMomentsOps
  QuantumNLS.HighMomentsFinal QuantumNLS.NormalityBridge QuantumNLS.BetheConditionalBasis
  QuantumNLS.BethePhysicalTransfer QuantumNLS.ContactOperator QuantumNLS.BetheFreeFamily
  QuantumNLS.BetheContinuityInputs QuantumNLS.BetheBasisOrthogonality
  QuantumNLS.AbstractContinuityProof
open QuantumNLS QuantumNLS.UnconditionalBetheBasis

theorem basisConclusion_def (L : ℝ) [Fact (0 < L)] (N : ℕ) (c : ℝ≥0) :
    BetheConditionalBasis.BasisConclusion L N c ↔ ((∀ n, sourceWave L N c n ≠ 0) ∧
  (Submodule.span ℂ (range (sourceWave L N c))).topologicalClosure = ⊤ ∧
  (∀ n m, n ≠ m → ⟪sourceWave L N c n, sourceWave L N c m⟫_ℂ = 0) ∧
  (∀ n, ∃ h : sourceWave L N c n ∈ (Hop (L := L) c c.property).domain,
    Hop c c.property ⟨sourceWave L N c n, h⟩ =
      ((∑ j, (BetheSmooth.sourceRoots L n.val c j)^2 : ℝ) : ℂ) • sourceWave L N c n) ∧
  (∀ n, ‖normalizedWave L N c n‖ = 1) ∧
  Orthonormal ℂ (normalizedWave L N c) ∧
  (Submodule.span ℂ (range (normalizedWave L N c))).topologicalClosure = ⊤ ∧
  (∀ n, ∃ h : normalizedWave L N c n ∈ (Hop (L := L) c c.property).domain,
    Hop c c.property ⟨normalizedWave L N c n, h⟩ =
      ((∑ j, (BetheSmooth.sourceRoots L n.val c j)^2 : ℝ) : ℂ) • normalizedWave L N c n)) := Iff.rfl

theorem density_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (c : ℝ≥0) :
    (Submodule.span ℂ (range (wave (L := L) c : Label (N+1) → SymL2 L (N+1)))).topologicalClosure = ⊤ := by
  apply QuantumNLS.UnconditionalBetheBasis.density <;> assumption

theorem dense_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (c : ℝ≥0) :
    (Submodule.span ℂ (range (wave (L := L) c : Label (N+1) → SymL2 L (N+1)))).topologicalClosure = ⊤ := by
  apply QuantumNLS.UnconditionalBetheBasis.dense <;> assumption

theorem basis_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) :
    BasisConclusion L N ⟨c, hc.le⟩ := by
  apply QuantumNLS.UnconditionalBetheBasis.basis <;> assumption

theorem meanField_basis_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) {κ : ℝ} (hκ : 0 < κ) :
    BasisConclusion L N ⟨κ / N, (div_pos hκ (by exact_mod_cast hN)).le⟩ := by
  apply QuantumNLS.UnconditionalBetheBasis.meanField_basis <;> assumption

theorem physicalBasis_position_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c)
    (m : BetheLabels.MArr N) :
    symmetricPosition L N (physicalBasis L N hN c hc m) =
      normalizedWave L N ⟨c, hc.le⟩ ((labelArr N).symm m) := by
  apply QuantumNLS.UnconditionalBetheBasis.physicalBasis_position <;> assumption

theorem coefficientTransform_apply_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ)
    (hc : 0 < c) (ψ : physSector L N) (m : BetheLabels.MArr N) :
    coefficientTransform L N hN c hc ψ m =
      ⟪normalizedWave L N ⟨c, hc.le⟩ ((labelArr N).symm m), symmetricPosition L N ψ⟫_ℂ := by
  apply QuantumNLS.UnconditionalBetheBasis.coefficientTransform_apply <;> assumption

theorem bornLaw_hasSum_one_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c)
    (u : L2T L) (hu : ‖u‖ = 1) :
    HasSum (BetheCoefficientTransform.bornLaw (physicalBasis L N hN c hc) u) 1 := by
  apply QuantumNLS.UnconditionalBetheBasis.bornLaw_hasSum_one <;> assumption

end R8E4Spec
#print axioms R8E4Spec.density_spec
#print axioms R8E4Spec.dense_spec
#print axioms R8E4Spec.basis_spec
#print axioms R8E4Spec.meanField_basis_spec
#print axioms R8E4Spec.physicalBasis_position_spec
#print axioms R8E4Spec.coefficientTransform_apply_spec
#print axioms R8E4Spec.bornLaw_hasSum_one_spec
