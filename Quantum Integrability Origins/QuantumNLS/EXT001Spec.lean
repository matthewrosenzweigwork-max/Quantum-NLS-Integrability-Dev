import QuantumNLS.UnconditionalBetheBasis
/-! integrator-authored trusted spec for EXT-001 / R-9BF8373D (the abstract continuity-of-completeness principle,
periodic_basis.tex:43–85, in BCB1's shifted inverse-resolvent form; Terra r105 correspondence, r133 ACCEPT). The
proposition is written out IN FULL below (copied from BCB1's definition) and proved with no hypotheses. -/
namespace EXT001Spec
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

theorem spec :
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ι : Type) (A : ℝ≥0 → E →ₗ.[ℂ] E) (R : ℝ≥0 → E →L[ℂ] E),
    (∀ t, IsSelfAdjoint (A t)) →
    (∀ t, ∀ x : (A t).domain, ‖(x : E)‖ ^ 2 ≤ (⟪(x : E), A t x⟫_ℂ).re) →
    (∀ t f, ∃ h : R t f ∈ (A t).domain, A t ⟨R t f, h⟩ = f) →
    (∀ t (x : (A t).domain), R t (A t x) = (x : E)) →
    (∀ s t, s ≤ t → ∀ f, (⟪R t f, f⟫_ℂ).re ≤ (⟪R s f, f⟫_ℂ).re) →
    (∀ t f, Tendsto (fun s => R s f) (𝓝[≥] t) (𝓝 (R t f))) →
    IsCompactOperator (R 0) →
    ∀ (v : ℝ≥0 → ι → E) (ev : ℝ≥0 → ι → ℝ),
      (∀ i, Continuous (fun t => v t i)) →
      (∀ t i, v t i ≠ 0) →
      (∀ t, LinearIndependent ℂ (v t)) →
      (∀ t i, ∃ h : v t i ∈ (A t).domain, A t ⟨v t i, h⟩ = (ev t i : ℂ) • v t i) →
      (Submodule.span ℂ (range (v 0))).topologicalClosure = ⊤ →
      ∀ t, (Submodule.span ℂ (range (v t))).topologicalClosure = ⊤ :=
  QuantumNLS.AbstractContinuityProof.abstractContinuity

theorem spec_is_BCB1 : BetheConditionalBasis.AbstractContinuity := QuantumNLS.AbstractContinuityProof.abstractContinuity

end EXT001Spec
#print axioms EXT001Spec.spec
#print axioms EXT001Spec.spec_is_BCB1
