import QuantumNLS.BetheChargeResolution
/-! integrator-authored trusted spec for R-892D1666 prop:transfer (Terra r139 ACCEPT): BBT1 transfer consequences in the
unconditional physical basis (entire, eigenrelation, normality/commutation, spectral projections, bound) and BCR1's identification
of chargeProjection with the spectral projection of the actual maximal charge; statements copied verbatim. -/
namespace R892Spec
open scoped BigOperators InnerProductSpace ComplexConjugate
open QuantumNLS.PhysicalTensor QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.NormalizedTransfer QuantumNLS.NormalityBridge QuantumNLS.BetheLabels
open scoped BigOperators InnerProductSpace ComplexConjugate LinearPMap
open QuantumNLS.BetheSpectralCharges QuantumNLS.BetheCoefficientTransform QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels
open QuantumNLS.BoundedBetheTransfer Function
open QuantumNLS QuantumNLS.BoundedBetheTransfer QuantumNLS.BetheChargeResolution

set_option maxHeartbeats 4000000 in
theorem transfer_consequences_spec (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) :
    Differentiable ℂ (normalizedTransfer L κ N) ∧
    (∀ z, Commute (normalizedTransfer L κ N z).adjoint (normalizedTransfer L κ N z) ∧
      (∀ w, Commute (normalizedTransfer L κ N z) (normalizedTransfer L κ N w) ∧
        Commute (normalizedTransfer L κ N z) (normalizedTransfer L κ N w).adjoint) ∧
      ∀ r s, Commute (normalizedTransfer L κ N z) (chargeProjection L hκ hN r s)) ∧
    ∀ η, 0 < η → ∀ z, z.im = η →
      ‖normalizedTransfer L κ N z‖ ≤ 2 * (1 + κ / ((N : ℝ) * η)) ^ N ∧
      2 * (1 + κ / ((N : ℝ) * η)) ^ N ≤ 2 * Real.exp (κ / η) := by
  apply QuantumNLS.BoundedBetheTransfer.transfer_consequences <;> assumption

set_option maxHeartbeats 4000000 in
theorem chargeProjection_orthogonal_spec (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (r : ℕ) (s : Set ℝ) :
    (chargeProjection L hκ hN r s).adjoint = chargeProjection L hκ hN r s ∧
    chargeProjection L hκ hN r s * chargeProjection L hκ hN r s = chargeProjection L hκ hN r s := by
  apply QuantumNLS.BoundedBetheTransfer.chargeProjection_orthogonal <;> assumption

set_option maxHeartbeats 4000000 in
theorem commute_chargeProjection_spec (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (z : ℂ) (r : ℕ) (s : Set ℝ) :
    Commute (normalizedTransfer L κ N z) (chargeProjection L hκ hN r s) := by
  apply QuantumNLS.BoundedBetheTransfer.commute_chargeProjection <;> assumption

set_option maxHeartbeats 4000000 in
theorem exponential_bound_spec (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (η : ℝ) (hη : 0 < η) :
    2 * (1 + κ / ((N : ℝ) * η)) ^ N ≤ 2 * Real.exp (κ / η) := by
  apply QuantumNLS.BoundedBetheTransfer.exponential_bound <;> assumption

set_option maxHeartbeats 4000000 in
theorem physical_spectralProjection_eq_chargeProjection_spec (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (r : ℕ) (s : Set ℝ)
    (_hs : MeasurableSet s) :
    (physicalChargeResolution L hκ hN r).measure.toFun s =
      chargeProjection L hκ hN r s := by
  apply QuantumNLS.BetheChargeResolution.physical_spectralProjection_eq_chargeProjection <;> assumption

set_option maxHeartbeats 4000000 in
theorem physical_spectralProjection_unique_spec (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (r : ℕ)
    (R : AtomicSpectralResolution (charge
      (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) (κ / N) r))
    (s : Set ℝ) (hs : MeasurableSet s) :
    R.measure.toFun s = chargeProjection L hκ hN r s := by
  apply QuantumNLS.BetheChargeResolution.physical_spectralProjection_unique <;> assumption

end R892Spec
#print axioms R892Spec.transfer_consequences_spec
#print axioms R892Spec.chargeProjection_orthogonal_spec
#print axioms R892Spec.commute_chargeProjection_spec
#print axioms R892Spec.exponential_bound_spec
#print axioms R892Spec.physical_spectralProjection_eq_chargeProjection_spec
#print axioms R892Spec.physical_spectralProjection_unique_spec
