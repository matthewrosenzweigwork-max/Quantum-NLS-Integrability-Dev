import QuantumNLS.RootScalarUniquenessR28
/-! integrator-authored trusted spec for R-063C168E thm:root-scalar-uniqueness (terra_review r202/r203 PASS): headline statement(s) copied verbatim from RootScalarUniquenessR28 (QuantumNLS.RootScalarUniquenessR28). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.R063Spec
open QuantumNLS.RootScalarUniquenessR28
open PhysicalTensor (L2T)
open RootScalarContinuityR28
open TotalVariation (tvNorm)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_scalar_uniqueness_spec (hκ : 0 < κ) :
    (∀ u v : L2T L,
      (∀ n : ℤ,(RootIndexedMasses.masses hκ u).1 n = (RootIndexedMasses.masses hκ v).1 n) →
        PhysicalQuantumMeasure.measure hκ u = PhysicalQuantumMeasure.measure hκ v) ∧
    (∃! F : realized (L := L) hκ → FiniteMeasure ℝ,
      (∀ u : L2T L,(F (realizedPoint hκ u) : Measure ℝ) = PhysicalQuantumMeasure.measure hκ u) ∧
      (∀ a : realized (L := L) hκ,
        Tendsto (fun b : realized (L := L) hκ => tvNorm (F b : Measure ℝ) (F a : Measure ℝ))
          (𝓝 a) (𝓝 0))) := by
  exact QuantumNLS.RootScalarUniquenessR28.root_scalar_uniqueness hκ

end QuantumNLS.R063Spec
#print axioms QuantumNLS.R063Spec.root_scalar_uniqueness_spec
