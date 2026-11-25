import QuantumNLS.RootWeightedMassesR26
/-! integrator-authored trusted spec for R-A8F7B7B0 thm:root-weighted-masses (terra_review r193 PASS): headline statement(s) copied verbatim from RootWeightedMassesR26 (QuantumNLS.RootWeightedMassesR26). -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.RA8FSpec
open QuantumNLS.RootWeightedMassesR26
open PhysicalTensor (L2T)
open RootWeightedCellsR26 RootWeightedMomentsR26 RootWeightedIdentitiesR26
open RootWeightedPhysicalR26 RootWeightedFirstR26 RootWeightedPlaneR26
open ProductEnergyPreparation (OneH1)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_weighted_masses_spec (hκ : 0 < κ) (u : L2T L) :
    Integrable (fun x => (x-cellMomentum hκ u x)^2) (PhysicalQuantumMeasure.measure hκ u) ∧
    0 ≤ displacement hκ u ∧ displacement hκ u ≤ κ*‖u‖^4/L ∧
    (Integrable (fun x : ℝ => x^2) (PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n : ℤ => momentum L n^2*(RootIndexedMasses.masses hκ u).1 n)) ∧
    ∀ hH : OneH1 u,
      Summable (fun n : ℤ => |momentum L n*(RootIndexedMasses.masses hκ u).1 n|) ∧
      Summable (fun n : ℤ => |momentum L n^2*(RootIndexedMasses.masses hκ u).1 n|) ∧
      ⟪u,-Complex.I • weakDerivative u hH⟫_ℂ =
        ((∑' n : ℤ,momentum L n*(RootIndexedMasses.masses hκ u).1 n : ℝ) : ℂ) ∧
      ‖weakDerivative u hH‖^2+κ*ChargeEnergy.quartic (u : AddCircle L → ℂ) =
        (∑' n : ℤ,momentum L n^2*(RootIndexedMasses.masses hκ u).1 n) +
          2*κ*‖u‖^4/L-displacement hκ u ∧
      κ*‖u‖^4/L ≤ ‖weakDerivative u hH‖^2+κ*ChargeEnergy.quartic (u : AddCircle L → ℂ) -
        (∑' n : ℤ,momentum L n^2*(RootIndexedMasses.masses hκ u).1 n) ∧
      ‖weakDerivative u hH‖^2+κ*ChargeEnergy.quartic (u : AddCircle L → ℂ) -
        (∑' n : ℤ,momentum L n^2*(RootIndexedMasses.masses hκ u).1 n) ≤ 2*κ*‖u‖^4/L ∧
      (u ≠ 0 → ∀ k : ℤ,
        (∀ n : ℤ,(RootIndexedMasses.masses hκ u).1 n = if n=k then ‖u‖^2 else 0) ↔
          ∃ a : ℂ,(u : AddCircle L → ℂ) =ᵐ[volume] fun x => a*_root_.fourier k x) := by
  exact QuantumNLS.RootWeightedMassesR26.root_weighted_masses hκ u

end QuantumNLS.RA8FSpec
#print axioms QuantumNLS.RA8FSpec.root_weighted_masses_spec
