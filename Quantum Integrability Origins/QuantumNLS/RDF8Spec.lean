import QuantumNLS.RDF8Main
/-! integrator-authored trusted spec for R-DF8F25DD thm:root-H1-characterization (review record r46 PASS): headline statement(s) copied verbatim from RDF8Main (QuantumNLS.RDF8Main). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Fourier QuantumNLS.RootH1RatioConvergence
namespace QuantumNLS.RDF8Spec
open QuantumNLS.RDF8Main
open QuantumNLS.ProductEnergyPreparation (OneH1)
variable {L : ℝ} [hLf : Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_H1_characterization_spec {κ : ℝ} (hκ : 0 < κ) (u : L2T L) :
    (OneH1 u ↔ Integrable (fun t : ℝ => t ^ 2) (FullMass.Mmeas κ u)) ∧
    (Integrable (fun t : ℝ => t ^ 2) (FullMass.Mmeas κ u) ↔
      Summable (fun n : ℤ =>
        RootWeightedCellsR26.momentum L n ^ 2 * (RootIndexedMasses.masses hκ u).1 n)) ∧
    (∀ hH : OneH1 u,
      ((∫ t : ℝ, t ^ 2 ∂FullMass.Mmeas κ u) = ChargeEnergy.energyH1 κ (u : AddCircle L → ℂ)) ∧
      Summable (fun n : ℤ =>
        |RootWeightedCellsR26.momentum L n ^ 2 * (RootIndexedMasses.masses hκ u).1 n|) ∧
      (‖RootWeightedPhysicalR26.weakDerivative u hH‖ ^ 2 +
          κ * ChargeEnergy.quartic (u : AddCircle L → ℂ) =
        (∑' n : ℤ, RootWeightedCellsR26.momentum L n ^ 2 * (RootIndexedMasses.masses hκ u).1 n) +
          2 * κ * ‖u‖ ^ 4 / L - RootWeightedCellsR26.displacement hκ u) ∧
      (‖u‖ ^ 2 + ‖RootWeightedPhysicalR26.weakDerivative u hH‖ ^ 2 ≤
        ‖u‖ ^ 2 +
          (∑' n : ℤ, RootWeightedCellsR26.momentum L n ^ 2 * (RootIndexedMasses.masses hκ u).1 n) +
          2 * κ * (‖u‖ ^ 2) ^ 2 / L) ∧
      (hsNormSq L 1 (fun n => fourierL2 L u n) ≤
        2 * (‖u‖ ^ 2 + ‖RootWeightedPhysicalR26.weakDerivative u hH‖ ^ 2)) ∧
      (2 * (‖u‖ ^ 2 + ‖RootWeightedPhysicalR26.weakDerivative u hH‖ ^ 2) ≤
        2 * ‖u‖ ^ 2 +
          2 * (∑' n : ℤ, RootWeightedCellsR26.momentum L n ^ 2 * (RootIndexedMasses.masses hκ u).1 n) +
          4 * κ * (‖u‖ ^ 2) ^ 2 / L)) ∧
    (u ≠ 0 → ∀ k : ℤ,
      (∀ n : ℤ, n ≠ k → (RootIndexedMasses.masses hκ u).1 n = 0) ↔
        ∃ a : ℂ, a ≠ 0 ∧ (u : AddCircle L → ℂ) =ᵐ[volume] fun x => a * _root_.fourier k x) := by
  exact QuantumNLS.RDF8Main.root_H1_characterization hκ u

end QuantumNLS.RDF8Spec
#print axioms QuantumNLS.RDF8Spec.root_H1_characterization_spec
