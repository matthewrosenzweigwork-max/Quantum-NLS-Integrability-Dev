import QuantumNLS.RootEnergyMoment
/-! integrator-authored trusted spec for R-484B3F6D thm:root-energy-moment (terra_review r189 PASS): headline statement(s) copied verbatim from RootEnergyMoment (QuantumNLS.RootEnergyMoment). -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.ProductEnergyPreparation QuantumNLS.ChargeEnergy
open QuantumNLS.RootEnergyMomentLaws QuantumNLS.RootEnergyMomentExpectation
open QuantumNLS.RootEnergyMomentBounded QuantumNLS.RootEnergyMomentAverage
open QuantumNLS.RootEnergyMomentTails QuantumNLS.BulkResponseActual
namespace QuantumNLS.R484Spec
open QuantumNLS.RootEnergyMoment
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_energy_moment_spec (hκ : 0 < κ) (u : L2T L) (hH : OneH1 u) :
    Integrable (fun t : ℝ => t^2) (QuantumNLS.FullMass.Mmeas κ u) ∧
    (∫ t : ℝ,t^2 ∂QuantumNLS.FullMass.Mmeas κ u) = energyH1 κ (u : AddCircle L → ℂ) ∧
    ∀ hu : ‖u‖ = 1,
      (∀ n, Integrable (fun t : ℝ => t^2) (barycenter hκ u hu n) ∧
        (∫ t : ℝ,t^2 ∂barycenter hκ u hu n) =
          energyH1 κ (u : AddCircle L → ℂ) - κ*quartic (u : AddCircle L → ℂ)/((n+1 : ℕ) : ℝ)) ∧
      (∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 < R ∧ ∀ n,squareTail (barycenter hκ u hu n) R < ε) ∧
      (∀ n,Integrable (fun m : QuantumNLS.BetheLabels.MArr (n+1) =>
        ∫ t : ℝ,t^2 ∂EmpiricalRapidity.empiricalMeasure L (κ/((n+1 : ℕ) : ℝ)) m)
          (law hκ u hu (n+1))) ∧
      Tendsto (fun n => ∫ m,|(∫ t : ℝ,t^2 ∂EmpiricalRapidity.empiricalMeasure L (κ/((n+1 : ℕ) : ℝ)) m) -
        energyH1 κ (u : AddCircle L → ℂ)| ∂law hκ u hu (n+1)) atTop (nhds 0) := by
  exact QuantumNLS.RootEnergyMoment.root_energy_moment hκ u hH

end QuantumNLS.R484Spec
#print axioms QuantumNLS.R484Spec.root_energy_moment_spec
