import QuantumNLS.RootEnergyVectorField
/-! integrator-authored trusted spec for R-63A99F0E prop:root-energy-vector-field (review record r34 PASS): headline statement(s) copied verbatim from RootEnergyVectorField (QuantumNLS.RootEnergyVectorField). -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.Sobolev
  QuantumNLS.Sobolev.PosWeight QuantumNLS.LocalWellPosedness
  QuantumNLS.F04Regularity QuantumNLS.RootEnergyVariation
  QuantumNLS.PhysicalTensor QuantumNLS.ProductEnergyPreparation QuantumNLS.WeakDerivatives
namespace QuantumNLS.R63ASpec
open QuantumNLS.RootEnergyVectorField
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_energy_vector_field_spec (κ : ℝ) (u : h04 L 2) :
    let a := m21 u
    let U := physical (m10 a)
    let Ux := physical (Complex.I • D a)
    let Uxx := -physical (lap u)
    let C := physical (m10 (Fh (le_refl (1 : ℝ)) a))
    (HasWeakDeriv U Ux ∧ HasWeakDeriv Ux Uxx) ∧
    ((C : AddCircle L → ℂ) =ᵐ[volume]
      fun x => ((‖U x‖ ^ 2 : ℝ) : ℂ) * U x) ∧
    energy κ a = QuantumNLS.ChargeEnergy.energyH1 κ (U : AddCircle L → ℂ) ∧
    (∀ (c : ℝ) (N : ℕ), ∃ Ψ : QuantumNLS.PhysicalEnergy.PhysH1 L N,
      Ψ.val = prodState U N ∧
      QuantumNLS.ContactProductIntegrals.PiSquareFubini Ψ.val ∧
      QuantumNLS.ContactForm.q c Ψ Ψ =
        ((N * (‖U‖ ^ 2) ^ (N-1) * QuantumNLS.ChargeEnergy.kinetic (U : AddCircle L → ℂ) +
          c * N * ((N : ℝ)-1) * (‖U‖ ^ 2) ^ (N-2) *
            QuantumNLS.ChargeEnergy.quartic (U : AddCircle L → ℂ) : ℝ) : ℂ)) ∧
    ((U = 0 ∧ energy κ a = 0) ∨
      ∃ (v : L2T L) (hv : ‖v‖ = 1) (hH : OneH1 v),
        U = (‖U‖ : ℂ) • v ∧
        Tendsto (fun N : ℕ => ‖U‖ ^ 2 *
          (hN (κ * ‖U‖ ^ 2) N (productH1 hv hH N) / N)) atTop
            (nhds (energy κ a))) ∧
    HasFDerivAt (energy κ) (differential κ u) a ∧
    (∀ h : h04 L 1,
      differential κ u h = 2 * (⟪-Uxx + ((2 * κ : ℝ) : ℂ) • C,
        physical (m10 h)⟫_ℂ).re ∧
      omega (X κ u) (physical (m10 h)) = differential κ u h) ∧
    Complex.I • X κ u = -Uxx + ((2 * κ : ℝ) : ℂ) • C := by
  exact QuantumNLS.RootEnergyVectorField.root_energy_vector_field κ u

end QuantumNLS.R63ASpec
#print axioms QuantumNLS.R63ASpec.root_energy_vector_field_spec
