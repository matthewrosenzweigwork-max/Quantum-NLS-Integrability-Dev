import QuantumNLS.RootMassPropernessR27
/-! integrator-authored trusted spec for R-0191D778 thm:root-mass-properness (terra_review r199 PASS): headline statement(s) copied verbatim from RootMassPropernessR27 (QuantumNLS.RootMassPropernessR27). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.R019Spec
open QuantumNLS.RootMassPropernessR27
open PhysicalTensor (L2T)
open ActionTorus RootWeightedCellsR26 RootMassSpectralR27 RootMassBoundR27
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_mass_properness_spec (hκ : 0 < κ) :
    (∀ (u : L2T L) (Y : ℝ),
      max 1 (max (Real.log 3/L) (16*κ*‖u‖^2)) ≤ Y →
      fourierTail Y u ≤
        4*(∑' n : ℤ,min 1 (momentum L n^2/Y^2)*(RootIndexedMasses.masses (L := L) hκ u).1 n)+
          4*κ*‖u‖^4/(L*Y^2)+8*κ*‖u‖^4/Y) ∧
    Continuous (RootIndexedMasses.masses (L := L) hκ) ∧
    (∀ K : Set PosL1,IsCompact K → IsCompact ((RootIndexedMasses.masses (L := L) hκ) ⁻¹' K)) ∧
    (∀ a : PosL1,IsCompact ((RootIndexedMasses.masses (L := L) hκ) ⁻¹' {a})) ∧
    IsClosed (Set.range (RootIndexedMasses.masses (L := L) hκ)) := by
  exact QuantumNLS.RootMassPropernessR27.root_mass_properness hκ

end QuantumNLS.R019Spec
#print axioms QuantumNLS.R019Spec.root_mass_properness_spec
