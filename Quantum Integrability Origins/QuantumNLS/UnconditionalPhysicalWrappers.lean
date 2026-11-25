import QuantumNLS.AbstractContinuityProof
import QuantumNLS.BetheConditionalBasis
import QuantumNLS.BetheSpectralCharges
import QuantumNLS.BetheOccupationGauge
import QuantumNLS.BalancedWickDefinition
import QuantumNLS.CommonBethePacket
import QuantumNLS.ExactOccupationAlgebra
import QuantumNLS.CartesianOccupationTransfer
import QuantumNLS.FullOccupationAffinity
import QuantumNLS.UnitPhaseTransfer

/-!
# Unconditional physical wrappers: the frozen `AbstractContinuity`-hypothesis declarations at `hcont := ACP1`

Each wrapper instantiates a frozen declaration that takes `hcont : BetheConditionalBasis.AbstractContinuity`
as an explicit hypothesis, with the accepted proof `QuantumNLS.AbstractContinuityProof.abstractContinuity`
(the review ACP1). The statement is the source statement with `hcont` replaced by that proof, and every other binder
is unchanged. Definitions omit the return type and theorems use the placeholder `_`, so the statement is the
one Lean infers from the source declaration (no retyping). Nothing frozen is edited.

Wrapped declarations (source module, wrapper name):
* BalancedWickDefinition: `betheWick`, `meanFieldWick`;
* BetheOccupationGauge: `sectorBasis`, `selectedBasis`, `selectedBasis_apply`, `selectedTransform`,
  `selectedMeanFieldBasis`, `selectedMeanFieldTransform`;
* BetheSpectralCharges: `betheCharge_basis`, `betheCharge`, `betheCharge_domain`, `oneCoordinateBasis_eq`,
  `onePhysicalBasis_eq`, `sectorBasis`, `sectorCharge`;
* CommonBethePacket: `meanFieldBasis`, `IsCommonMeanField`;
* ExactOccupationAlgebra: `selected_comm`, `meanField_comm`;
* CartesianOccupationTransfer: `selectedPhysical`, `selectedMeanFieldPhysical`;
* FullOccupationAffinity: `selectedCoefficients`, `selectedMeanFieldCoefficients`;
* UnitPhaseTransfer: `selectedPhysical`, `selectedMeanFieldPhysical`;
* BetheConditionalBasis (BCB1 core, not already wrapped by `UnconditionalBetheBasis`): `density_from_continuity`,
  `coordinateBasis`, `coordinateBasis_apply`.

Already covered by `UnconditionalBetheBasis` (not repeated here): `dense`, `basis`, `meanField_basis`,
`physicalBasis`, `physicalBasis_position`, `coefficientTransform`, `coefficientTransform_apply`,
`meanField_physicalBasis`, `bornLaw_hasSum_one` (BCB1), `meanField_isBetheBasis`, `transfer_physicalBasis`,
`normal_deriv_physical`, `commute_deriv_physical`, `transfer_moments_physical`, `transfer_moments_deriv_physical`
(ConditionalBetheNormality). The FiniteCell* modules, CompactSpectralHelpers, SpectralFamilySteps and
SpectralLeftStep contain no hypothesis binder (their `AbstractContinuity` mentions are audit guards or comments).

Standard axioms only; no `sorry`, no custom axioms.
-/

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.UnconditionalPhysicalWrappers

/-- The accepted ACP1 proof of the abstract continuity principle. -/
abbrev acp : QuantumNLS.BetheConditionalBasis.AbstractContinuity :=
  QuantumNLS.AbstractContinuityProof.abstractContinuity

namespace BCB1core
open Set Filter
open scoped BigOperators Topology InnerProductSpace NNReal
open PhysicalTensor BethePhysicalTransfer ContactOperator BetheFreeFamily BetheContinuityInputs

theorem density_from_continuity_physical (L : ℝ) [Fact (0 < L)] (N : ℕ) (c : ℝ≥0) :
    (Submodule.span ℂ (range (wave (L := L) c : Label (N+1) → SymL2 L (N+1)))).topologicalClosure = ⊤ :=
  QuantumNLS.BetheConditionalBasis.density_from_continuity acp L N c

def coordinateBasis_physical (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) :=
  QuantumNLS.BetheConditionalBasis.coordinateBasis acp L N hN c hc

theorem coordinateBasis_apply_physical (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c)
    (n : Label N) :
    QuantumNLS.BetheConditionalBasis.coordinateBasis acp L N hN c hc n =
      QuantumNLS.BetheConditionalBasis.normalizedWave L N ⟨c, hc.le⟩ n :=
  QuantumNLS.BetheConditionalBasis.coordinateBasis_apply acp L N hN c hc n

end BCB1core

namespace BalancedWick
open scoped BigOperators InnerProductSpace
open WickSymbols WickBounds Occupation OccupationHilbert BetheCoefficientTransform PhysicalTensor

def betheWick_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection) (L : ℝ) [Fact (0 < L)]
    (c : ℝ) (hc : 0 < c) (N : ℕ) (f : QuantumNLS.BalancedWickDefinition.Polynomial) :=
  QuantumNLS.BalancedWickDefinition.betheWick acp s L c hc N f

def meanFieldWick_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection) (L : ℝ) [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (f : QuantumNLS.BalancedWickDefinition.Polynomial) :=
  QuantumNLS.BalancedWickDefinition.meanFieldWick acp s L κ hκ N hN f

end BalancedWick

namespace OccGauge
open scoped BigOperators InnerProductSpace
open BetheLabels BetheCoefficientTransform PhysicalTensor BetheSpectralCharges

def sectorBasis_physical (L : ℝ) [Fact (0 < L)] (c : ℝ) (hc : 0 < c) :=
  QuantumNLS.BetheOccupationGauge.sectorBasis acp L c hc

def selectedBasis_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection) (L : ℝ) [Fact (0 < L)]
    (c : ℝ) (hc : 0 < c) (N : ℕ) :=
  QuantumNLS.BetheOccupationGauge.selectedBasis acp s L c hc N

theorem selectedBasis_apply_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (c : ℝ) (hc : 0 < c) (N : ℕ) (m : MArr N) :
    QuantumNLS.BetheOccupationGauge.selectedBasis acp s L c hc N m =
      (s L Fact.out c hc N m).val • QuantumNLS.BetheOccupationGauge.sectorBasis acp L c hc N m :=
  QuantumNLS.BetheOccupationGauge.selectedBasis_apply acp s L c hc N m

def selectedTransform_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection) (L : ℝ) [Fact (0 < L)]
    (c : ℝ) (hc : 0 < c) (N : ℕ) :=
  QuantumNLS.BetheOccupationGauge.selectedTransform acp s L c hc N

def selectedMeanFieldBasis_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) :=
  QuantumNLS.BetheOccupationGauge.selectedMeanFieldBasis acp s L κ hκ N hN

def selectedMeanFieldTransform_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) :=
  QuantumNLS.BetheOccupationGauge.selectedMeanFieldTransform acp s L κ hκ N hN

end OccGauge

namespace SpecCharges
open scoped BigOperators InnerProductSpace NNReal
open BetheLabels BetheCoefficientTransform PhysicalTensor QuantumNLS.BetheSpectralCharges

theorem betheCharge_basis_physical (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c)
    (r : ℕ) (m : MArr N) :
    ∃ h : QuantumNLS.BetheConditionalBasis.physicalBasis acp L N hN c hc m ∈
      (charge (QuantumNLS.BetheConditionalBasis.physicalBasis acp L N hN c hc) c r).domain,
      charge (QuantumNLS.BetheConditionalBasis.physicalBasis acp L N hN c hc) c r
        ⟨QuantumNLS.BetheConditionalBasis.physicalBasis acp L N hN c hc m, h⟩ =
          (eigenvalue L N c r m : ℂ) • QuantumNLS.BetheConditionalBasis.physicalBasis acp L N hN c hc m :=
  QuantumNLS.BetheSpectralCharges.betheCharge_basis acp L N hN c hc r m

def betheCharge_physical (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (r : ℕ) :=
  QuantumNLS.BetheSpectralCharges.betheCharge acp L N hN c hc r

theorem betheCharge_domain_physical (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c)
    (r : ℕ) (ψ : HN L N) :
    ψ ∈ (QuantumNLS.BetheSpectralCharges.betheCharge acp L N hN c hc r).domain ↔
      Summable (fun m => |eigenvalue L N c r m| ^ 2 *
        ‖QuantumNLS.BetheConditionalBasis.coefficientTransform acp L N hN c hc ψ m‖ ^ 2) :=
  QuantumNLS.BetheSpectralCharges.betheCharge_domain acp L N hN c hc r ψ

theorem oneCoordinateBasis_eq_physical (L : ℝ) [Fact (0 < L)] (c : ℝ) (hc : 0 < c) :
    oneCoordinateBasis L c hc = QuantumNLS.BetheConditionalBasis.coordinateBasis acp L 1 (by omega) c hc :=
  QuantumNLS.BetheSpectralCharges.oneCoordinateBasis_eq acp L c hc

theorem onePhysicalBasis_eq_physical (L : ℝ) [Fact (0 < L)] (c : ℝ) (hc : 0 < c) :
    onePhysicalBasis L c hc = QuantumNLS.BetheConditionalBasis.physicalBasis acp L 1 (by omega) c hc :=
  QuantumNLS.BetheSpectralCharges.onePhysicalBasis_eq acp L c hc

def sectorBasis_physical (L : ℝ) [Fact (0 < L)] (c : ℝ) (hc : 0 < c) :=
  QuantumNLS.BetheSpectralCharges.sectorBasis acp L c hc

def sectorCharge_physical (L : ℝ) [Fact (0 < L)] (c : ℝ) (hc : 0 < c) (N r : ℕ) :=
  QuantumNLS.BetheSpectralCharges.sectorCharge acp L c hc N r

end SpecCharges

namespace CommonPacket
open scoped BigOperators InnerProductSpace Topology
open BetheLabels BetheCoefficientTransform PhysicalTensor Filter QuantumNLS.CommonBethePacket

def meanFieldBasis_physical (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (n : ℕ) :=
  QuantumNLS.CommonBethePacket.meanFieldBasis acp L κ hκ n

def IsCommonMeanField_physical (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ)
    (P : (n : ℕ) → Packet (QuantumNLS.CommonBethePacket.meanFieldBasis acp L κ hκ n))
    (u : L2T L) (chargeTarget : ℕ → ℝ) (A : ActionTarget) : Prop :=
  QuantumNLS.CommonBethePacket.IsCommonMeanField acp L κ hκ P u chargeTarget A

end CommonPacket

namespace ExactAlgebra
open scoped InnerProductSpace ComplexConjugate

theorem selected_comm_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection) (L : ℝ) [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 0 < N) (a b c d : ℤ) :
    QuantumNLS.CartesianOccupationTransfer.selectedPhysical acp s L κ hκ N a b *
        QuantumNLS.CartesianOccupationTransfer.selectedPhysical acp s L κ hκ N c d -
      QuantumNLS.CartesianOccupationTransfer.selectedPhysical acp s L κ hκ N c d *
        QuantumNLS.CartesianOccupationTransfer.selectedPhysical acp s L κ hκ N a b =
    (N : ℂ)⁻¹ • ((if a = d then (1 : ℂ) else 0) •
        QuantumNLS.CartesianOccupationTransfer.selectedPhysical acp s L κ hκ N c b -
      (if b = c then (1 : ℂ) else 0) •
        QuantumNLS.CartesianOccupationTransfer.selectedPhysical acp s L κ hκ N a d) :=
  QuantumNLS.ExactOccupationAlgebra.selected_comm acp s L κ hκ N hN a b c d

theorem meanField_comm_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection) (L : ℝ) [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (a b c d : ℤ) :
    QuantumNLS.CartesianOccupationTransfer.selectedMeanFieldPhysical acp s L κ hκ N hN a b *
        QuantumNLS.CartesianOccupationTransfer.selectedMeanFieldPhysical acp s L κ hκ N hN c d -
      QuantumNLS.CartesianOccupationTransfer.selectedMeanFieldPhysical acp s L κ hκ N hN c d *
        QuantumNLS.CartesianOccupationTransfer.selectedMeanFieldPhysical acp s L κ hκ N hN a b =
    (N : ℂ)⁻¹ • ((if a = d then (1 : ℂ) else 0) •
        QuantumNLS.CartesianOccupationTransfer.selectedMeanFieldPhysical acp s L κ hκ N hN c b -
      (if b = c then (1 : ℂ) else 0) •
        QuantumNLS.CartesianOccupationTransfer.selectedMeanFieldPhysical acp s L κ hκ N hN a d) :=
  QuantumNLS.ExactOccupationAlgebra.meanField_comm acp s L κ hκ N hN a b c d

end ExactAlgebra

namespace CartesianTransfer
open scoped InnerProductSpace ComplexConjugate
open BetheLabels BetheCoefficientTransform BetheOccupationGauge Occupation

def selectedPhysical_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection) (L : ℝ) [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (a b : ℤ) :=
  QuantumNLS.CartesianOccupationTransfer.selectedPhysical acp s L κ hκ N a b

def selectedMeanFieldPhysical_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (a b : ℤ) :=
  QuantumNLS.CartesianOccupationTransfer.selectedMeanFieldPhysical acp s L κ hκ N hN a b

end CartesianTransfer

namespace FullAffinity
open scoped InnerProductSpace ComplexConjugate ENNReal
open Occupation OccupationHilbert BetheCoefficientTransform BetheOccupationGauge

def selectedCoefficients_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection) (L : ℝ) [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (ψ : {ψ : HN L N // ‖ψ‖ = 1}) :=
  QuantumNLS.FullOccupationAffinity.selectedCoefficients acp s L κ hκ N ψ

def selectedMeanFieldCoefficients_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (ψ : {ψ : HN L N // ‖ψ‖ = 1}) :=
  QuantumNLS.FullOccupationAffinity.selectedMeanFieldCoefficients acp s L κ hκ N hN ψ

end FullAffinity

namespace UnitPhase
open scoped InnerProductSpace ComplexConjugate
open BetheLabels BetheCoefficientTransform BetheOccupationGauge Occupation

def selectedPhysical_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection) (L : ℝ) [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (a b : ℤ) :=
  QuantumNLS.UnitPhaseTransfer.selectedPhysical acp s L κ hκ N a b

def selectedMeanFieldPhysical_physical (s : QuantumNLS.BetheOccupationGauge.UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (a b : ℤ) :=
  QuantumNLS.UnitPhaseTransfer.selectedMeanFieldPhysical acp s L κ hκ N hN a b

end UnitPhase

end QuantumNLS.UnconditionalPhysicalWrappers

#print axioms QuantumNLS.UnconditionalPhysicalWrappers.acp
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.BCB1core.density_from_continuity_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.BCB1core.coordinateBasis_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.BCB1core.coordinateBasis_apply_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.BalancedWick.betheWick_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.BalancedWick.meanFieldWick_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.OccGauge.sectorBasis_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.OccGauge.selectedBasis_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.OccGauge.selectedBasis_apply_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.OccGauge.selectedTransform_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.OccGauge.selectedMeanFieldBasis_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.OccGauge.selectedMeanFieldTransform_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.SpecCharges.betheCharge_basis_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.SpecCharges.betheCharge_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.SpecCharges.betheCharge_domain_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.SpecCharges.oneCoordinateBasis_eq_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.SpecCharges.onePhysicalBasis_eq_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.SpecCharges.sectorBasis_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.SpecCharges.sectorCharge_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.CommonPacket.meanFieldBasis_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.CommonPacket.IsCommonMeanField_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.ExactAlgebra.selected_comm_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.ExactAlgebra.meanField_comm_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.CartesianTransfer.selectedPhysical_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.CartesianTransfer.selectedMeanFieldPhysical_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.FullAffinity.selectedCoefficients_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.FullAffinity.selectedMeanFieldCoefficients_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.UnitPhase.selectedPhysical_physical
#print axioms QuantumNLS.UnconditionalPhysicalWrappers.UnitPhase.selectedMeanFieldPhysical_physical
