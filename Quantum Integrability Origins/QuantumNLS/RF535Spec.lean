import QuantumNLS.RF535Final
/-! integrator-authored trusted spec for R-F5355ABD thm:global-actual-chart (review record r57 ACCEPT): headline statement(s) copied verbatim from RF535Final (QuantumNLS.RF535Final). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory BoundedContinuousFunction
namespace QuantumNLS.RF535Spec
open QuantumNLS.RF535Final
open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoser QuantumNLS.ResetMoserClamp
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (fourierL2 modeLp)
open QuantumNLS.Local021 QuantumNLS.Local021R QuantumNLS.Local023
open QuantumNLS.LocalSpectral (pm)
open QuantumNLS.RootIndexedMasses (masses)
open QuantumNLS.ResetNormalizationUniqueness (IsStronglySymplecticOn Cphys)
open QuantumNLS.ActionTorus (PosL1 actionTorus rotate)
open QuantumNLS.ProductTorusGenerator (Linf)
open QuantumNLS.Ext025B6TorusCoordinates (Torus)
variable {L κ : ℝ} [Fact (0 < L)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 8000000 in
theorem global_actual_chart_spec (L : ℝ) [Fact (0 < L)] :
    (∃ d CL : ℝ, 0 < d ∧ 0 ≤ CL ∧ ∃ (Φloc : ℝ → L2T L → K) (Ψloc : ℝ → K → L2T L), Local023Body L d CL Φloc Ψloc) ∧
    ∀ (d CL : ℝ) (Φloc : ℝ → L2T L → K) (Ψloc : ℝ → K → L2T L), 0 < d → 0 ≤ CL →
      Local023Body L d CL Φloc Ψloc →
      ∀ (κ : ℝ) (hκ : 0 < κ), GlobalStatement L κ hκ d (Φloc κ) (Ψloc κ) := by
  exact QuantumNLS.RF535Final.global_actual_chart L

end QuantumNLS.RF535Spec
#print axioms QuantumNLS.RF535Spec.global_actual_chart_spec
