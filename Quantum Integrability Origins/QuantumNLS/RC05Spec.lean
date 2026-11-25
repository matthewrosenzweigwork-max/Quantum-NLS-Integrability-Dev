import QuantumNLS.RC05Displayed
/-! integrator-authored trusted spec for R-C05E2420 displayed theorem (review record r72 conditional PASS): headline statement(s) copied verbatim from RC05Displayed (QuantumNLS.RC05Displayed). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open scoped ENNReal Topology ComplexConjugate
open Filter Set Metric
namespace QuantumNLS.RC05Spec
open QuantumNLS.RC05Displayed
open QuantumNLS.StrongSymplectic QuantumNLS.REF88PrintedChartLocal QuantumNLS.RC05Statement QuantumNLS.RC05Parts
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.RF535Final (Local023Body)
open QuantumNLS.GlobalCompatR47a (Family Compatibility)

set_option maxHeartbeats 8000000 in
theorem global_full_transform_spec :
    (∀ (L : ℝ) [Fact (0 < L)], ∃ d CL : ℝ, 0 < d ∧ 0 ≤ CL ∧
      ∃ (Φl : ℝ → L2T L → K) (Ψl : ℝ → K → L2T L),
        Local023Body L d CL Φl Ψl ∧ (∃ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L), Family d Φl Ψl Φ Ψ) ∧
        ∀ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L), Family d Φl Ψl Φ Ψ → PrintedTransform L d CL Φl Ψl Φ Ψ) ∧
    PeriodConversion ∧
    (∀ (c κ : ℝ) (hc : c ≠ 0) (hκ : 0 < κ), RephasingStatement c κ hc hκ) := by
  exact QuantumNLS.RC05Displayed.global_full_transform 

theorem PrintedTransform_literal (L : ℝ) [Fact (0 < L)] (d CL : ℝ) (Φl : ℝ → L2T L → K) (Ψl : ℝ → K → L2T L)
    (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L) :
    QuantumNLS.RC05Displayed.PrintedTransform L d CL Φl Ψl Φ Ψ ↔ (
  -- (1) item 1: the map of `thm:global-actual-chart`, strongly symplectic (DEF-016), characterized as the global chart
  (∀ (κ : ℝ) (hκ : 0 < κ), GlobalClauses L κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ) ∧
    IsStronglySymplectic (Φ κ) ∧ IsGlobalChart L κ hκ (Φ κ)) ∧
  -- (2), (3), (4) items 2-4: the physical dynamics, frequencies and Sobolev statements (R-EF8C2837)
  (∀ (κ : ℝ) (hκ : 0 < κ), ∃ hs : IsStronglySymplectic (Φ κ), PhysDyn hκ hs) ∧
  -- (5) items 5 and 6: covariances, scaling, joint analyticity, free limit with bounds, uniqueness (R-CA92819A)
  Compatibility d CL Φ Ψ ∧
  -- (6) item 6: necessity of the real identity, the action-dependent canonical phase freedom (R-8DD5AE6E)
  (∀ (κ : ℝ) (hκ : 0 < κ) (c : ℝ), c ≠ 0 → RephasingFreedom hκ (Φ κ) c)) := Iff.rfl

theorem PeriodConversion_literal  :
    QuantumNLS.RC05Statement.PeriodConversion  ↔ (
  ∀ (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ)
    (G : L2T L → K) (G1 : L2T 1 → K) (G11 : L2T 1 → K),
    IsGlobalChart L κ hκ G → IsGlobalChart 1 (κ * L) (mul_pos hκ (Fact.out : 0 < L)) G1 →
    IsGlobalChart 1 1 one_pos G11 →
    ∀ u : L2T L,
      G u = G1 (QuantumNLS.PeriodFieldR42b.period L u) ∧
      G u = (Real.sqrt (κ * L))⁻¹ • G11 (QuantumNLS.IndependentScalingConversionR42b.unitPotential L κ u)) := Iff.rfl

theorem RephasingStatement_literal (c κ : ℝ) (hc : c ≠ 0) (hκ : 0 < κ) :
    QuantumNLS.RC05Statement.RephasingStatement c κ hc hκ ↔ (
  type_of% (QuantumNLS.RephasingFlow.norm_rephasing c κ hc hκ)) := Iff.rfl

end QuantumNLS.RC05Spec
#print axioms QuantumNLS.RC05Spec.global_full_transform_spec
