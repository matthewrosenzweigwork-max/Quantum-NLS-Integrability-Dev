import QuantumNLS.FullWickFinalH15
/-! integrator-authored trusted spec for R-140AE34B thm:full-wick (final, Q06 gauge, one family): headline statement(s) copied verbatim from FullWickFinalH15 (QuantumNLS.FullWickFinalH15). -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open Filter Topology
open scoped ComplexConjugate
namespace QuantumNLS.R140Spec
open QuantumNLS.FullWickFinalH15
open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.FullWickH7 (IsNormClosePrepT)
open QuantumNLS.FullWickO1 (staticGauge)
open QuantumNLS.FullWickO2 (UR)
open QuantumNLS.WickSymbols (Sym Balanced)
open QuantumNLS.WickBounds (gensym wordSym labelsOf)
open QuantumNLS.WickSpectralBridge (evalSym)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.ReconstructionR33m (Preparation TimeBox flows RD8362E5EBInput)
open QuantumNLS.FullWickS1 (orderedWord)
open Def033HierarchyR24m (Smooth physical)
variable {H H' : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]
  [∀ N, NormedAddCommGroup (H' N)] [∀ N, NormedSpace ℂ (H' N)]

set_option maxHeartbeats 8000000 in
theorem thm_full_wick_Q06_final_spec (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) :
    FullWickH10.Stage1Clause L ∧ FullWickH10.Stage2Clause L ∧ Q06Static L κ hκ
      ∧ Q06StaticNormClose L κ hκ ∧ Q06StaticDirac L κ hκ ∧ Q06StaticWord L κ hκ
      ∧ Q06Dynamic L κ hκ ∧ Q06DynamicDirac L κ hκ ∧ Q06DynamicWord L κ hκ
      ∧ Q06StaticWordNormClose L κ hκ ∧ Q06StaticDiracNormClose L κ hκ
      ∧ Q06StaticPolyProduct L κ hκ ∧ Q06StaticPolyProductNormClose L κ hκ
      ∧ Q06DynamicPolyProduct L κ hκ := by
  first
  | exact QuantumNLS.FullWickFinalH15.thm_full_wick_Q06_final
  | (apply QuantumNLS.FullWickFinalH15.thm_full_wick_Q06_final <;> assumption)

end QuantumNLS.R140Spec
#print axioms QuantumNLS.R140Spec.thm_full_wick_Q06_final_spec
