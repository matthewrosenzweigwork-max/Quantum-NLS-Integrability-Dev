import QuantumNLS.CompleteAnalyticFlowR107
/-! integrator-authored trusted spec for R-7ED997C1 global:complete-analytic-flow (review record r47 PASS): headline statement(s) copied verbatim from CompleteAnalyticFlowR107 (QuantumNLS.CompleteAnalyticFlowR107). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set Metric
namespace QuantumNLS.R7EDSpec
open QuantumNLS.CompleteAnalyticFlowR107
open PhysicalTensor (L2T)
open CompleteFlowPhysicalR107
open TerraMultiRound30HessianBridge (Actions)
open ProductTorusGenerator ProductTorusFlow ProductTorusCommute ProductTorusVariational
open RootMassInvolutionR8 (mass)
variable {L κ : ℝ} [Fact (0 < L)]
local instance realNormed : NormedSpace ℝ (L2T L) := realNS
local instance realModule : Module ℝ (L2T L) := (realNS (L := L)).toModule
local instance realSMul : SMul ℝ (L2T L) := (realNS (L := L)).toSMul
local instance additiveGroup : AddCommGroup (L2T L) :=
  (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup

set_option maxHeartbeats 8000000 in
theorem complete_analytic_flow_spec (hκ : 0 < κ) (n : ℤ) :
    (∀ u : L2T L, phi (L := L) hκ n 0 u = u ∧ ∀ t,
      HasDerivAt (fun s => phi (L := L) hκ n s u)
        (SymplecticBracket.hamField (mass (L := L) hκ n) (phi (L := L) hκ n t u)) t) ∧
    (∀ p : ℝ × L2T L, AnalyticAt ℝ (fun q : ℝ × L2T L => phi (L := L) hκ n q.1 q.2) p) ∧
    (∀ t : ℝ, (∀ u, timeHomeomorph (L := L) hκ n t u = phi (L := L) hκ n t u) ∧
      (∀ u, (timeHomeomorph (L := L) hκ n t).symm u = phi (L := L) hκ n (-t) u) ∧
      AnalyticOnNhd ℝ (timeHomeomorph (L := L) hκ n t) univ ∧
      AnalyticOnNhd ℝ (timeHomeomorph (L := L) hκ n t).symm univ ∧
      ∀ u, (differentialEquiv (L := L) hκ n t u : L2T L →L[ℝ] L2T L) = fderiv ℝ (phi (L := L) hκ n t) u ∧
        ((differentialEquiv (L := L) hκ n t u).symm : L2T L →L[ℝ] L2T L) =
          fderiv ℝ (phi (L := L) hκ n (-t)) (phi (L := L) hκ n t u)) ∧
    (∀ (t : ℝ) (u h k : L2T L),
      SymplecticBracket.omega (fderiv ℝ (phi (L := L) hκ n t) u h) (fderiv ℝ (phi (L := L) hκ n t) u k) =
        SymplecticBracket.omega h k) := by
  exact QuantumNLS.CompleteAnalyticFlowR107.complete_analytic_flow hκ n

end QuantumNLS.R7EDSpec
#print axioms QuantumNLS.R7EDSpec.complete_analytic_flow_spec
