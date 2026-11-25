import QuantumNLS.Q07GradientRemovalR24
/-! integrator-authored trusted spec for R-C5645D32 prop:Q07Bgradientremoval (terra_review r194/r195 PASS): headline statement(s) copied verbatim from Q07GradientRemovalR24 (QuantumNLS.Q07GradientRemovalR24). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open Set Metric Filter Topology
namespace QuantumNLS.RC56Spec
open QuantumNLS.Q07GradientRemovalR24
open RiccatiSobolevBanach Q07TailBindingR24 Q07SobolevModelR24 Q07RealCalculusR24
open Q07ChargeLevelsR24 ClassicalCharges SmoothScalarMomentsPhysical
open ComplexifiedSobolevField RiccatiPointwiseDisc PROP017UniformN
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem prop_Q07Bgradientremoval_spec (hκ : 0 < κ) (r : ℕ) (_hr : 2 ≤ r)
    (B : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l →
      (∀ u : Sobolev.H02 L (regularity r), ‖u‖ ≤ B → DifferentiableAt ℝ (T (L := L) hκ r h l) u) ∧
      sSup ((fun u : Sobolev.H02 L (regularity r) => ‖fderiv ℝ (T (L := L) hκ r h l) u‖) '' smoothBall (L := L) r B)
        ≤ C*(cutSeq L l)^(-(1/2 : ℝ)) := by
  exact QuantumNLS.Q07GradientRemovalR24.«prop:Q07Bgradientremoval» hκ r _hr B hh
end QuantumNLS.RC56Spec
#print axioms QuantumNLS.RC56Spec.prop_Q07Bgradientremoval_spec
