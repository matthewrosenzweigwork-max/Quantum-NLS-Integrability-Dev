import QuantumNLS.LOCAL017SourceBetaR19
import QuantumNLS.LOCAL017HaarPrimitive

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.LOCAL017SourceR19
open Ext025A4BanachComplexification

/-- Native data derived from S; no holomorphic-extension or bridge input. -/
structure NativeExtension (S : ResetMoser.Hyp) where
  radius : ℝ
  realConstant : ℝ
  complexConstant : ℝ
  loc : ResetMoser.Loc S radius realConstant
  constant_nonneg : 0 ≤ complexConstant
  form : CH → CForm
  holomorphic : DifferentiableOn ℂ (radialBeta form) (ball 0 radius)
  cubic : ∀ z ∈ ball (0 : CH) radius, ‖radialBeta form z‖ ≤ complexConstant * ‖z‖^3
  real_slice : ∀ z ∈ ball (0 : H) radius, ∀ h,
    radialBeta form (Cx.ι z) (Cx.ι h) = (ResetMoser.betaR S z h : ℂ)

theorem exists_nativeExtension (S : ResetMoser.Hyp) : Nonempty (NativeExtension S) := by
  obtain ⟨R, M, C, hL, hC, G, hg, hb, he⟩ := source_beta_extension S
  exact ⟨⟨R, M, C, hL, hC, G, hg, hb, he⟩⟩

def nativeExtension (S : ResetMoser.Hyp) : NativeExtension S :=
  Classical.choice (exists_nativeExtension S)

/-- The exact accepted Terra r174 bridge, specialized to the common CH. -/
theorem acceptedBridge : GP05CauchyMajorantsR14.BanachHolomorphicBridge CH CCov :=
  GP05AcceptedBridgeR16.banachHolomorphicBridge

/-- The round-18 canonical data are instantiated with the native radial
integral and the accepted named bridge, both constructed without premises. -/
def nativeData (S : ResetMoser.Hyp) : LOCAL017Haar.ComplexData (E := CH)
    (ResetMoser.betaR S) (nativeExtension S).radius (nativeExtension S).complexConstant :=
  LOCAL017Haar.canonicalData (ResetMoser.betaR S) (radialBeta (nativeExtension S).form)
    (nativeExtension S).real_slice (nativeExtension S).holomorphic
    (nativeExtension S).cubic acceptedBridge

/-- The only remaining stage input: the earlier finite-torus periodic
potential. This is item 2 and contains no averaged differential conclusion. -/
def ItemTwoPotential (S : ResetMoser.Hyp) : Prop :=
  ∀ z ∈ ball (0 : H) (nativeExtension S).radius, {n | z n ≠ 0}.Finite →
    Nonempty (LOCAL017Haar.OrbitPotential (ResetMoser.betaR S) z)

/-- Native reset-moser hann, conditional only on the item-2 potential. -/
theorem reset_moser_hann (S : ResetMoser.Hyp) (hpot : ItemTwoPotential S) :
    ContinuousOn (LOCAL017Haar.beta0 (ResetMoser.betaR S))
      (ball 0 (nativeExtension S).radius) ∧
    (∀ z ∈ ball (0 : H) (nativeExtension S).radius, ∀ h ∈ ResetMoser.Tz z,
      (ResetMoser.betaR S z - fderiv ℝ (LOCAL017Haar.primitive (ResetMoser.betaR S)) z) h = 0) :=
  LOCAL017Haar.reset_moser_hann S (nativeExtension S).loc (nativeData S)
    (nativeExtension S).constant_nonneg hpot

/-- The scalar, first, and second full operator estimates and hann now have
only the same single source-stage input. -/
theorem primitive_with_bounds (S : ResetMoser.Hyp) (hpot : ItemTwoPotential S) :
    let N := nativeExtension S
    AnalyticOnNhd ℝ (LOCAL017Haar.primitive (ResetMoser.betaR S)) (ball 0 N.radius) ∧
    ContinuousOn (LOCAL017Haar.beta0 (ResetMoser.betaR S)) (ball 0 N.radius) ∧
    (∀ z ∈ ball (0 : H) (N.radius/2),
      |LOCAL017Haar.primitive (ResetMoser.betaR S) z| ≤ N.realConstant * Real.pi * ‖z‖^4 ∧
      ‖fderiv ℝ (LOCAL017Haar.primitive (ResetMoser.betaR S)) z‖ ≤
        64 * N.complexConstant * Real.pi * ‖z‖^3 ∧
      ‖iteratedFDeriv ℝ 2 (LOCAL017Haar.primitive (ResetMoser.betaR S)) z‖ ≤
        576 * N.complexConstant * Real.pi * ‖z‖^2 ∧
      ‖LOCAL017Haar.beta0 (ResetMoser.betaR S) z‖ ≤
        (N.realConstant + 64 * N.complexConstant * Real.pi) * ‖z‖^3) ∧
    (∀ z ∈ ball (0 : H) N.radius, ∀ h ∈ ResetMoser.Tz z,
      LOCAL017Haar.beta0 (ResetMoser.betaR S) z h = 0) :=
  LOCAL017Haar.primitive_with_bounds (nativeData S) (nativeExtension S).loc.ρpos
    (nativeExtension S).constant_nonneg
    (fun _ hz => (ResetMoser.betaR_hasFDerivAt S (nativeExtension S).loc hz).continuousAt.continuousWithinAt)
    (fun _ hz => ResetMoser.norm_betaR_le S (nativeExtension S).loc hz) hpot

end QuantumNLS.LOCAL017SourceR19
