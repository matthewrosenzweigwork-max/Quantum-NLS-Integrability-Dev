import QuantumNLS.RootH1Positive
/-! integrator-authored trusted spec for R-F36DAC7F lem:root-H1-positive (review record r43 PASS): headline statement(s) copied verbatim from RootH1Positive (QuantumNLS.RootH1Positive). -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open QuantumNLS.PhysicalTensor QuantumNLS.HaarResolvent
  QuantumNLS.RootH1RatioConvergence QuantumNLS.RootH1PositiveData
  QuantumNLS.RootH1PositiveAlgebra QuantumNLS.RootH1PositiveIntegrals
  QuantumNLS.RootH1PositiveSpectral QuantumNLS.RootH1PositiveEnergy
namespace QuantumNLS.RF36Spec
open QuantumNLS.RootH1Positive
variable {L : ℝ} [hLf : Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_H1_positive_spec {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0) :
    (∀ Y : ℝ, threshold κ u ≤ Y →
      ∃ g d : ℝ → ℂ,
        IsH1Rep L (ratioAt hκ.le u Y) g d ∧ g L = g 0 ∧
        (∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt g (d t) t) ∧
        (let s := fun t => ‖g t‖^2
         let a := fun t => (d t+(κ:ℂ)*(g t)^2*conj (d t))/((1-κ^2*(s t)^2:ℝ):ℂ)
         (∀ t ∈ Icc (0:ℝ) L, 3/4 ≤ 1-κ*s t ∧ 15/16 ≤ 1-κ^2*(s t)^2) ∧
         (∫ t : ℝ, Y^2*t^2/(Y^2+t^2) ∂(FullMass.Mmeas κ u)) =
           Y^2*(∫ t in (0:ℝ)..L, ‖a t‖^2)+κ*Y^4*(∫ t in (0:ℝ)..L, (s t)^2/(1-κ*s t)^2) ∧
         (∫ t in (0:ℝ)..L, ‖(Y:ℂ)*d t‖^2) ≤
           (1+κ*‖ratioInfAt hκ.le u Y‖^2)^2*
             (∫ t : ℝ, Y^2*t^2/(Y^2+t^2) ∂(FullMass.Mmeas κ u)))) ∧
    Tendsto (fun Y : ℝ => κ*‖ratioInfAt hκ.le u Y‖^2) atTop (nhds 0) := by
  exact QuantumNLS.RootH1Positive.root_H1_positive hκ u hu

end QuantumNLS.RF36Spec
#print axioms QuantumNLS.RF36Spec.root_H1_positive_spec
