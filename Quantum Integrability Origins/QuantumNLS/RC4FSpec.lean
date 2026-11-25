import QuantumNLS.RootGBoundaryBracket
/-! integrator-authored trusted spec for R-C4F43CA8 thm:root-involution boundary brackets (Terra r161 FULL ACCEPT): headline statement(s) copied verbatim from RootGBoundaryBracket (QuantumNLS.RootGBoundaryBracket). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology Metric
namespace QuantumNLS.RC4FSpec
open QuantumNLS.RootGBoundaryBracket
open QuantumNLS.SymplecticBracket QuantumNLS.RootGBracket QuantumNLS.RootGNeighbourhood
  QuantumNLS.RootGLocal QuantumNLS.RootGFullDomain QuantumNLS.RootGReduced QuantumNLS.PhysicalTensor
  QuantumNLS.RootSymbolFrechet QuantumNLS.RootSymbolBrackets QuantumNLS.NormalizedTransfer

set_option maxHeartbeats 8000000 in
theorem reduced_bracket_zero_closed_spec (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z w : ℂ)
    (hz4 : 4 * κ ≤ z.im) (hzL : Real.log 16 ≤ L * z.im)
    (hw4 : 4 * κ ≤ w.im) (hwL : Real.log 16 ≤ L * w.im) (u0 : L2T L) (hu0 : ‖u0‖ = 1) :
    reducedC L (fun v => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z)
        (fun v => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w) u0 = 0 ∧
    reducedC L (fun v => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z)
        (fun v => conj (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w)) u0 = 0 ∧
    reducedR L (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).re)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).re) u0 = 0 ∧
    reducedR L (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).im)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).im) u0 = 0 ∧
    reducedR L (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).im)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).re) u0 = 0 ∧
    reducedR L (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).re)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).im) u0 = 0 := by
  first
  | exact QuantumNLS.RootGBoundaryBracket.reduced_bracket_zero_closed
  | (apply QuantumNLS.RootGBoundaryBracket.reduced_bracket_zero_closed <;> assumption)

end QuantumNLS.RC4FSpec
#print axioms QuantumNLS.RC4FSpec.reduced_bracket_zero_closed_spec
