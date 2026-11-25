import QuantumNLS.TerraMultiRound39PhysicalBall
import QuantumNLS.RootMassFourierR27

/-! The signed Fourier resolvent equals the independent physical L² resolvent
at positive height. This is an ingredient of solution identification. -/
set_option autoImplicit false
noncomputable section
open Complex
namespace QuantumNLS.TerraMultiRound43ResolventBridge
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.TerraMultiRound38SignedPicard QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.RootH1RatioOperator QuantumNLS.RootH1RatioModes
open QuantumNLS.RootMassFourierR27 QuantumNLS.Fourier

theorem fieldMap_signed_resolvent (L : ℝ) [Fact (0 < L)] {a Y : ℝ}
    (ha : 0 ≤ a) (hY : 0 < Y) (x : Ell2) :
    fieldMap L a ha (signedCLM L Y (abs_pos.mpr hY.ne') x) =
      resolvent Y (fieldMap L a ha x) := by
  apply (fourierL2 L).injective
  apply lp.ext
  funext k
  rw [resolvent_coeff hY, fourierL2_apply, fourierL2_apply,
    coeff_fieldMap, coeff_fieldMap]
  have ho : omega L k = Complex.I * (QuantumNLS.RiccatiSobolevE1.freq L k : ℂ) := by
    unfold omega QuantumNLS.RiccatiSobolevE1.freq
    push_cast
    ring
  rw [ho]
  change (x k / ((Y : ℂ) + Complex.I * (QuantumNLS.RiccatiSobolevE1.freq L k : ℂ))) /
      ((pw L a k : ℝ) : ℂ) =
    ((Y : ℂ) + Complex.I * (QuantumNLS.RiccatiSobolevE1.freq L k : ℂ))⁻¹ *
      (x k / ((pw L a k : ℝ) : ℂ))
  ring

#print axioms fieldMap_signed_resolvent
end QuantumNLS.TerraMultiRound43ResolventBridge
