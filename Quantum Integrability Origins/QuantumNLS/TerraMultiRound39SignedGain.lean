import QuantumNLS.TerraMultiRound39PhysicalBall

/-! One-order gain for signed physical fixed points in the exact weighted
Fourier Sobolev model. -/
set_option autoImplicit false
noncomputable section
open Complex
namespace QuantumNLS.TerraMultiRound39SignedGain
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.TerraMultiRound38SignedResolvent QuantumNLS.TerraMultiRound38SignedPicard
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.ComplexifiedSobolevField

theorem toField_signedCLM (L a Y : ℝ) (hY : 0 < |Y|) (x : Ell2) :
    toField L a (signedCLM L Y hY x) = signedResolvent L Y (toField L a x) := by
  funext k
  change (x k / ((Y : ℂ) + Complex.I * (freq L k : ℂ))) /
      ((pw L a k : ℝ) : ℂ) =
    (x k / ((pw L a k : ℝ) : ℂ)) / ((Y : ℂ) + Complex.I * (freq L k : ℂ))
  simp only [div_eq_mul_inv]
  ring

/-- Every signed fixed point has one more Fourier Sobolev order. -/
theorem physical_fixed_gain {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (hY1 : 1 ≤ |Y|) (κ : ℝ) (u r : Ell2)
    (hr : physicalT hL ha hY κ u r = r) :
    hsq L (a + 1) (toField L a r) ≠ ⊤ := by
  let f : Ell2 := u - ((κ / L : ℝ) : ℂ) • mulBil hL ha (jEll u) (mulBil hL ha r r)
  have he : r = signedCLM L Y hY f := by
    rw [← hr]
    simp only [physicalT, signedT, f, map_sub, map_smul]
  rw [he, toField_signedCLM]
  apply ne_top_of_le_ne_top _ (signed_resolvent_gain L a Y hY1 (toField L a f))
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hsq_toField_ne_top L a f)

end QuantumNLS.TerraMultiRound39SignedGain
#print axioms QuantumNLS.TerraMultiRound39SignedGain.toField_signedCLM
#print axioms QuantumNLS.TerraMultiRound39SignedGain.physical_fixed_gain
