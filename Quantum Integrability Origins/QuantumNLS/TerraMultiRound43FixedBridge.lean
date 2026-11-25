import QuantumNLS.TerraMultiRound43ResolventBridge
import QuantumNLS.TerraMultiRound43ProductBridge
import QuantumNLS.RootH1RatioBounds

/-! Equality of the Fourier and physical nonlinear fixed-point maps at
positive height, on almost-everywhere matching representatives. -/
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
namespace QuantumNLS.TerraMultiRound43FixedBridge
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.TerraMultiRound38SignedPicard QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.TerraMultiRound39AlgebraBall
open QuantumNLS.TerraMultiRound43ResolventBridge QuantumNLS.TerraMultiRound43ProductBridge
open QuantumNLS.RootH1RatioOperator QuantumNLS.RootH1RatioNonlinear

lemma physical_cubic_scale {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (u r : Ell2) :
    physicalProduct hL ha (jEll u) (physicalProduct hL ha r r) =
      ((L : ℂ)⁻¹) • mulBil hL ha (jEll u) (mulBil hL ha r r) := by
  have hs : (((Real.sqrt L : ℝ) : ℂ) ^ 2) = (L : ℂ) := by
    exact_mod_cast Real.sq_sqrt hL.le
  have hi : (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) = (L : ℂ)⁻¹ := by
    rw [Complex.ofReal_inv, ← pow_two, inv_pow, hs]
  unfold physicalProduct
  rw [map_smul, smul_smul, hi]

/-- The signed map and ratio map have the same physical L² output. -/
theorem fieldMap_physicalT (L : ℝ) [hLf : Fact (0 < L)] {a Y : ℝ}
    (ha : 1 / 2 < a) (hY : 0 < Y) (κ : ℝ) (u r : Ell2) (s : Linfty L)
    (hs : s =ᵐ[volume] fieldMap L a (by linarith : (0 : ℝ) ≤ a) r) :
    fieldMap L a (by linarith : (0 : ℝ) ≤ a)
        (physicalT hLf.out ha (abs_pos.mpr hY.ne') κ u r) =
      resolvent Y (forcing κ (fieldMap L a (by linarith : (0 : ℝ) ≤ a) u) s) := by
  have hq : (κ : ℂ) • physicalProduct hLf.out ha (jEll u) (physicalProduct hLf.out ha r r) =
      ((κ / L : ℝ) : ℂ) • mulBil hLf.out ha (jEll u) (mulBil hLf.out ha r r) := by
    rw [physical_cubic_scale, smul_smul]
    congr 1
    push_cast
    ring
  unfold physicalT signedT forcing
  rw [← map_smul, ← hq, ← map_sub, fieldMap_signed_resolvent L (by linarith) hY]
  rw [map_sub, map_smul, fieldMap_cubic L ha u r s hs]

#print axioms physical_cubic_scale
#print axioms fieldMap_physicalT
end QuantumNLS.TerraMultiRound43FixedBridge
