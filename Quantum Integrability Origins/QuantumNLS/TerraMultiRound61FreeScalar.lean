import QuantumNLS.TerraMultiRound61ScalarBridge
import QuantumNLS.TerraMultiRound43ResolventBridge

/-! The free scalar is the Fourier Poisson sum with the physical normalization. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory ComplexConjugate
open scoped InnerProductSpace
namespace QuantumNLS.TerraMultiRound61FreeScalar
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.TerraMultiRound57Collection
open QuantumNLS.TerraMultiRound38SignedPicard QuantumNLS.TerraMultiRound43ResolventBridge
open QuantumNLS.TerraMultiRound61ScalarBridge QuantumNLS.RootH1RatioOperator
open QuantumNLS.RootMassFourierR27 QuantumNLS.RootWeightedCellsR26 QuantumNLS.Fourier
open QuantumNLS.RootH1RatioStrong

variable {L : ℝ} [Fact (0 < L)]

theorem free_scalar_resolvent {a Y : ℝ} (ha : 1 / 2 < a) (hY : 0 < Y) (x : Ell2) :
    freeScalar (L := L) a x Y = inner ℂ (fieldMap L a (by linarith) x)
      (resolvent Y (fieldMap L a (by linarith) x)) := by
  simp only [freeScalar, dif_pos (abs_pos.mpr hY.ne')]
  rw [scalar_inner ha, fieldMap_signed_resolvent L (by linarith) hY]

theorem free_scalar_poisson {a Y : ℝ} (ha : 1 / 2 < a) (hY : 0 < Y) (x : Ell2) :
    Y * (freeScalar (L := L) a x Y).re =
      ∑' n : ℤ, (Y^2 / (Y^2 + momentum L n ^ 2)) *
        ‖fourierL2 L (fieldMap L a (by linarith) x) n‖ ^ 2 := by
  let u := fieldMap L a (by linarith) x
  have hi := lp.summable_inner (𝕜 := ℂ) (fourierL2 L u) (fourierL2 L (rescaled Y u))
  have hterms (n : ℤ) :
      (inner ℂ (fourierL2 L u n) (fourierL2 L (rescaled Y u) n)).re =
      (Y^2 / (Y^2 + momentum L n ^ 2)) * ‖fourierL2 L u n‖ ^ 2 := by
    rw [RCLike.inner_apply']
    change (conj (fourierL2 L u n) * fourierL2 L ((Y : ℂ) • resolvent Y u) n).re = _
    rw [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, resolvent_coeff hY]
    have ho : QuantumNLS.RootH1RatioModes.omega L n = Complex.I * (momentum L n : ℂ) := by
      unfold QuantumNLS.RootH1RatioModes.omega momentum
      push_cast
      ring
    rw [ho]
    simpa only [mul_assoc] using multiplier_real Y (momentum L n) (fourierL2 L u n)
  have hsum : (inner ℂ u (rescaled Y u)).re =
      ∑' n : ℤ, (Y^2 / (Y^2 + momentum L n ^ 2)) * ‖fourierL2 L u n‖ ^ 2 := by
    rw [← (fourierL2 L).inner_map_map, lp.inner_eq_tsum, Complex.re_tsum hi]
    exact tsum_congr hterms
  rw [free_scalar_resolvent ha hY]
  change Y * (inner ℂ u (resolvent Y u)).re = _
  rw [← hsum]
  change Y * (inner ℂ u (resolvent Y u)).re =
    (inner ℂ u ((Y : ℂ) • resolvent Y u)).re
  rw [inner_smul_right]
  simp

#print axioms free_scalar_resolvent
#print axioms free_scalar_poisson
end QuantumNLS.TerraMultiRound61FreeScalar
