import QuantumNLS.TerraMultiRound40PhysicalParity
import QuantumNLS.SmoothScalarMomentsBinding

/-! Positive signed fixed-point scalar bound to the selected quantum Cauchy
transform. Identification of the fixed point itself with the L∞ ratio is separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Complex MeasureTheory
namespace QuantumNLS.TerraMultiRound41Cauchy
open QuantumNLS.PhysicalTensor QuantumNLS.FullMass QuantumNLS.RootMeasureComplex
open QuantumNLS.CauchyUniqueness QuantumNLS.NormalizedTransfer
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.RiccatiSobolevE2 QuantumNLS.RiccatiPicardBall
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.RiccatiMonodromy
open QuantumNLS.RiccatiExpansions QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.SmoothScalarMomentsBinding QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.TerraMultiRound40ScalarParity

/-- The scalar of any sufficiently small positive fixed point is the selected
Cauchy transform. The explicit threshold is an intermediate estimate. -/
theorem positive_scalar_cauchy (L : ℝ) [hLf : Fact (0 < L)] {a Y κ : ℝ}
    (ha : 1 / 2 < a) (hY : 0 < Y) (hκ : 0 < κ) (u r : Ell2)
    (β B : ℝ) (hβ : 0 < β) (hu : ‖u‖ ≤ β)
    (hrn : ‖r‖ ≤ 2 * β / Y)
    (hr : physicalT hLf.out ha (abs_pos.mpr hY.ne') κ u r = r)
    (hB : 0 < B)
    (hm : ‖fieldMap L a (by linarith : (0 : ℝ) ≤ a) u‖ ^ 2 ≤ B)
    (hb : 2 * L * (physK L a) ^ 2 * β ^ 2 ≤ B)
    (hhigh : HighHalf L (κ * B) ((Y : ℂ) * Complex.I)) :
    CauchyUniqueness.cauchyTransform
      (Mmeas κ (fieldMap L a (by linarith : (0 : ℝ) ≤ a) u)) ((Y : ℂ) * Complex.I) =
        -Complex.I * scalar L a u r := by
  have hr' := hr
  rw [physicalT_positive hLf.out ha hY] at hr'
  have hz : 0 < (((Y : ℂ) * Complex.I).im) := by simpa using hY
  have hc := QuantumNLS.RootTraceSymbolFinal.traceSymbol_all (L := L) hκ.le
    (fieldMap L a (by linarith : (0 : ℝ) ≤ a) u) ((Y : ℂ) * Complex.I)
  have htrace : Complex.exp (Complex.I * ((Y : ℂ) * Complex.I) * (L : ℂ) / 2) *
      (Complex.exp (-(Complex.I * ((Y : ℂ) * Complex.I) * (L : ℂ) / 2) +
        (κ : ℂ) * floquetJ L a u r) +
        (Complex.exp (-(Complex.I * ((Y : ℂ) * Complex.I) * (L : ℂ) / 2) +
          (κ : ℂ) * floquetJ L a u r))⁻¹) =
      productSymbol L κ (fieldMap L a (by linarith : (0 : ℝ) ≤ a) u) ((Y : ℂ) * Complex.I) := by
    rw [QuantumNLS.RiccatiPointwiseDisc.l2_discriminant_monodromy L ha hz hκ u r hr',
      psi_floquet κ hLf.out ha] at hc
    rw [← hc, ← mul_assoc, ← Complex.exp_add]
    simp
  have hpk : 0 ≤ physK L a := physK_nonneg (by linarith)
  have hJ : ‖floquetJ L a u r‖ ≤ B / (((Y : ℂ) * Complex.I).im) := by
    have ht := QuantumNLS.RiccatiJBound.norm_J_le (f := physRep L a u)
      (r := physRep L a r) hLf.out.le (mul_nonneg hpk hβ.le)
      (fun t _ => (physRep_norm_le hLf.out ha u t).trans (mul_le_mul_of_nonneg_left hu hpk))
      (fun t _ => (physRep_norm_le hLf.out ha r t).trans (mul_le_mul_of_nonneg_left hrn hpk))
    change ‖floquetJ L a u r‖ ≤ _ at ht
    calc
      _ ≤ L * (physK L a * β * (physK L a * (2 * β / Y))) := ht
      _ = (2 * L * physK L a ^ 2 * β ^ 2) / Y := by ring
      _ ≤ B / (((Y : ℂ) * Complex.I).im) := by
        simpa using div_le_div_of_nonneg_right hb hY.le
  have hid := cauchy_eq_floquet hκ hB _ hm hhigh hz hJ htrace
  have hs : floquetJ L a u r = scalar L a u r := rfl
  rw [hs] at hid
  rw [hid]
  simp [← mul_assoc, Complex.I_mul_I]

#print axioms positive_scalar_cauchy
end QuantumNLS.TerraMultiRound41Cauchy
