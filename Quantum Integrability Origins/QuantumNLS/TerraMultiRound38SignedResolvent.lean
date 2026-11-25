import QuantumNLS.RiccatiSobolevE1

/-! Signed Fourier resolvent estimate for REG-005. This is a supporting result,
not the signed fixed point, parity identity, or full lemma. -/
set_option autoImplicit false
noncomputable section
open Complex
namespace QuantumNLS.TerraMultiRound38SignedResolvent
open QuantumNLS.RiccatiSobolevE1

/-- The Fourier multiplier of `(Y + ∂ₓ)⁻¹`, defined for both signs of `Y`. -/
def signedResolvent (L Y : ℝ) (c : ℤ → ℂ) : ℤ → ℂ :=
  fun k => c k / ((Y : ℂ) + Complex.I * (freq L k : ℂ))

/-- The signed multiplier has the same norm bound on either side of zero. -/
theorem signed_multiplier_bound (Y p : ℝ) (hY : Y ≠ 0) (c : ℂ) :
    ‖c / ((Y : ℂ) + Complex.I * (p : ℂ))‖ ≤ |Y|⁻¹ * ‖c‖ := by
  have hp : 0 < |Y| := abs_pos.mpr hY
  have hw : |Y| ≤ ‖((Y : ℂ) + Complex.I * (p : ℂ))‖ := by
    have h := Complex.abs_re_le_norm ((Y : ℂ) + Complex.I * (p : ℂ))
    simpa using h
  rw [norm_div]
  calc ‖c‖ / ‖((Y : ℂ) + Complex.I * (p : ℂ))‖ ≤ ‖c‖ / |Y| :=
    div_le_div_of_nonneg_left (norm_nonneg c) hp hw
    _ = |Y|⁻¹ * ‖c‖ := by rw [div_eq_inv_mul]

/-- Signed `H^a` squared bound for every real order and every coefficient sequence. -/
theorem signed_resolvent_hsq_bound (L a Y : ℝ) (hY : Y ≠ 0) (c : ℤ → ℂ) :
    hsq L a (signedResolvent L Y c) ≤ ENNReal.ofReal (|Y|⁻¹ ^ 2) * hsq L a c := by
  unfold hsq
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hn := signed_multiplier_bound Y (freq L k) hY (c k)
  have hn2 : ‖signedResolvent L Y c k‖ ^ 2 ≤ |Y|⁻¹ ^ 2 * ‖c k‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg (signedResolvent L Y c k)) hn 2
    rw [mul_pow] at hh
    exact hh
  calc wt L a k * ‖signedResolvent L Y c k‖ ^ 2
      ≤ wt L a k * (|Y|⁻¹ ^ 2 * ‖c k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hn2 (wt_nonneg L a k)
    _ = |Y|⁻¹ ^ 2 * (wt L a k * ‖c k‖ ^ 2) := by ring


/-- The resolvent gains one derivative for either sign when `|Y| ≥ 1`. -/
theorem signed_resolvent_gain (L a Y : ℝ) (hY : 1 ≤ |Y|) (c : ℤ → ℂ) :
    hsq L (a + 1) (signedResolvent L Y c) ≤ ENNReal.ofReal 4 * hsq L a c := by
  unfold hsq
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  let p := freq L k
  let d : ℂ := (Y : ℂ) + Complex.I * (p : ℂ)
  have hdY : |Y| ≤ ‖d‖ := by
    have h := Complex.abs_re_le_norm d
    simpa [d] using h
  have hdp : |p| ≤ ‖d‖ := by
    have h := Complex.abs_im_le_norm d
    simpa [d] using h
  have hd : 0 < ‖d‖ := by linarith
  have hratio : (1 + |p|) / ‖d‖ ≤ 2 := by
    apply (div_le_iff₀ hd).2
    linarith
  have hh : (1 + |p|) * ‖signedResolvent L Y c k‖ ≤ 2 * ‖c k‖ := by
    change (1 + |p|) * ‖c k / d‖ ≤ 2 * ‖c k‖
    rw [norm_div]
    calc (1 + |p|) * (‖c k‖ / ‖d‖) = ((1 + |p|) / ‖d‖) * ‖c k‖ := by ring
      _ ≤ 2 * ‖c k‖ := mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
  have hh2 := pow_le_pow_left₀ (mul_nonneg (by positivity : 0 ≤ 1 + |p|)
    (norm_nonneg (signedResolvent L Y c k))) hh 2
  rw [mul_pow, mul_pow] at hh2
  have hw : wt L (a + 1) k = wt L a k * (1 + |p|) ^ 2 := by
    unfold wt
    change (1 + |p|) ^ (2 * (a + 1)) = (1 + |p|) ^ (2 * a) * (1 + |p|) ^ 2
    rw [show 2 * (a + 1) = 2 * a + 2 by ring, Real.rpow_add (by positivity)]
    rw [Real.rpow_two]
  rw [hw]
  have hh3 := mul_le_mul_of_nonneg_left hh2 (wt_nonneg L a k)
  nlinarith only [hh3]

end QuantumNLS.TerraMultiRound38SignedResolvent
#print axioms QuantumNLS.TerraMultiRound38SignedResolvent.signed_multiplier_bound
#print axioms QuantumNLS.TerraMultiRound38SignedResolvent.signed_resolvent_hsq_bound
#print axioms QuantumNLS.TerraMultiRound38SignedResolvent.signed_resolvent_gain
