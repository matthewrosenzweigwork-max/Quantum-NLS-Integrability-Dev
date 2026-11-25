import Mathlib
import QuantumNLS.RiccatiGlobal
import QuantumNLS.RiccatiExpV

/-!
# R-3FEAD88B stage (c-iii), value part: uniform-in-parameter value bounds on the globalized branch

Frozen inputs (read only): `RiccatiExpansions.expansion_a` (bottom-level remainder),
`RiccatiExpansions.{modeCoef, logS, physRep_norm_le, physK_nonneg}`,
`RiccatiExpV.exp_logS_eq_cxDisc_and_bound` (the exp-identity, log bound, exponential tail),
`RiccatiChargeIdent.Wc` (definitionally `wAbs` at `(κ/L)`), and `RiccatiGlobal` (stage c-i/c-ii).

Content (all statements with `κ > 0` physical, model coupling `κ / L`, `r = rfG` the globalized
fixed point at uniqueness radius `βu`, expansion radius `B < βu`):
* `value_remainder`: `‖rfG p − r_M(coeffs p)(1/z)‖ ≤ remC · |z|^{-(M+1)}`;
* `logTrace_eq_logS`: the principal log of the discriminant equals `logS` on the sector;
* `log_value`: `‖log(disc) − i κ Σ_{n=1}^M I_n z^{-n}‖ ≤ logC · |z|^{-(M+1)}`;
* `trace_near_one`: `‖e^{izL/2} cxDisc − 1‖ ≤ 1/2`.
The derivative (C1 / fderiv) fields are NOT here; see the report of this stage.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex

namespace QuantumNLS.RiccatiValueBounds

open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPicardBall QuantumNLS.RiccatiChargeLevels
open QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiRemainder QuantumNLS.RiccatiGlobal
open QuantumNLS.RiccatiExpV QuantumNLS.ComplexifiedSobolevField QuantumNLS.RiccatiPointwiseDisc

/-- Floquet integral bound `|modeCoef f w| ≤ L · (physK ‖f‖)(physK ‖w‖)`. -/
theorem norm_modeCoef_le {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (f w : Ell2) :
    ‖modeCoef L a f w‖ ≤ L * ((physK L a * ‖f‖) * (physK L a * ‖w‖)) := by
  unfold modeCoef
  have hC : ∀ s ∈ Set.uIoc 0 L,
      ‖(fun s => physRep L a f s * physRep L a w s) s‖
        ≤ (physK L a * ‖f‖) * (physK L a * ‖w‖) := by
    intro s _
    show ‖physRep L a f s * physRep L a w s‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (physRep_norm_le hL ha f s) (physRep_norm_le hL ha w s) (norm_nonneg _)
      (mul_nonneg (physK_nonneg (by linarith)) (norm_nonneg _))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hC
  rw [sub_zero, abs_of_pos hL] at h
  exact h.trans (le_of_eq (by ring))

/-- `1 + e ≠ 0` when `‖e‖ ≤ 1/2`. -/
theorem one_add_ne_zero_of_norm_le {e : ℂ} (he : ‖e‖ ≤ 1 / 2) : 1 + e ≠ 0 := by
  intro h
  have he' : e = -1 := by linear_combination h
  rw [he'] at he
  norm_num at he

/-- `0 ≤ Re(1 + e)` when `‖e‖ ≤ 1/2`. -/
theorem re_one_add_nonneg {e : ℂ} (he : ‖e‖ ≤ 1 / 2) : 0 ≤ (1 + e).re := by
  have h := (abs_le.mp (Complex.abs_re_le_norm e)).1
  simp only [Complex.add_re, Complex.one_re]
  linarith

/-- Exponential identity: `exp(logS J) = exp(κJ)(1+e)` with `e = exp(izL − 2κJ)`. -/
theorem exp_logS_factor (L κ : ℝ) (z J : ℂ) (he : ‖Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)‖ ≤ 1 / 2) :
    Complex.exp (logS L κ z J)
      = Complex.exp ((κ : ℂ) * J) * (1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)) := by
  unfold logS
  rw [Complex.exp_add, Complex.exp_log (one_add_ne_zero_of_norm_le he)]

/-- The principal log of `exp(izL/2) · cxDisc` equals `logS` on the sector: the imaginary part of
`logS` lies in `(-π, π]` when `|κ Im J| ≤ 1`. -/
theorem logTrace_eq_logS {a S : ℝ} {M : ℕ} {L : ℝ} (hL : 0 < L) [Fact (0 < L)] (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (hκ : 0 < κ) (u v : Ell2) (β : ℝ)
    (hβ : 0 < β) (hu : ‖u‖ ≤ β) (hv : ‖v‖ ≤ β)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 0 < z.im) (hsec : δ * ‖z‖ ≤ z.im)
    (hR : logR L a S M κ β δ ≤ ‖z‖)
    (r : Ell2) (hr : riccatiT hL ha hz (κ / L) (lowT L a S u) (lowT L a S v) r = r)
    (hrn : ‖r‖ ≤ 2 * β / z.im)
    (hJ : κ * ‖modeCoef L a (lowT L a S v) r‖ ≤ 1) :
    Complex.log (Complex.exp (Complex.I * z * (L : ℂ) / 2)
        * QuantumNLS.ComplexifiedDiscriminant.cxDisc κ
          (fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S u))
          (fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S v)) z)
      = logS L κ z (modeCoef L a (lowT L a S v) r) := by
  haveI : Fact (0 < L) := ⟨hL⟩
  obtain ⟨h1, -, h3⟩ := exp_logS_eq_cxDisc_and_bound L hL ha haS hM κ hκ u v β hβ hu hv D hD δ hδ z
    hz hsec hR r hr hrn
  rw [← h1]
  set J := modeCoef L a (lowT L a S v) r with hJdef
  set e := Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J) with hedef
  have hre : 0 ≤ (1 + e).re := re_one_add_nonneg h3
  have harg : |Complex.arg (1 + e)| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hre
  have him : (logS L κ z J).im = (κ : ℝ) * J.im + Complex.arg (1 + e) := by
    unfold logS
    rw [Complex.add_im, Complex.log_im]
    simp [hedef]
  have hJim : |(κ : ℝ) * J.im| ≤ 1 := by
    rw [abs_mul, abs_of_pos hκ]
    have hi : |J.im| ≤ ‖J‖ := Complex.abs_im_le_norm J
    have hJn : κ * ‖J‖ ≤ 1 := hJ
    nlinarith [abs_nonneg J.im]
  have hpi := Real.pi_gt_three
  have hlow : -Real.pi < (logS L κ z J).im := by
    rw [him]
    have := (abs_le.mp hJim).1
    have := (abs_le.mp harg).1
    linarith
  have hhigh : (logS L κ z J).im ≤ Real.pi := by
    rw [him]
    have := (abs_le.mp hJim).2
    have := (abs_le.mp harg).2
    linarith
  exact Complex.log_exp hlow hhigh

/-- Value bound for the globalized fixed point against the truncated Riccati sum at radius `B`. -/
theorem value_remainder {a S : ℝ} {M : ℕ} {L : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) {B βu : ℝ} (hB : 0 < B) (hBu : B < βu)
    (hβu : 0 < βu) (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (δ : ℝ) (hδ : 0 < δ) {z : ℂ} (hz : 0 < z.im) (hsec : δ * ‖z‖ ≤ z.im)
    (hR : remR L a S M (κ / L) B δ ≤ ‖z‖)
    (hκ : 16 * |κ / L| * Cmul L a ^ 2 * βu ^ 2 ≤ z.im ^ 2)
    {p : Ell2 × Ell2} (h1 : ‖p.1‖ ≤ B) (h2 : ‖p.2‖ ≤ B) :
    ‖rfG hL ha S (κ / L) βu hβu z p
        - rMsum (wAbs (mulLin hL ha) D (lowT L a S p.2) (lowT L a S p.1) ((κ / L : ℝ) : ℂ)) (z⁻¹) M‖
      ≤ remC L a S M (κ / L) B δ * (‖z‖ ^ (M + 1))⁻¹ := by
  obtain ⟨hfix, hnorm⟩ := rfG_small_radius (S := S) hL ha hβu hz hκ hB hBu h1 h2
  exact (expansion_a L hL ha haS hM (κ / L) p.1 p.2 B hB h1 h2 D hD δ hδ z hz hsec hR).2
    _ hfix hnorm

/-- Value bound of the principal log of the discriminant against the truncated expansion. -/
theorem log_value {a S : ℝ} {M : ℕ} {L : ℝ} (hL : 0 < L) [Fact (0 < L)] (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (hκ0 : 0 < κ) {B βu : ℝ} (hB : 0 < B)
    (hBu : B < βu) (hβu : 0 < βu) (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (δ : ℝ) (hδ : 0 < δ) {z : ℂ} (hz : 0 < z.im) (hsec : δ * ‖z‖ ≤ z.im)
    (hR : logR L a S M κ B δ ≤ ‖z‖)
    (hκ : 16 * |κ / L| * Cmul L a ^ 2 * βu ^ 2 ≤ z.im ^ 2)
    (hJ : κ * (L * ((physK L a * B) * (physK L a * (2 * B / z.im)))) ≤ 1 / 8)
    {p : Ell2 × Ell2} (h1 : ‖p.1‖ ≤ B) (h2 : ‖p.2‖ ≤ B) :
    Complex.log (Complex.exp (Complex.I * z * (L : ℂ) / 2)
        * QuantumNLS.ComplexifiedDiscriminant.cxDisc κ
          (fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S p.1))
          (fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S p.2)) z)
      = logS L κ z (modeCoef L a (lowT L a S p.2)
          (rfG hL ha S (κ / L) βu hβu z p)) ∧
    ‖Complex.log (Complex.exp (Complex.I * z * (L : ℂ) / 2)
        * QuantumNLS.ComplexifiedDiscriminant.cxDisc κ
          (fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S p.1))
          (fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S p.2)) z)
        - Complex.I * (κ : ℂ) * ∑ n ∈ Finset.Icc 1 M,
            modeCoef L a (lowT L a S p.2)
              (wAbs (mulLin hL ha) D (lowT L a S p.2) (lowT L a S p.1) ((κ / L : ℝ) : ℂ) n)
              * (z⁻¹) ^ n‖
      ≤ logC L a S M κ B δ * (‖z‖ ^ (M + 1))⁻¹ := by
  haveI : Fact (0 < L) := ⟨hL⟩
  obtain ⟨hfix, hnorm⟩ := rfG_small_radius (S := S) hL ha hβu hz hκ hB hBu h1 h2
  have hJbound : ‖modeCoef L a (lowT L a S p.2) (rfG hL ha S (κ / L) βu hβu z p)‖
      ≤ L * ((physK L a * B) * (physK L a * (2 * B / z.im))) := by
    refine (norm_modeCoef_le hL ha _ _).trans ?_
    apply mul_le_mul_of_nonneg_left _ hL.le
    apply mul_le_mul _ _ (mul_nonneg (physK_nonneg (by linarith)) (norm_nonneg _))
      (mul_nonneg (physK_nonneg (by linarith)) hB.le)
    · exact mul_le_mul_of_nonneg_left (norm_lowT_le L a S p.2 |>.trans h2)
        (physK_nonneg (by linarith))
    · exact mul_le_mul_of_nonneg_left hnorm (physK_nonneg (by linarith))
  have hJ' : κ * ‖modeCoef L a (lowT L a S p.2) (rfG hL ha S (κ / L) βu hβu z p)‖ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hJbound hκ0.le
    have h8 : κ * (L * ((physK L a * B) * (physK L a * (2 * B / z.im)))) ≤ 1 := by linarith
    exact this.trans h8
  have hlog := logTrace_eq_logS hL ha haS hM κ hκ0 p.1 p.2 B hB h1 h2 D hD δ hδ z hz hsec hR
    (rfG hL ha S (κ / L) βu hβu z p) hfix hnorm hJ'
  refine ⟨hlog, ?_⟩
  have hb := (exp_logS_eq_cxDisc_and_bound L hL ha haS hM κ hκ0 p.1 p.2 B hB h1 h2 D hD δ hδ z hz
    hsec hR (rfG hL ha S (κ / L) βu hβu z p) hfix hnorm).2.1
  rw [hlog]
  have e : Complex.I * (κ : ℂ) * ∑ n ∈ Finset.Icc 1 M,
        modeCoef L a (lowT L a S p.2)
          (wAbs (mulLin hL ha) D (lowT L a S p.2) (lowT L a S p.1) ((κ / L : ℝ) : ℂ) n)
          * (z⁻¹) ^ n
      = (κ : ℂ) * (Complex.I * ∑ n ∈ Finset.Icc 1 M,
        modeCoef L a (lowT L a S p.2)
          (wAbs (mulLin hL ha) D (lowT L a S p.2) (lowT L a S p.1) ((κ / L : ℝ) : ℂ) n)
          * (z⁻¹) ^ n) := by ring
  rw [e]
  exact hb

/-- Trace estimate `‖e^{izL/2} cxDisc − 1‖ ≤ 1/2` on the sector (the factorisation
`e^{logS} = e^{κJ}(1+e)` with `‖e‖ ≤ 1/8` and `|κJ| ≤ 1/8`). -/
theorem trace_near_one_bound {a S : ℝ} {M : ℕ} {L : ℝ} (hL : 0 < L) [Fact (0 < L)] (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (hκ0 : 0 < κ) {B βu : ℝ} (hB : 0 < B)
    (hBu : B < βu) (hβu : 0 < βu) (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (δ : ℝ) (hδ : 0 < δ) {z : ℂ} (hz : 0 < z.im) (hsec : δ * ‖z‖ ≤ z.im)
    (hR : logR L a S M κ B δ ≤ ‖z‖)
    (hκ : 16 * |κ / L| * Cmul L a ^ 2 * βu ^ 2 ≤ z.im ^ 2)
    (hJ : κ * (L * ((physK L a * B) * (physK L a * (2 * B / z.im)))) ≤ 1 / 8)
    (hLIm : 8 + 1 / 4 ≤ L * z.im)
    {p : Ell2 × Ell2} (h1 : ‖p.1‖ ≤ B) (h2 : ‖p.2‖ ≤ B) :
    ‖Complex.exp (Complex.I * z * (L : ℂ) / 2)
        * QuantumNLS.ComplexifiedDiscriminant.cxDisc κ
          (fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S p.1))
          (fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S p.2)) z - 1‖ ≤ 1 / 2 := by
  haveI : Fact (0 < L) := ⟨hL⟩
  obtain ⟨hfix, hnorm⟩ := rfG_small_radius (S := S) hL ha hβu hz hκ hB hBu h1 h2
  have hJbound : ‖modeCoef L a (lowT L a S p.2) (rfG hL ha S (κ / L) βu hβu z p)‖
      ≤ L * ((physK L a * B) * (physK L a * (2 * B / z.im))) := by
    refine (norm_modeCoef_le hL ha _ _).trans ?_
    apply mul_le_mul_of_nonneg_left _ hL.le
    apply mul_le_mul _ _ (mul_nonneg (physK_nonneg (by linarith)) (norm_nonneg _))
      (mul_nonneg (physK_nonneg (by linarith)) hB.le)
    · exact mul_le_mul_of_nonneg_left ((norm_lowT_le L a S p.2).trans h2)
        (physK_nonneg (by linarith))
    · exact mul_le_mul_of_nonneg_left hnorm (physK_nonneg (by linarith))
  set J := modeCoef L a (lowT L a S p.2) (rfG hL ha S (κ / L) βu hβu z p) with hJdef
  have hκJ : ‖(κ : ℂ) * J‖ ≤ 1 / 8 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0.le]
    have := mul_le_mul_of_nonneg_left hJbound hκ0.le
    linarith
  obtain ⟨h1', -, h3⟩ := exp_logS_eq_cxDisc_and_bound L hL ha haS hM κ hκ0 p.1 p.2 B hB h1 h2 D hD δ
    hδ z hz hsec hR (rfG hL ha S (κ / L) βu hβu z p) hfix hnorm
  set e := Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J) with hedef
  have hEq : Complex.exp (Complex.I * z * (L : ℂ) / 2)
        * QuantumNLS.ComplexifiedDiscriminant.cxDisc κ
          (fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S p.1))
          (fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S p.2)) z
      = Complex.exp ((κ : ℂ) * J) * (1 + e) := by
    rw [← h1', exp_logS_factor L κ z J h3]
  have hexp1 : ‖Complex.exp ((κ : ℂ) * J) - 1‖ ≤ 2 * ‖(κ : ℂ) * J‖ :=
    Complex.norm_exp_sub_one_le (by linarith)
  have hexp2 : ‖Complex.exp ((κ : ℂ) * J)‖ ≤ 5 / 4 := by
    have := norm_sub_norm_le (Complex.exp ((κ : ℂ) * J)) 1
    rw [norm_one] at this
    linarith
  have hre : Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)
      = Complex.exp (Complex.I * z * (L : ℂ) - 2 * ((κ : ℂ) * J)) := by ring_nf
  have hEnorm : ‖e‖ ≤ 1 / 8 := by
    rw [hedef, hre, Complex.norm_exp]
    have hr2 : (Complex.I * z * (L : ℂ) - 2 * ((κ : ℂ) * J)).re
        = -(L * z.im) - 2 * ((κ : ℂ) * J).re := by
      simp [Complex.mul_re, Complex.mul_im]
      ring
    rw [hr2]
    have hab : ((κ : ℂ) * J).re ≥ -‖(κ : ℂ) * J‖ := by
      have := (abs_le.mp (Complex.abs_re_le_norm ((κ : ℂ) * J))).1
      linarith
    have hy : Real.exp (-(L * z.im) - 2 * ((κ : ℂ) * J).re) ≤ Real.exp (-(L * z.im - 1 / 4)) :=
      Real.exp_le_exp.mpr (by linarith)
    refine hy.trans ?_
    have hpos : 8 ≤ L * z.im - 1 / 4 := by linarith
    have hexpy : (L * z.im - 1 / 4) + 1 ≤ Real.exp (L * z.im - 1 / 4) :=
      Real.add_one_le_exp _
    calc Real.exp (-(L * z.im - 1 / 4)) = 1 / Real.exp (L * z.im - 1 / 4) := by
          rw [Real.exp_neg]; ring
      _ ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  rw [hEq]
  have hdecomp : Complex.exp ((κ : ℂ) * J) * (1 + e) - 1
      = (Complex.exp ((κ : ℂ) * J) - 1) + Complex.exp ((κ : ℂ) * J) * e := by ring
  rw [hdecomp]
  calc ‖(Complex.exp ((κ : ℂ) * J) - 1) + Complex.exp ((κ : ℂ) * J) * e‖
      ≤ ‖Complex.exp ((κ : ℂ) * J) - 1‖ + ‖Complex.exp ((κ : ℂ) * J) * e‖ := norm_add_le _ _
    _ ≤ 2 * (1 / 8) + (5 / 4) * (1 / 8) := by
        rw [norm_mul]
        have := mul_le_mul hexp2 hEnorm (norm_nonneg _) (by norm_num)
        linarith
    _ ≤ 1 / 2 := by norm_num

end QuantumNLS.RiccatiValueBounds

#print axioms QuantumNLS.RiccatiValueBounds.norm_modeCoef_le
#print axioms QuantumNLS.RiccatiValueBounds.logTrace_eq_logS
#print axioms QuantumNLS.RiccatiValueBounds.value_remainder
#print axioms QuantumNLS.RiccatiValueBounds.log_value
#print axioms QuantumNLS.RiccatiValueBounds.trace_near_one_bound
