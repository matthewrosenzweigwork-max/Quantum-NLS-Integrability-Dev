import NlsGge.Birkhoff.SignedMoments38
import NlsGge.Spectral.ActualTraceMomentsE02_38

/-! # SIGNED-MOMENTS (`F:rem:signed`), file 2: spectral side (`B`-free)

* **SIGNED-MOMENTS.01** `signedSpectralMoment38 u k = (2/π) ∫ (2λ)^k v(λ;u) dλ` (the signed hierarchy moment `C_k`);
  `signedSpectral_even_eq_localCharge38` (`C_{2j} = Q_{2j}`, E02) and `signedSpectral_odd_eq_oddLocalCharge38`
  (`C_{2j+1} = Im ∫₀¹ (-1)^{j+1} u p_{2j+2}`, from the E02 odd trace moments).
* **SIGNED-MOMENTS.02** `cs_moment38`, `signedSpectral_cs38`: `C_{2j+1}² ≤ C_{2j} C_{2j+2}` (Cauchy-Schwarz for the
  positive spectral measure `v dλ`, by the discriminant of `∫ (s(2λ)^j + (2λ)^{j+1})² v ≥ 0`).
* **SIGNED-MOMENTS.03** `signedSpectral_amgm38`: `|C_{2j+1}| ≤ (C_{2j} + C_{2j+2})/2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations MeasureTheory
open scoped ContDiff

/-- **SIGNED-MOMENTS.01.** The signed spectral moment `C_k(u) = (2/π) ∫ (2λ)^k v(λ;u) dλ`
(`v` = `actualGapHeightE02_38 u`, the boundary value of `Im k`; totalized integral, finite on smooth fields). -/
def signedSpectralMoment38 (u : PhysicalL2) (k : ℕ) : ℝ :=
  (2 / Real.pi) * ∫ t : ℝ, (2 * t) ^ k * actualGapHeightE02_38 u t

/-- The local polynomial representative of the odd moment `C_{2j+1}`: `Im ∫₀¹ (-1)^{j+1} u p_{2j+2}`. -/
def oddLocalCharge38 (u : ℝ → ℂ) (j : ℕ) : ℝ :=
  (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalOddChargeIntegrand38 j)).im

theorem spectralCharge38_eq_signed (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) (j : ℕ) :
    spectralCharge38 U hU hper j = signedSpectralMoment38 (smoothL2_38 U hU hper) (2 * j) := rfl

/-- `C_{2j} = Q_{2j}` (E02 trace formula) on smooth fields. -/
theorem signedSpectral_even_eq_localCharge38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) (j : ℕ) :
    signedSpectralMoment38 (smoothL2_38 U hU hper) (2 * j) = localCharge38 U j :=
  (localCharge_eq_spectralCharge38 U hU hper j).symm

/-- Integrability of all moments up to order `2J` of a smooth field, and the odd trace formula. -/
theorem signedSpectral_moments38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1)
    (J : ℕ) :
    (∀ k ≤ 2 * J, Integrable (fun t : ℝ =>
        (2 * t) ^ k * actualGapHeightE02_38 (smoothL2_38 U hU hper) t)) ∧
    ∀ j : ℕ, j + 1 ≤ J →
      signedSpectralMoment38 (smoothL2_38 U hU hper) (2 * j + 1) = oddLocalCharge38 U j := by
  have hall := fun m (hm : m ≤ 2 * J) => actualTraceMoments_E02_38 (smoothL2_38 U hU hper)
    (smoothL2_38_sobolev U hU hper) U hU hper (smoothL2_38_cover_ae U hU hper) J m hm
  refine ⟨fun k hk => ?_, fun j hj => ?_⟩
  · have := (hall k hk).1.const_mul ((2 : ℝ) ^ k)
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [mul_pow]; ring
  · obtain ⟨-, hval⟩ := hall (2 * j + 1) (by omega)
    set v := actualGapHeightE02_38 (smoothL2_38 U hU hper) with hv
    set T : ℝ := ∫ t, (t ^ (2 * j + 1) * v t) with hT
    set Z := ∫ x in (0 : ℝ)..1, riccatiJetEvaluation U x
      (MvPolynomial.X (false, 0) * p (2 * j + 1 + 1)) with hZ
    have hW : (∫ x in (0 : ℝ)..1, riccatiJetEvaluation U x (formalOddChargeIntegrand38 j)) =
        (-1 : ℂ) ^ (j + 1) * Z := by
      have hpt : ∀ x, riccatiJetEvaluation U x (formalOddChargeIntegrand38 j) =
          (-1 : ℂ) ^ (j + 1) *
            riccatiJetEvaluation U x (MvPolynomial.X (false, 0) * p (2 * j + 1 + 1)) := by
        intro x
        simp [formalOddChargeIntegrand38, riccatiJetEvaluation, polynomialEvaluation, mul_assoc]
      simp_rw [hpt]
      rw [intervalIntegral.integral_const_mul]
    have hb : riccatiQuasiCoeff38 U (2 * j + 1 + 1) =
        Complex.I * ((-2 : ℂ) ^ (2 * j + 1 + 1))⁻¹ * Z := rfl
    rw [hb] at hval
    have hIpow : Complex.I ^ (2 * j + 1 + 1) = (-1 : ℂ) ^ (j + 1) := by
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul, Complex.I_sq]
    have h2 : ((-2 : ℂ) ^ (2 * j + 1 + 1)) = (2 : ℂ) ^ (2 * j + 2) := by
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul]; norm_num
      rw [pow_mul]; norm_num
    rw [hIpow, h2] at hval
    -- R := 2^(2j+2) T / π
    set R : ℝ := (2 : ℝ) ^ (2 * j + 2) * T / Real.pi with hR
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2ne : ((2 : ℂ) ^ (2 * j + 2)) ≠ 0 := pow_ne_zero _ two_ne_zero
    have hsign : ((-1 : ℂ) ^ (j + 1)) * (-1 : ℂ) ^ (j + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have hWI : (-1 : ℂ) ^ (j + 1) * Z = Complex.I * (R : ℂ) := by
      have hRc : (R : ℂ) = (2 : ℂ) ^ (2 * j + 2) * (T : ℂ) / (Real.pi : ℂ) := by
        simp only [hR]; push_cast; ring
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      field_simp at hval
      have key : (-1 : ℂ) ^ (j + 1) * Z * (Real.pi : ℂ) =
          Complex.I * ((2 : ℂ) ^ (2 * j + 2) * (T : ℂ)) := by
        linear_combination (-Complex.I) * hval + ((-1 : ℂ) ^ (j + 1) * Z * (Real.pi : ℂ)) * hI
      rw [hRc]
      field_simp
      linear_combination key
    unfold oddLocalCharge38 signedSpectralMoment38
    rw [hW, hWI]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have hint : ∫ t : ℝ, (2 * t) ^ (2 * j + 1) * v t = 2 ^ (2 * j + 1) * T := by
      rw [hT, ← integral_const_mul]
      congr 1; funext t; rw [mul_pow]; ring
    rw [hint, hR]
    field_simp
    ring

/-- **SIGNED-MOMENTS.02** (Cauchy-Schwarz for the positive measure `v dλ`):
`(∫ (2λ)^{2j+1} v)² ≤ (∫ (2λ)^{2j} v)(∫ (2λ)^{2j+2} v)`. -/
theorem cs_moment38 (v : ℝ → ℝ) (hv0 : ∀ t, 0 ≤ v t) (j : ℕ)
    (i0 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j) * v t))
    (i1 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j + 1) * v t))
    (i2 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j + 2) * v t)) :
    (∫ t : ℝ, (2 * t) ^ (2 * j + 1) * v t) ^ 2 ≤
      (∫ t : ℝ, (2 * t) ^ (2 * j) * v t) * ∫ t : ℝ, (2 * t) ^ (2 * j + 2) * v t := by
  set f0 := ∫ t : ℝ, (2 * t) ^ (2 * j) * v t with hf0
  set f1 := ∫ t : ℝ, (2 * t) ^ (2 * j + 1) * v t with hf1
  set f2 := ∫ t : ℝ, (2 * t) ^ (2 * j + 2) * v t with hf2
  have hq : ∀ s : ℝ, 0 ≤ f0 * (s * s) + (2 * f1) * s + f2 := by
    intro s
    have ia : Integrable (fun t : ℝ => s ^ 2 * ((2 * t) ^ (2 * j) * v t)) := i0.const_mul _
    have ib : Integrable (fun t : ℝ => (2 * s) * ((2 * t) ^ (2 * j + 1) * v t)) := i1.const_mul _
    have hab : Integrable (fun t : ℝ => s ^ 2 * ((2 * t) ^ (2 * j) * v t) +
        (2 * s) * ((2 * t) ^ (2 * j + 1) * v t)) := ia.add ib
    have hnn : 0 ≤ ∫ t : ℝ, ((s ^ 2) * ((2 * t) ^ (2 * j) * v t) +
        (2 * s) * ((2 * t) ^ (2 * j + 1) * v t) + (2 * t) ^ (2 * j + 2) * v t) := by
      refine integral_nonneg fun t => ?_
      have : (s ^ 2) * ((2 * t) ^ (2 * j) * v t) + (2 * s) * ((2 * t) ^ (2 * j + 1) * v t) +
          (2 * t) ^ (2 * j + 2) * v t = ((s * (2 * t) ^ j + (2 * t) ^ (j + 1)) ^ 2) * v t := by
        ring
      rw [this]
      exact mul_nonneg (sq_nonneg _) (hv0 t)
    rw [integral_add hab i2, integral_add ia ib, integral_const_mul, integral_const_mul,
      ← hf0, ← hf1, ← hf2] at hnn
    nlinarith [hnn]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

/-- `|C_{2j+1}|² ≤ C_{2j} C_{2j+2}` for a field whose moments up to order `2j+2` are integrable. -/
theorem signedSpectral_cs38 (u : PhysicalL2) (j : ℕ)
    (i0 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t))
    (i1 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j + 1) * actualGapHeightE02_38 u t))
    (i2 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j + 2) * actualGapHeightE02_38 u t)) :
    signedSpectralMoment38 u (2 * j + 1) ^ 2 ≤
      signedSpectralMoment38 u (2 * j) * signedSpectralMoment38 u (2 * j + 2) := by
  have h := cs_moment38 (actualGapHeightE02_38 u) (actualGapHeightE02_38_nonneg u) j i0 i1 i2
  unfold signedSpectralMoment38
  have hc : 0 ≤ (2 / Real.pi) ^ 2 := sq_nonneg _
  calc ((2 / Real.pi) * ∫ t : ℝ, (2 * t) ^ (2 * j + 1) * actualGapHeightE02_38 u t) ^ 2
      = (2 / Real.pi) ^ 2 * (∫ t : ℝ, (2 * t) ^ (2 * j + 1) * actualGapHeightE02_38 u t) ^ 2 := by ring
    _ ≤ (2 / Real.pi) ^ 2 * ((∫ t : ℝ, (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t) *
          ∫ t : ℝ, (2 * t) ^ (2 * j + 2) * actualGapHeightE02_38 u t) :=
        mul_le_mul_of_nonneg_left h hc
    _ = _ := by ring

theorem signedSpectral_even_nonneg38 (u : PhysicalL2) (j : ℕ) :
    0 ≤ signedSpectralMoment38 u (2 * j) := by
  unfold signedSpectralMoment38
  refine mul_nonneg (by positivity) (integral_nonneg fun t => ?_)
  have : (2 * t) ^ (2 * j) = ((2 * t) ^ j) ^ 2 := by ring
  rw [this]
  exact mul_nonneg (sq_nonneg _) (actualGapHeightE02_38_nonneg u t)

/-- **SIGNED-MOMENTS.03** (arithmetic-geometric mean): `|C_{2j+1}| ≤ (C_{2j} + C_{2j+2})/2`. -/
theorem signedSpectral_amgm38 (u : PhysicalL2) (j : ℕ)
    (i0 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t))
    (i1 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j + 1) * actualGapHeightE02_38 u t))
    (i2 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j + 2) * actualGapHeightE02_38 u t)) :
    |signedSpectralMoment38 u (2 * j + 1)| ≤
      (signedSpectralMoment38 u (2 * j) + signedSpectralMoment38 u (2 * (j + 1))) / 2 := by
  have h := signedSpectral_cs38 u j i0 i1 i2
  have h0 := signedSpectral_even_nonneg38 u j
  have h2 := signedSpectral_even_nonneg38 u (j + 1)
  rw [show 2 * (j + 1) = 2 * j + 2 by ring] at h2 ⊢
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  nlinarith [sq_nonneg (signedSpectralMoment38 u (2 * j) - signedSpectralMoment38 u (2 * j + 2))]

end NlsGge.Birkhoff
end
