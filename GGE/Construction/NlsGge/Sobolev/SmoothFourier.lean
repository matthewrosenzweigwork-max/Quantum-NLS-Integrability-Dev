import NlsGge.Sobolev.PhysicalRegularity
import NlsGge.Analysis.ReciprocalBracket
import Mathlib.Analysis.Calculus.SmoothSeries

set_option autoImplicit false
noncomputable section
open scoped Real
namespace NlsGge.Pilot

lemma japaneseBracket_sq (n : ℤ) : japaneseBracket n ^ 2 = 1 + (n : ℝ) ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma summable_japaneseBracket_inv_sq :
    Summable (fun n : ℤ => (japaneseBracket n)⁻¹ ^ 2) := by
  apply NlsGge.Analysis.summable_reciprocal_bracket_square.congr
  intro n
  rw [inv_pow, japaneseBracket_sq, one_div]

/-- Cauchy--Schwarz at the summability level, retaining the zero mode. -/
theorem summable_sobolev_amplitude (k : ℕ) (x : ℤ → ℂ)
    (hx : SobolevSquareSummable ((k + 1 : ℕ) : ℝ) x) :
    Summable (fun n : ℤ => japaneseBracket n ^ k * ‖x n‖) := by
  have hs : Summable (fun n : ℤ => (japaneseBracket n ^ (k + 1) * ‖x n‖) ^ 2) := by
    apply hx.congr
    intro n
    have he : 2 * ((k + 1 : ℕ) : ℝ) = ((k + 1) * 2 : ℕ) := by
      push_cast
      ring
    change Real.rpow (japaneseBracket n) (2 * ((k + 1 : ℕ) : ℝ)) * ‖x n‖ ^ 2 = _
    rw [he]
    have hr : Real.rpow (japaneseBracket n) (((k + 1) * 2 : ℕ) : ℝ) =
        japaneseBracket n ^ ((k + 1) * 2) := Real.rpow_natCast _ _
    rw [hr, mul_pow, ← pow_mul]
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg (japaneseBracket_pos n).le _) (norm_nonneg _))
    (fun n => ?_) (hs.add summable_japaneseBracket_inv_sq)
  have hprod : (japaneseBracket n ^ (k + 1) * ‖x n‖) * (japaneseBracket n)⁻¹ =
      japaneseBracket n ^ k * ‖x n‖ := by
    rw [pow_succ]
    have hn := (japaneseBracket_pos n).ne'
    field_simp
  nlinarith [sq_nonneg (japaneseBracket n ^ (k + 1) * ‖x n‖ - (japaneseBracket n)⁻¹),
    sq_nonneg (japaneseBracket n ^ (k + 1) * ‖x n‖), sq_nonneg ((japaneseBracket n)⁻¹)]

theorem summable_physicalWeighted_fourier_amplitude {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) (u : PhysicalWeighted c s) (k : ℕ) :
    Summable (fun n : ℤ => japaneseBracket n ^ k * ‖physicalFourier u.field n‖) :=
  summable_sobolev_amplitude k (physicalFourier u.field)
    (physicalWeighted_sobolev c s u ((k + 1 : ℕ) : ℝ))

def fourierMultiplier (n : ℤ) : ℂ := 2 * π * Complex.I * (n : ℂ)
def fourierRealTerm (n : ℤ) (z : ℂ) (y : ℝ) : ℂ := z * fourier n (y : PhysicalCircle)

theorem contDiff_fourierRealTerm (n : ℤ) (z : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fourierRealTerm n z) := by
  unfold fourierRealTerm
  apply contDiff_const.mul
  simp only [fourier_coe_apply]
  apply ContDiff.cexp
  apply ContDiff.div_const
  exact contDiff_const.mul Complex.ofRealCLM.contDiff

theorem hasDerivAt_fourierRealTerm (n : ℤ) (z : ℂ) (y : ℝ) :
    HasDerivAt (fourierRealTerm n z) (fourierRealTerm n (z * fourierMultiplier n) y) y := by
  have h := (hasDerivAt_fourier (1 : ℝ) n y).const_mul z
  convert h using 1
  · rfl
  · simp only [fourierRealTerm, fourierMultiplier, Complex.ofReal_one, div_one]
    ring

theorem iteratedDeriv_fourierRealTerm (n : ℤ) (z : ℂ) (k : ℕ) :
    iteratedDeriv k (fourierRealTerm n z) = fourierRealTerm n (z * fourierMultiplier n ^ k) := by
  induction k with
  | zero => simp only [iteratedDeriv_zero, pow_zero, mul_one]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    rw [(hasDerivAt_fourierRealTerm n (z * fourierMultiplier n ^ k) y).deriv]
    simp only [fourierRealTerm, pow_succ]
    ring

theorem norm_fourierMultiplier (n : ℤ) :
    ‖fourierMultiplier n‖ = (2 * π) * |(n : ℝ)| := by
  simp only [fourierMultiplier, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp]
  rw [Complex.norm_real, Real.norm_eq_abs]

theorem norm_iteratedFDeriv_fourierRealTerm (n : ℤ) (z : ℂ) (k : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ k (fourierRealTerm n z) y‖ = ((2 * π) * |(n : ℝ)|) ^ k * ‖z‖ := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_fourierRealTerm]
  simp only [fourierRealTerm, norm_mul, norm_pow, norm_fourierMultiplier,
    fourier_apply, Circle.norm_coe, mul_one]
  ring

theorem norm_iteratedFDeriv_fourierRealTerm_le (n : ℤ) (z : ℂ) (k : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ k (fourierRealTerm n z) y‖ ≤
      (2 * π) ^ k * (japaneseBracket n ^ k * ‖z‖) := by
  have hn : |(n : ℝ)| ≤ japaneseBracket n := by
    unfold japaneseBracket
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    linarith
  rw [norm_iteratedFDeriv_fourierRealTerm, mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hn k) (norm_nonneg z))
    (pow_nonneg (by positivity) k)

end NlsGge.Pilot
