import NlsGge.GK38.XiSqTauRatio
import Mathlib.Analysis.SpecialFunctions.Log.Summable

set_option autoImplicit false
open Set Filter Topology Metric SummationFilter
namespace NlsGge.GK38
noncomputable section

def a5OmittedQ38 (n m : ℤ) (p : PotPair × ℂ) : ℂ :=
  if m = n then 1 else
    Complex.sqrt (1 - (gamma2 p.1 m / 4) / (tauN p.1 m - p.2)^2)

def a5QCorrectionProduct38 (n : ℤ) (p : PotPair × ℂ) : ℂ :=
  ∏' m : ℤ, a5OmittedQ38 n m p

/-- Global principal-root bound, including totalized zero denominators. -/
theorem a5QNormDifference_le38 (g w : ℂ) :
    ‖Complex.sqrt (1 - (g / 4) / w^2) - 1‖ ≤ ‖g‖ / (4 * ‖w‖^2) := by
  calc
    _ ≤ ‖(g / 4) / w^2‖ := Lib.norm_sqrt_one_sub_sub_one_le ((g / 4) / w^2)
    _ = _ := by
      rw [Complex.norm_div, Complex.norm_div, Complex.norm_pow, Complex.norm_ofNat]
      ring

/-- A scalar separation estimate is used only with a positive distance and scale. -/
theorem a5QNormDifference_separation38 (g w : ℂ) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d) (hsep : c⁻¹ * d ≤ ‖w‖) :
    ‖Complex.sqrt (1 - (g / 4) / w^2) - 1‖ ≤
      (c^2 / 4) * ‖g‖ * (1 / d)^2 := by
  have hw : 0 < ‖w‖ := (mul_pos (inv_pos.mpr hc) hd).trans_le hsep
  have hcd : d ≤ c * ‖w‖ := by
    have hh : d / c ≤ ‖w‖ := by simpa only [div_eq_mul_inv, mul_comm] using hsep
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hh
  have hinv : 1 / ‖w‖^2 ≤ c^2 / d^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hw) (sq_pos_of_pos hd)).2
    simpa only [one_mul, mul_pow] using pow_le_pow_left₀ hd.le hcd 2
  calc
    _ ≤ ‖g‖ / (4 * ‖w‖^2) := a5QNormDifference_le38 g w
    _ = (‖g‖ / 4) * (1 / ‖w‖^2) := by ring
    _ ≤ (‖g‖ / 4) * (c^2 / d^2) := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring

theorem a5GammaNorm_summable38 (φ : PotPair) (hφ : φ ∈ gkW) :
    Summable (fun m : ℤ => ‖gamma2 φ m‖) := by
  obtain ⟨V, hV, _hVW, _B, _hB, h⟩ := tauGamma_common_value_bound38 discC discR
    isolating_selectors_admissible38 φ hφ
  exact (h φ (mem_of_mem_nhds hV)).2.2.1

/-- Actual OTHER-factor separation controls absolute root correction errors. -/
theorem a5OmittedQ_norm_error38 (n m : ℤ) (p : PotPair × ℂ) (c : ℝ) (hc : 0 < c)
    (hsep : ∀ j : ℤ, j ≠ n → c⁻¹ * |(j : ℝ) - n| ≤ ‖tauN p.1 j - p.2‖) :
    ‖a5OmittedQ38 n m p - 1‖ ≤
      (c^2 / 4) * (‖gamma2 p.1 m‖ * Lib.c3w n m^2) := by
  by_cases hm : m = n
  · simp only [a5OmittedQ38, hm, ite_true, sub_self, norm_zero]
    positivity
  · have hdist : 0 < |(m : ℝ) - n| := by
      apply abs_pos.mpr
      exact_mod_cast sub_ne_zero.mpr hm
    simpa only [a5OmittedQ38, hm, ite_false, Lib.c3w, mul_assoc] using
      a5QNormDifference_separation38 (gamma2 p.1 m) (tauN p.1 m - p.2)
        c |(m : ℝ) - n| hc hdist (hsep m hm)

/-- Genuine absolute summability precedes the ordinary and symmetric product identities. -/
theorem a5OmittedQ_error_summable38 (n : ℤ) (p : PotPair × ℂ) (hW : p.1 ∈ gkW)
    (c : ℝ) (hc : 0 < c)
    (hsep : ∀ j : ℤ, j ≠ n → c⁻¹ * |(j : ℝ) - n| ≤ ‖tauN p.1 j - p.2‖) :
    Summable (fun m : ℤ => ‖a5OmittedQ38 n m p - 1‖) ∧
      (∑' m : ℤ, ‖a5OmittedQ38 n m p - 1‖) ≤
        (c^2 / 4) * a5GammaConvolution38 p.1 n := by
  have hsγ := a5GammaNorm_summable38 p.1 hW
  have hterm : Summable (fun m : ℤ => ‖gamma2 p.1 m‖ * Lib.c3w n m^2) := by
    refine hsγ.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    have hw0 := Lib.c3w_nonneg n m
    have hw1 := Lib.c3w_le_one n m
    have hw2 : Lib.c3w n m^2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hw0 hw1 2
    exact (mul_le_mul_of_nonneg_left hw2 (norm_nonneg _)).trans_eq (mul_one _)
  have hdom := hterm.mul_left (c^2/4)
  have hs := hdom.of_nonneg_of_le (fun m => norm_nonneg _)
    (fun m => a5OmittedQ_norm_error38 n m p c hc hsep)
  refine ⟨hs, (hs.tsum_le_tsum (fun m => a5OmittedQ_norm_error38 n m p c hc hsep) hdom).trans_eq ?_⟩
  rw [tsum_mul_left, a5GammaConvolution_eq38]

/-- Absolute convergence supplies the actual ordinary correction product and its norm bound. -/
theorem a5QCorrectionProduct_converges_bound38 (n : ℤ) (p : PotPair × ℂ)
    (hW : p.1 ∈ gkW) (c : ℝ) (hc : 0 < c)
    (hsep : ∀ j : ℤ, j ≠ n → c⁻¹ * |(j : ℝ) - n| ≤ ‖tauN p.1 j - p.2‖) :
    Multipliable (fun m : ℤ => a5OmittedQ38 n m p) ∧
      ‖a5QCorrectionProduct38 n p - 1‖ ≤
        Real.exp ((c^2 / 4) * a5GammaConvolution38 p.1 n) - 1 := by
  obtain ⟨hs, hb⟩ := a5OmittedQ_error_summable38 n p hW c hc hsep
  have he : (fun m : ℤ => 1 + (a5OmittedQ38 n m p - 1)) =
      (fun m : ℤ => a5OmittedQ38 n m p) := by funext m; ring
  have hm := multipliable_one_add_of_summable hs
  have hbound := Lib.norm_tprod_one_add_sub_one_le hs
  rw [he] at hm hbound
  exact ⟨hm, hbound.trans (sub_le_sub_right (Real.exp_le_exp.mpr hb) 1)⟩

/-- Exact actual omitted product factorization, preserving all piN and symmetric conventions. -/
theorem a5OmittedRoot_tauQ_factorization38 (n : ℤ) (p : PotPair × ℂ)
    (hp : p ∈ a5OmittedRootDomain38 n) (c : ℝ) (hc : 0 < c)
    (hsep : ∀ j : ℤ, j ≠ n → c⁻¹ * |(j : ℝ) - n| ≤ ‖tauN p.1 j - p.2‖) :
    a5OmittedRootProduct38 n p = a5TauNumerator38 n p * a5QCorrectionProduct38 n p := by
  have hτ := (a5TauNumerator_multipliable38 n p hp.1).hasProd
  rw [← a5TauNumerator_product38 n p hp.1] at hτ
  have hQ := (a5QCorrectionProduct_converges_bound38 n p hp.1 c hc hsep).1
  have hQsym := hQ.hasProd.mono_left (symmetricIcc ℤ).le_atTop
  have he : (fun m : ℤ =>
      (if m = n then 1 else (tauN p.1 m - p.2) / (Lib.piN m : ℂ)) * a5OmittedQ38 n m p) =
      (fun m : ℤ => a5OmittedRootFactor38 n m p) := by
    funext m
    by_cases hm : m = n
    · simp only [hm, a5OmittedQ38, a5OmittedRootFactor38, ite_true, one_mul]
    · simp only [hm, a5OmittedQ38, a5OmittedRootFactor38, ite_false, rootFactor38, stdRoot38]
      ring
  have hprod := hτ.mul hQsym
  rw [he] at hprod
  exact hprod.tprod_eq

theorem a5QCorrectionProduct_ne_zero38 (n : ℤ) (p : PotPair × ℂ)
    (hp : p ∈ a5OmittedRootDomain38 n) (c : ℝ) (hc : 0 < c)
    (hsep : ∀ j : ℤ, j ≠ n → c⁻¹ * |(j : ℝ) - n| ≤ ‖tauN p.1 j - p.2‖) :
    a5QCorrectionProduct38 n p ≠ 0 := by
  intro he
  apply a5OmittedRoot_ne_zero38 n p hp
  rw [a5OmittedRoot_tauQ_factorization38 n p hp c hc hsep, he, mul_zero]

/-- Actual chi, with genuine C.3 convergence supplied before the exact ratio identity. -/
theorem a5Chi_ratioQ38 (n : ℤ) (p : PotPair × ℂ)
    (hp : p ∈ a5OmittedRootDomain38 n) (c : ℝ) (hc : 0 < c)
    (hsep : ∀ j : ℤ, j ≠ n → c⁻¹ * |(j : ℝ) - n| ≤ ‖tauN p.1 j - p.2‖)
    (hprod : Multipliable (Lib.ratioFam (lamDot p.1) (tauN p.1) n p.2) (symmetricIcc ℤ)) :
    a5Chi38 n p = Lib.ratioProd (lamDot p.1) (tauN p.1) n p.2 / a5QCorrectionProduct38 n p := by
  unfold a5Chi38
  rw [a5CriticalTau_ratio_product38 n p hp hprod,
    a5OmittedRoot_tauQ_factorization38 n p hp c hc hsep]
  have hT := a5TauNumerator_ne_zero38 n p hp
  have hQ := a5QCorrectionProduct_ne_zero38 n p hp c hc hsep
  field_simp

end
end NlsGge.GK38
