import Mathlib
import NlsGge.GK38.StdRootBranchesDefs
import NlsGge.GK38.Lib.ParamProductsRoot
/- H215_ROOTDEV01 (proof development, AUTHOR; not self-reviewed). Pro round 9 section 10, step 3 (G4-018).
   Scalar standard-root deviation from the principal-root estimate Lib.norm_sqrt_one_sub_sub_one_le:
   |stdRoot38 tau g z - (tau - z)| <= |g|/(4|tau - z|), and the one-factor ratio estimate
   |(v+d)/w - 1| <= |d|/t + |g|/(4 t^2) whenever |v|, |w| >= t > 0. No small-gap premise. -/
set_option autoImplicit false

namespace NlsGge.G4018Support

open NlsGge.GK38

theorem stdRoot_sub_tau_le (τ g z : ℂ) (hv : τ - z ≠ 0) :
    ‖stdRoot38 τ g z - (τ - z)‖ ≤ ‖g‖ / (4 * ‖τ - z‖) := by
  have h1 : stdRoot38 τ g z - (τ - z) = (τ - z) * (Complex.sqrt (1 - (g / 4) / (τ - z) ^ 2) - 1) := by
    unfold stdRoot38
    ring
  have hv0 : ‖τ - z‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have h2 := Lib.norm_sqrt_one_sub_sub_one_le ((g / 4) / (τ - z) ^ 2)
  rw [h1, norm_mul]
  calc ‖τ - z‖ * ‖Complex.sqrt (1 - (g / 4) / (τ - z) ^ 2) - 1‖
      ≤ ‖τ - z‖ * ‖(g / 4) / (τ - z) ^ 2‖ := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖g‖ / (4 * ‖τ - z‖) := by
        rw [norm_div, norm_div, norm_pow, Complex.norm_ofNat]
        field_simp

theorem ratio_sub_one_le (v d g w : ℂ) (t : ℝ) (ht : 0 < t)
    (hv : t ≤ ‖v‖) (hw : t ≤ ‖w‖) (hwv : ‖w - v‖ ≤ ‖g‖ / (4 * ‖v‖)) :
    ‖(v + d) / w - 1‖ ≤ ‖d‖ / t + ‖g‖ / (4 * t ^ 2) := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    linarith
  have e : (v + d) / w - 1 = ((v - w) + d) / w := by
    field_simp
    ring
  have ht4 : 0 < 4 * t := by linarith
  have hA : ‖g‖ / (4 * ‖v‖) ≤ ‖g‖ / (4 * t) := by
    gcongr
  have hnum : ‖(v - w) + d‖ ≤ ‖g‖ / (4 * t) + ‖d‖ := by
    calc ‖(v - w) + d‖ ≤ ‖v - w‖ + ‖d‖ := norm_add_le _ _
      _ = ‖w - v‖ + ‖d‖ := by rw [norm_sub_rev]
      _ ≤ ‖g‖ / (4 * t) + ‖d‖ := by linarith [hwv.trans hA]
  calc ‖(v + d) / w - 1‖ = ‖(v - w) + d‖ / ‖w‖ := by rw [e, norm_div]
    _ ≤ (‖g‖ / (4 * t) + ‖d‖) / t := by
        gcongr
    _ = ‖d‖ / t + ‖g‖ / (4 * t ^ 2) := by
        field_simp
        ring

end NlsGge.G4018Support
