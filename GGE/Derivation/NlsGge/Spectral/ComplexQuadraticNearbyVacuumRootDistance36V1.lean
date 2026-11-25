import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations

/-- Scalar characteristic-polynomial stability, retaining BOTH possible
vacuum roots. This does not select the physical small-root branch. -/
theorem complexQuadratic_rootDistanceProduct36V1
    (d d₀ w a b : ℂ) (hab : a*b=1) (hsum : a+b=2*d₀)
    (hroot : w^2-2*d*w+1=0) (hw : ‖w‖ ≤ 1) :
    ‖w-a‖*‖w-b‖ ≤ 2*‖d-d₀‖ := by
  have he : (w-a)*(w-b)=2*(d-d₀)*w := by
    calc
      (w-a)*(w-b)=w^2-(a+b)*w+a*b := by ring
      _ = w^2-2*d₀*w+1 := by rw [hsum, hab]
      _ = 2*(d-d₀)*w := by linear_combination hroot
  calc
    ‖w-a‖*‖w-b‖ = ‖(w-a)*(w-b)‖ := (norm_mul _ _).symm
    _ = (2*‖d-d₀‖)*‖w‖ := by rw [he]; norm_num [norm_mul]
    _ ≤ 2*‖d-d₀‖ := mul_le_of_le_one_right (by positivity) hw

/-- A characteristic root lies near at least one vacuum root. The actual
coupling-family continuity and branch selection are separate prerequisites. -/
theorem complexQuadratic_minRootDistance36V1
    (d d₀ w a b : ℂ) (hab : a*b=1) (hsum : a+b=2*d₀)
    (hroot : w^2-2*d*w+1=0) (hw : ‖w‖ ≤ 1) :
    min ‖w-a‖ ‖w-b‖ ≤ Real.sqrt (2*‖d-d₀‖) := by
  have hm : 0 ≤ min ‖w-a‖ ‖w-b‖ := le_min (norm_nonneg _) (norm_nonneg _)
  have hp : min ‖w-a‖ ‖w-b‖ * min ‖w-a‖ ‖w-b‖ ≤ ‖w-a‖*‖w-b‖ :=
    mul_le_mul (min_le_left _ _) (min_le_right _ _) hm (norm_nonneg _)
  apply (Real.le_sqrt hm (by positivity)).mpr
  simpa only [pow_two] using hp.trans
    (complexQuadratic_rootDistanceProduct36V1 d d₀ w a b hab hsum hroot hw)
end NlsGge.SpectralFoundations
end
