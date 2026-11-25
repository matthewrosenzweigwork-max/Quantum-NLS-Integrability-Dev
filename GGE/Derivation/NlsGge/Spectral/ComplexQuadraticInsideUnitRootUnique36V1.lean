import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations
/-- The characteristic polynomial has at most one root strictly inside the
unit circle. The strict condition is essential; the boundary is not asserted. -/
theorem complexQuadratic_insideUnitRoot_unique36V1
    (d w v : ℂ) (hwroot : w^2-2*d*w+1=0)
    (hvroot : v^2-2*d*v+1=0) (hw : ‖w‖ < 1) (hv : ‖v‖ < 1) : w=v := by
  have hfac : (w-v)*(w+v-2*d)=0 := by
    linear_combination hwroot-hvroot
  rcases mul_eq_zero.mp hfac with he | he
  · exact sub_eq_zero.mp he
  · have hsum : w+v=2*d := sub_eq_zero.mp he
    have hprod : w*v=1 := by
      linear_combination -hwroot+w*hsum
    have hn : ‖w‖*‖v‖=1 := by
      rw [← norm_mul, hprod, norm_one]
    have hh : ‖w‖*‖v‖ ≤ ‖w‖ := mul_le_of_le_one_right (norm_nonneg _) hv.le
    linarith
/-- With vacuum reference roots of product one, any characteristic root
strictly inside the unit circle equals the vacuum inside root. -/
theorem complexQuadratic_vacuumInsideRoot36V1
    (d a b w : ℂ) (hab : a*b=1) (hsum : a+b=2*d)
    (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) (hroot : w^2-2*d*w+1=0) : w=a := by
  have haroot : a^2-2*d*a+1=0 := by
    calc
      a^2-2*d*a+1 = a^2-(a+b)*a+a*b := by rw [hsum, hab]
      _ = 0 := by ring
  exact complexQuadratic_insideUnitRoot_unique36V1 d w a hroot haroot hw ha
end NlsGge.SpectralFoundations
end
