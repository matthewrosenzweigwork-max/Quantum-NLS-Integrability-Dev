import Mathlib

namespace NlsGge.Atomic.AL046


                                                                                                                                            
set_option autoImplicit false


theorem AL046_main : ((∀ u w : ℂ, (3 / 2) * (2 * (star u * w).re) ^ 2 + 4 * ‖u‖ ^ 2 * ‖w‖ ^ 2 + 2 * (star u * w).im ^ 2 =
    6 * ‖u‖ ^ 2 * ‖w‖ ^ 2 + (2 * (star u * w).re) ^ 2) : Prop) := by
  intro u w
  have h1 : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h2 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have e1 : (star u * w).re = u.re * w.re + u.im * w.im := by
    simp [Complex.star_def, Complex.mul_re]
  have e2 : (star u * w).im = u.re * w.im - u.im * w.re := by
    simp [Complex.star_def, Complex.mul_im]; ring
  rw [e1, e2, h1, h2]
  ring


end NlsGge.Atomic.AL046
