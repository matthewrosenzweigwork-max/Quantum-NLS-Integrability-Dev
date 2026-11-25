import Mathlib

namespace NlsGge.Atomic.F020


                                                                                                                                          
set_option autoImplicit false


theorem F020_main : ((∀ j k l m dt dr : ℕ, (dt : ℤ) + dr = 2 * j + 2 - 2 * k - 2 * l → j ≤ m → 1 ≤ k →
    (2 * (j : ℤ) + 1 - k * (2 * m + 1) - l ≤ -(l : ℤ)) ∧
    (l = 0 → 2 ≤ k → (dt : ℤ) - k * (2 * m - 1) ≤ -2 * (m : ℤ))) : Prop) := by
  intro j k l m dt dr h hjm hk
  have hjm' : (j : ℤ) ≤ m := by exact_mod_cast hjm
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hm0 : (0 : ℤ) ≤ 2 * m + 1 := by positivity
  have hdr : (0 : ℤ) ≤ dr := by positivity
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hk' hm0]
  · intro hl hk2
    subst hl
    have hk2' : (2 : ℤ) ≤ k := by exact_mod_cast hk2
    nlinarith [mul_le_mul_of_nonneg_right hk2' hm0]


end NlsGge.Atomic.F020
