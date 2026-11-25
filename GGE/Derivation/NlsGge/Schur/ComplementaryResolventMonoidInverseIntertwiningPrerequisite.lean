import Mathlib.Algebra.Group.Defs

set_option autoImplicit false

namespace NlsGge.Schur

/-- Two-sided inverse choices for one element of a monoid agree. -/
theorem monoid_twoSidedInverse_unique_actual22
    {M : Type*} [Monoid M] (T S₁ S₂ : M)
    (hleft : S₁ * T = 1) (hright : T * S₂ = 1) :
    S₁ = S₂ := by
  calc
    S₁ = S₁ * 1 := (mul_one _).symm
    _ = S₁ * (T * S₂) := by rw [hright]
    _ = (S₁ * T) * S₂ := by simp only [mul_assoc]
    _ = 1 * S₂ := by rw [hleft]
    _ = S₂ := one_mul _

/-- An intertwining relation transports a two-sided inverse across its actual
pair of left/right factors, with all multiplication order retained. -/
theorem monoid_intertwining_twoSidedInverses_actual22
    {M : Type*} [Monoid M] (X Y D Sx Sy : M)
    (hintertwine : X * D = D * Y)
    (hSx : Sx * X = 1) (hSy : Y * Sy = 1) :
    Sx * D = D * Sy := by
  calc
    Sx * D = (Sx * D) * 1 := (mul_one _).symm
    _ = (Sx * D) * (Y * Sy) := by rw [hSy]
    _ = Sx * (D * Y) * Sy := by simp only [mul_assoc]
    _ = Sx * (X * D) * Sy := by rw [← hintertwine]
    _ = (Sx * X) * (D * Sy) := by simp only [mul_assoc]
    _ = D * Sy := by rw [hSx, one_mul]

end NlsGge.Schur
