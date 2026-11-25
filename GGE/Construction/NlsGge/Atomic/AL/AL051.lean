import Mathlib

namespace NlsGge.Atomic.AL051


                                                                                                                                            
set_option autoImplicit false


theorem AL051_main : ((∀ (M : ℕ) [NeZero M] (α : ZMod M → ℂ),
    2 * ∑ j, ((α j * star (α (j - 1))).im) ^ 2 =
      ∑ j, ‖α j‖ ^ 2 * ‖α (j + 1)‖ ^ 2 - (∑ j, (α j * star (α (j - 1))) ^ 2).re) : Prop) := by
  intro M _ α
  have hterm : ∀ j : ZMod M, 2 * ((α j * star (α (j - 1))).im) ^ 2 =
      ‖α j‖ ^ 2 * ‖α (j - 1)‖ ^ 2 - ((α j * star (α (j - 1))) ^ 2).re := by
    intro j
    have hz : ‖α j * star (α (j - 1))‖ ^ 2 = ‖α j‖ ^ 2 * ‖α (j - 1)‖ ^ 2 := by
      rw [norm_mul, mul_pow, norm_star]
    have hn : ‖α j * star (α (j - 1))‖ ^ 2 =
        (α j * star (α (j - 1))).re ^ 2 + (α j * star (α (j - 1))).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hr : ((α j * star (α (j - 1))) ^ 2).re =
        (α j * star (α (j - 1))).re ^ 2 - (α j * star (α (j - 1))).im ^ 2 := by
      rw [sq, Complex.mul_re]; ring
    rw [hr, ← hz, hn]; ring
  have hshift : ∑ j : ZMod M, ‖α j‖ ^ 2 * ‖α (j - 1)‖ ^ 2 =
      ∑ j : ZMod M, ‖α j‖ ^ 2 * ‖α (j + 1)‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.subRight 1) (fun j => ‖α j‖ ^ 2 * ‖α (j - 1)‖ ^ 2)
      (fun j => ‖α j‖ ^ 2 * ‖α (j + 1)‖ ^ 2)
      (fun j => by simp only [Equiv.subRight_apply, sub_add_cancel]; ring)
  have hsum : 2 * ∑ j : ZMod M, ((α j * star (α (j - 1))).im) ^ 2 =
      ∑ j : ZMod M, ‖α j‖ ^ 2 * ‖α (j - 1)‖ ^ 2 - (∑ j : ZMod M, (α j * star (α (j - 1))) ^ 2).re := by
    rw [Finset.mul_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => hterm j
  rw [hsum, hshift]


end NlsGge.Atomic.AL051
