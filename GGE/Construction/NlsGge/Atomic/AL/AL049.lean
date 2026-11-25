import Mathlib

namespace NlsGge.Atomic.AL049


                                                                                                                                            
set_option autoImplicit false


theorem AL049_main : ((∀ (M : ℕ) [NeZero M] (r : ZMod M → ℝ),
    (3 / 2 : ℝ) * ∑ j, (r (j + 1) - r j) ^ 2 = 3 * ∑ j, r j ^ 2 - 3 * ∑ j, r j * r (j + 1)) : Prop) := by
  intro M _ r
  have hshift : ∑ j : ZMod M, r (j + 1) ^ 2 = ∑ j : ZMod M, r j ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight 1) (fun j => r (j + 1) ^ 2) (fun j => r j ^ 2) (fun j => rfl)
  have hexp : ∑ j : ZMod M, (r (j + 1) - r j) ^ 2 =
      ∑ j : ZMod M, r (j + 1) ^ 2 - 2 * ∑ j : ZMod M, r j * r (j + 1) + ∑ j : ZMod M, r j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, hshift]
  ring


end NlsGge.Atomic.AL049
