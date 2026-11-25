import Mathlib

namespace NlsGge.Atomic.AL048

                                                                                                         
-- Route: pointwise expansion of |x - 2y + z|^2 (x = alpha(j+1), y = alpha j, z = alpha(j-1)), then
-- cyclic reindexing of the three squared-norm sums and of the cross sum sum Re(alpha(j+1) conj alpha j).

theorem AL048 :
  ∀ (L : ℕ) [NeZero L] (α : ZMod L → ℂ),
    ∑ j : ZMod L, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2 =
      6 * ∑ j : ZMod L, ‖α j‖ ^ 2 - 8 * (∑ j : ZMod L, α j * star (α (j - 1))).re +
        2 * (∑ j : ZMod L, α (j + 1) * star (α (j - 1))).re := by
  intro L _ α
  have hpt : ∀ j : ZMod L, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2 =
      ‖α (j + 1)‖ ^ 2 + 4 * ‖α j‖ ^ 2 + ‖α (j - 1)‖ ^ 2 -
        4 * (α (j + 1) * star (α j)).re + 2 * (α (j + 1) * star (α (j - 1))).re -
        4 * (α j * star (α (j - 1))).re := by
    intro j
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hA1 : ∑ j : ZMod L, ‖α (j + 1)‖ ^ 2 = ∑ j : ZMod L, ‖α j‖ ^ 2 := by
    have h := Equiv.sum_comp (Equiv.addRight (1 : ZMod L)) (fun j => ‖α j‖ ^ 2)
    simpa using h
  have hA2 : ∑ j : ZMod L, ‖α (j - 1)‖ ^ 2 = ∑ j : ZMod L, ‖α j‖ ^ 2 := by
    have h := Equiv.sum_comp (Equiv.subRight (1 : ZMod L)) (fun j => ‖α j‖ ^ 2)
    simpa using h
  have hC : ∑ j : ZMod L, (α j * star (α (j - 1))).re =
      ∑ j : ZMod L, (α (j + 1) * star (α j)).re := by
    have h := Equiv.sum_comp (Equiv.subRight (1 : ZMod L))
      (fun j => (α (j + 1) * star (α j)).re)
    simpa using h
  simp only [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Complex.re_sum, Complex.re_sum, hA1, hA2, hC]
  ring

end NlsGge.Atomic.AL048
