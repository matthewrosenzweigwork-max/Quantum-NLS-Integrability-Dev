import Mathlib

namespace NlsGge.Atomic.AL050

                                                                                                         
-- Route: pointwise |x - z|^2 expansion (x = alpha(j+1), z = alpha(j-1)), then cyclic reindexing of
-- the r_j r_{j-1} term onto r_j r_{j+1}.

theorem AL050 :
  ∀ (L : ℕ) [NeZero L] (α : ZMod L → ℂ),
    ∑ j : ZMod L, ‖α j‖ ^ 2 * ‖α (j + 1) - α (j - 1)‖ ^ 2 =
      2 * ∑ j : ZMod L, ‖α j‖ ^ 2 * ‖α (j + 1)‖ ^ 2 -
        2 * ∑ j : ZMod L, ‖α j‖ ^ 2 * (α (j + 1) * star (α (j - 1))).re := by
  intro L _ α
  have hpt : ∀ j : ZMod L, ‖α j‖ ^ 2 * ‖α (j + 1) - α (j - 1)‖ ^ 2 =
      ‖α j‖ ^ 2 * ‖α (j + 1)‖ ^ 2 + ‖α j‖ ^ 2 * ‖α (j - 1)‖ ^ 2 -
        2 * (‖α j‖ ^ 2 * (α (j + 1) * star (α (j - 1))).re) := by
    intro j
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hshift : ∑ j : ZMod L, ‖α j‖ ^ 2 * ‖α (j - 1)‖ ^ 2 =
      ∑ j : ZMod L, ‖α j‖ ^ 2 * ‖α (j + 1)‖ ^ 2 := by
    have h := Equiv.sum_comp (Equiv.subRight (1 : ZMod L))
      (fun j => ‖α j‖ ^ 2 * ‖α (j + 1)‖ ^ 2)
    simp only [Equiv.subRight_apply, sub_add_cancel] at h
    rw [← h]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  simp only [hpt]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hshift, ← Finset.mul_sum]
  ring

end NlsGge.Atomic.AL050
