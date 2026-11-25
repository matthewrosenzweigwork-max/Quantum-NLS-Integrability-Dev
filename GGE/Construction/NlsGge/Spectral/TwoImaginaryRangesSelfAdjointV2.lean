import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
noncomputable section
open scoped LinearPMap

namespace NlsGge.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Generic two-range criterion on the genuine partial-map domain.
The concrete NLS domain, symmetry and both ranges must be supplied separately. -/
theorem partialMap_selfAdjoint_of_two_imaginary_ranges
    (A : E →ₗ.[ℂ] E) (η : ℝ) (hη : 0 < η)
    (hdense : Dense (A.domain : Set E)) (hsymm : A.IsFormalAdjoint A)
    (hminus : ∀ y : E, ∃ u : A.domain,
      A u - (Complex.I * (η : ℂ)) • (u : E) = y)
    (hplus : ∀ y : E, ∃ u : A.domain,
      A u + (Complex.I * (η : ℂ)) • (u : E) = y) :
    IsSelfAdjoint A := by
  have hinc : A ≤ A† := hsymm.le_adjoint hdense
  have hadj : A.IsFormalAdjoint A† := (A.adjoint_isFormalAdjoint hdense).symm
  have hdom : A†.domain ≤ A.domain := by
    intro x hx
    let x' : A†.domain := ⟨x, hx⟩
    obtain ⟨u, hu⟩ := hminus (A† x' - (Complex.I * (η : ℂ)) • x)
    have hdiff : A† x' - A u = (Complex.I * (η : ℂ)) • (x - (u : E)) := by
      rw [smul_sub]
      apply sub_eq_sub_iff_add_eq_add.mpr
      exact (sub_eq_sub_iff_add_eq_add.mp hu).symm.trans (add_comm _ _)
    have horth : ∀ w : A.domain,
        inner ℂ (A w + (Complex.I * (η : ℂ)) • (w : E))
          (x - (u : E)) = 0 := by
      intro w
      have hAw : inner ℂ (A w) (x - (u : E)) =
          (Complex.I * (η : ℂ)) * inner ℂ (w : E) (x - (u : E)) := by
        rw [inner_sub_right, hadj w x', hsymm w u,
          ← inner_sub_right, hdiff, inner_smul_right]
      rw [inner_add_left, hAw, inner_smul_left]
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
      ring
    obtain ⟨w, hw⟩ := hplus (x - (u : E))
    have hz : x - (u : E) = 0 :=
      (inner_self_eq_zero (𝕜 := ℂ)).mp (hw ▸ horth w)
    have hxu : x = (u : E) := sub_eq_zero.mp hz
    exact hxu ▸ u.property
  have hback : A† ≤ A := by
    refine ⟨hdom, ?_⟩
    intro x y hxy
    exact (hinc.2 hxy.symm).symm
  exact LinearPMap.isSelfAdjoint_def.mpr (le_antisymm hback hinc)

end NlsGge.Spectral
end
