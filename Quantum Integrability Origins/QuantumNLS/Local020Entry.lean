import Mathlib
import QuantumNLS.LocalSpectralReduced
import QuantumNLS.Local020Abs

/-! LOCAL-020: the lower-left entry `b = (B e₀)₁` of a `2×2` reduced matrix and its behaviour under conjugation by a
diagonal unit matrix. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
noncomputable section

open QuantumNLS.LocalSpectral QuantumNLS.Local020Abs

namespace QuantumNLS.Local020Entry

/-- The lower-left entry `(B e₀)₁`. -/
def bentry (B : E2 →L[ℂ] E2) : ℂ := (B (vec2 1 0)) 1

theorem bentry_id (p : ℂ) : bentry (p • ContinuousLinearMap.id ℂ E2) = 0 := by
  simp [bentry, vec2]

theorem bentry_add (A B : E2 →L[ℂ] E2) : bentry (A + B) = bentry A + bentry B := by
  simp [bentry]

theorem bentry_sub (A B : E2 →L[ℂ] E2) : bentry (A - B) = bentry A - bentry B := by
  simp [bentry]

theorem bentry_smul (c : ℂ) (A : E2 →L[ℂ] E2) : bentry (c • A) = c * bentry A := by
  simp [bentry]

theorem bentry_cjE (M : E2 ≃ₗᵢ[ℂ] E2) (m0 m1 : ℂ) (hm : ∀ v : E2, M v = vec2 (m0 * v 0) (m1 * v 1))
    (h0 : starRingEnd ℂ m0 * m0 = 1) (B : E2 →L[ℂ] E2) :
    bentry (cjE M B) = m1 * starRingEnd ℂ m0 * bentry B := by
  have hs : M.symm (vec2 1 0) = starRingEnd ℂ m0 • vec2 1 0 := by
    apply M.injective
    rw [M.apply_symm_apply, map_smul, hm]
    ext i
    fin_cases i <;> simp [vec2]
    exact h0.symm
  unfold bentry
  rw [cjE_apply, hs, map_smul, hm]
  simp [vec2]
  ring

/-- Transport of the entry through `B' = p' 1 + ε M (B - p 1) M⁻¹`. -/
theorem bentry_transport (M : E2 ≃ₗᵢ[ℂ] E2) (m0 m1 : ℂ) (hm : ∀ v : E2, M v = vec2 (m0 * v 0) (m1 * v 1))
    (h0 : starRingEnd ℂ m0 * m0 = 1) (ε p p' : ℂ) {B B' : E2 →L[ℂ] E2}
    (h : B' = p' • ContinuousLinearMap.id ℂ E2 + ε • cjE M (B - p • ContinuousLinearMap.id ℂ E2)) :
    bentry B' = ε * (m1 * starRingEnd ℂ m0) * bentry B := by
  have hc : cjE M (p • ContinuousLinearMap.id ℂ E2) = p • ContinuousLinearMap.id ℂ E2 := by
    ext x
    simp [cjE_apply]
  rw [h, bentry_add, bentry_id, zero_add, bentry_smul, map_sub, hc, bentry_sub, bentry_id, sub_zero,
    bentry_cjE M m0 m1 hm h0]
  ring

end QuantumNLS.Local020Entry

#print axioms QuantumNLS.Local020Entry.bentry_transport
