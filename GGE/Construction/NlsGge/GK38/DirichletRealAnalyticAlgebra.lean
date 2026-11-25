import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.Normed.Operator.Prod

/-! Explicit triangular continuous linear inverse used by the actual analytic root chart. -/
set_option autoImplicit false
open ContinuousLinearMap
namespace NlsGge.GK38
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem dirichlet_triangular_invertible38 (L : E × ℝ →L[ℝ] ℝ) (hc : L (0, 1) ≠ 0) :
    ((ContinuousLinearMap.fst ℝ E ℝ).prod L).IsInvertible := by
  let c := L (0, 1)
  have hsplit (p : E × ℝ) : L p = L (p.1, 0) + p.2 * c := by
    have he : p = (p.1, 0) + p.2 • ((0 : E), (1 : ℝ)) := by ext <;> simp
    calc
      L p = L ((p.1, 0) + p.2 • ((0 : E), (1 : ℝ))) := congrArg L he
      _ = _ := by rw [map_add, map_smul]; rfl
  let g : E × ℝ →L[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).prod (c⁻¹ •
      ((ContinuousLinearMap.snd ℝ E ℝ) -
        (L.comp (ContinuousLinearMap.inl ℝ E ℝ)).comp (ContinuousLinearMap.fst ℝ E ℝ)))
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := g)
  · apply ContinuousLinearMap.ext
    intro p
    apply Prod.ext
    · rfl
    · change L (p.1, c⁻¹ * (p.2 - L (p.1, 0))) = p.2
      rw [hsplit]
      change L (p.1, 0) + c⁻¹ * (p.2 - L (p.1, 0)) * c = p.2
      field_simp [c, hc]
      ring
  · apply ContinuousLinearMap.ext
    intro p
    apply Prod.ext
    · rfl
    · change c⁻¹ * (L p - L (p.1, 0)) = p.2
      rw [hsplit]
      field_simp [c, hc]
      ring
end NlsGge.GK38
