import NlsGge.GK38.AbelianQuarterArcGeometry
import Mathlib.Tactic.Ring

/-! SOURCE ONLY: four actual square-edge FUNCTION equalities before derivatives
or integrals. All complex centers and real signed/zero radii are retained.
Exact target/English preceded proof; UNCOMPILED/no native scope. -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

theorem p6Square_edge_affine_curves38 (c : ℂ) (r : ℝ) :
    (fun y : ℝ => p6RotatedSquareSector38 c r 0 1 y) =
      (fun y : ℝ => ((c.re+r : ℝ) : ℂ)+((r*y+c.im : ℝ) : ℂ)*Complex.I) ∧
    (fun y : ℝ => p6RotatedSquareSector38 c r 1 1 y) =
      (fun y : ℝ => ((c.im+r : ℝ) : ℂ)*Complex.I+((-r*y+c.re : ℝ) : ℂ)*(1 : ℂ)) ∧
    (fun y : ℝ => p6RotatedSquareSector38 c r 2 1 y) =
      (fun y : ℝ => ((c.re-r : ℝ) : ℂ)+((-r*y+c.im : ℝ) : ℂ)*Complex.I) ∧
    (fun y : ℝ => p6RotatedSquareSector38 c r 3 1 y) =
      (fun y : ℝ => ((c.im-r : ℝ) : ℂ)*Complex.I+((r*y+c.re : ℝ) : ℂ)*(1 : ℂ)) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    rw [p6Rotated_sector_square_curve38]
    funext y
    apply Complex.ext <;> norm_num [pow_succ,Complex.mul_re,Complex.mul_im] <;> ring

end
end NlsGge.GK38
