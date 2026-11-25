import NlsGge.GK38.Lib.EntireProductsParama
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! True operator norm controls ACTUAL complex lp2 diagonal coefficients.
No invertibility assumption is used to infer a diagonal lower bound. -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

theorem angleActual_diagonal_coefficient_sub_le38
    (A B : Lib.L2Seq →L[ℂ] Lib.L2Seq) (m : ℤ) :
    ‖A (lp.single 2 m (1 : ℂ)) m-B (lp.single 2 m (1 : ℂ)) m‖ ≤ ‖A-B‖ := by
  let e : Lib.L2Seq := lp.single 2 m (1 : ℂ)
  have he : ‖e‖=1 := by
    simpa only [e,norm_one] using lp.norm_single (E := fun _ : ℤ => ℂ) (by norm_num : (0 : ENNReal)<2) m (1 : ℂ)
  calc
    ‖A e m-B e m‖ = ‖((A-B) e) m‖ := rfl
    _ ≤ ‖(A-B) e‖ := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal)≠0) _ m
    _ ≤ ‖A-B‖*‖e‖ := (A-B).le_opNorm e
    _ = ‖A-B‖ := by rw [he,mul_one]

theorem angleActual_diagonal_norm_transfer38
    (A B : Lib.L2Seq →L[ℂ] Lib.L2Seq) (m : ℤ) :
    ‖A (lp.single 2 m (1 : ℂ)) m‖ ≤
      ‖B (lp.single 2 m (1 : ℂ)) m‖+‖A-B‖ := by
  let a : ℂ := A (lp.single 2 m (1 : ℂ)) m
  let b : ℂ := B (lp.single 2 m (1 : ℂ)) m
  calc
    ‖a‖ = ‖b+(a-b)‖ := by congr 1; ring
    _ ≤ ‖b‖+‖a-b‖ := norm_add_le _ _
    _ ≤ ‖b‖+‖A-B‖ := add_le_add le_rfl
      (angleActual_diagonal_coefficient_sub_le38 A B m)

end
end NlsGge.GK38
