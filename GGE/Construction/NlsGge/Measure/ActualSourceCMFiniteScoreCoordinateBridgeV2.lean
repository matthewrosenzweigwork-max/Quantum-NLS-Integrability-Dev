import NlsGge.Measure.WeightedModes
import NlsGge.Sobolev.CMWeightComparison

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace

namespace NlsGge.Measure

/-- The public coordinate identity needed by the finite Cameron--Martin score:
the mode map pairs with the actual CM inclusion by the source CM weight. -/
theorem actualSourceCMFiniteScore_mode_inner_coordinate_v2
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c))
    (n : ℤ) (z : ℂ) :
    inner ℝ (fullWeightedModeMap c 0 n z)
        (NlsGge.Pilot.cmToFullWeightedHilbert c 0 (by norm_num) x) =
      NlsGge.Pilot.sourceRate c n * inner ℝ z
        ((show NlsGge.Pilot.WeightedHilbert
          (NlsGge.Pilot.cmModeWeight c) from x) n) := by
  let w := NlsGge.Pilot.fullModeWeight c 0
  let e := NlsGge.Pilot.weightedIsometry w
  let a : ℂ := (Real.sqrt (w n) : ℂ)
  let y : NlsGge.Pilot.WeightedHilbert w :=
    NlsGge.Pilot.cmToFullWeightedHilbert c 0 (by norm_num) x
  have h := e.inner_map_map (e.symm (lp.single 2 n (a * z))) y
  change (inner ℂ (e.symm (lp.single 2 n (a * z))) y).re = _
  rw [LinearIsometryEquiv.apply_symm_apply, lp.inner_single_left] at h
  rw [← congrArg Complex.re h]
  change (inner ℂ (a * z) (a * y n)).re = _
  have ha : star a = a := by simp [a]
  have haa : a * a = (w n : ℂ) := by
    dsimp [a]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt
      (NlsGge.Pilot.fullModeWeight_pos c 0 n).le]
  have hcomplex : inner ℂ (a * z) (a * y n) =
      (w n : ℂ) * inner ℂ z (y n) := by
    change inner ℂ (a • z) (a • y n) = _
    rw [inner_smul_left, inner_smul_right]
    change star a * (a * inner ℂ z (y n)) = _
    rw [ha, ← mul_assoc, haa]
  rw [hcomplex]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [NlsGge.Pilot.cmToFullWeightedHilbert_apply]
  simp [w, NlsGge.Pilot.fullModeWeight, NlsGge.Pilot.sourceRate]

end NlsGge.Measure
