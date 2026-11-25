import NlsGge.GK38.AbelianFreeDerivative
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Complex.OperatorNorm

/-! Concrete omitted real lp2, using the pinned uniformly bounded lp.mapCLM API.
UNCOMPILED source preparation. The prior manual source snapshot is retained. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

abbrev P3RealSpace38 (n : ℤ) : Type := lp (fun _ : P2Index38 n => ℝ) 2

def p3RealIncludeCLM38 (n : ℤ) : P3RealSpace38 n →L[ℝ] P2Space38 n :=
  lp.mapCLM 2 (fun _ : P2Index38 n => Complex.ofRealCLM) zero_le_one
    (fun _ => by rw [Complex.ofRealCLM_norm])

@[simp] theorem p3RealIncludeCLM_apply38 (n : ℤ) (s : P3RealSpace38 n)
    (m : P2Index38 n) : p3RealIncludeCLM38 n s m = (s m : ℂ) := rfl

theorem p3RealIncludeCLM_norm38 (n : ℤ) (s : P3RealSpace38 n) :
    ‖p3RealIncludeCLM38 n s‖ = ‖s‖ := by
  have hr := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) s
  have hc := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)
    (p3RealIncludeCLM38 n s)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hr
  simp only [ENNReal.toReal_ofNat, Real.rpow_two,
    p3RealIncludeCLM_apply38, Complex.norm_real] at hc
  have hsq : ‖p3RealIncludeCLM38 n s‖ ^ 2 = ‖s‖ ^ 2 := hc.trans hr.symm
  nlinarith [norm_nonneg (p3RealIncludeCLM38 n s), norm_nonneg s]

def p3RealInclude38 (n : ℤ) : P3RealSpace38 n →ₗᵢ[ℝ] P2Space38 n where
  __ := (p3RealIncludeCLM38 n).toLinearMap
  norm_map' := p3RealIncludeCLM_norm38 n

@[simp] theorem p3RealInclude_apply38 (n : ℤ) (s : P3RealSpace38 n)
    (m : P2Index38 n) : p3RealInclude38 n s m = (s m : ℂ) := rfl

def p3RealPart38 (n : ℤ) : P2Space38 n →L[ℝ] P3RealSpace38 n :=
  lp.mapCLM 2 (fun _ : P2Index38 n => Complex.reCLM) zero_le_one
    (fun _ => by rw [Complex.reCLM_norm])

@[simp] theorem p3RealPart_apply38 (n : ℤ) (s : P2Space38 n) (m : P2Index38 n) :
    p3RealPart38 n s m = (s m).re := rfl

theorem p3RealPart_norm_le_one38 (n : ℤ) : ‖p3RealPart38 n‖ ≤ 1 :=
  lp.norm_mapCLM_le 2 (fun _ : P2Index38 n => Complex.reCLM) zero_le_one
    (fun _ => by rw [Complex.reCLM_norm])

@[simp] theorem p3RealPart_include38 (n : ℤ) (s : P3RealSpace38 n) :
    p3RealPart38 n (p3RealInclude38 n s) = s := by
  apply Subtype.ext
  funext m
  exact Complex.ofReal_re (s m)

theorem p3RealInclude_realPart38 (n : ℤ) (s : P2Space38 n) (hs : p2RealSeq38 n s) :
    p3RealInclude38 n (p3RealPart38 n s) = s := by
  apply Subtype.ext
  funext m
  change (((s m).re : ℝ) : ℂ) = s m
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simp only [Complex.ofReal_im, hs m]

/-- The canonical lp2 basis on the actual real omitted space. -/
def p3RealHilbertBasis38 (n : ℤ) : HilbertBasis (P2Index38 n) ℝ (P3RealSpace38 n) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)

/-- Source coefficients and the HS basis use exactly the same real unit vectors. -/
theorem p3RealHilbertBasis_apply38 (n : ℤ) (r : P2Index38 n) :
    p3RealHilbertBasis38 n r = lp.single 2 r (1 : ℝ) := by
  classical
  simpa only [p3RealHilbertBasis38, LinearIsometryEquiv.coe_refl] using!
    (p3RealHilbertBasis38 n).repr_self r

end
end NlsGge.GK38
