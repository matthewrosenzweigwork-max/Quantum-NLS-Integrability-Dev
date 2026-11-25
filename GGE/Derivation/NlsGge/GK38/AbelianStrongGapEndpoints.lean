import NlsGge.GK38.AbelianRealGapSquareContinuity
import NlsGge.GK38.XiSqTauRatio
import Mathlib.Analysis.Complex.OperatorNorm

/-! Uncompiled strong sequence realization, preserving all signed indices
and collapsed gaps. Every bundle below is constructed AFTER membership. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

def p5GapSquareL1_38 (u : PhysicalL2) : lp (fun _ : ℤ => ℝ) 1 := by
  refine ⟨p5RealGapSquare38 u,?_⟩
  apply (memℓp_gen_iff (by norm_num : 0 < (1 : ENNReal).toReal)).mpr
  have hs : Summable (fun m : ℤ => ‖p5RealGapSquare38 u m‖) :=
    (p5RealGapSquare_summable38 u).congr (fun m => by
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ p5RealGapSquare38 u m from sq_nonneg _)])
  simpa only [ENNReal.toReal_one,Real.rpow_one] using hs

theorem p5GapSquareL1_continuous38 : Continuous p5GapSquareL1_38 := by
  apply continuous_iff_continuousAt.mpr
  intro u₀
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he (u : PhysicalL2) : ‖p5GapSquareL1_38 u-p5GapSquareL1_38 u₀‖ =
      ∑' m : ℤ, |p5RealGapSquare38 u m-p5RealGapSquare38 u₀ m| := by
    have hn := lp.norm_rpow_eq_tsum (by norm_num : 0 < (1 : ENNReal).toReal)
      (p5GapSquareL1_38 u-p5GapSquareL1_38 u₀)
    simpa only [ENNReal.toReal_one,Real.rpow_one,lp.coeFn_sub,Pi.sub_apply,
      p5GapSquareL1_38,Real.norm_eq_abs] using hn
  simpa only [he] using p5RealGapSquare_strong_tendsto38 u₀

def p5RealGapWidth38 (u : PhysicalL2) (m : ℤ) : ℝ :=
  actualGapUpperAllE02_38 u m-actualGapLowerAllE02_38 u m

theorem p5RealGapWidth_nonneg38 (u : PhysicalL2) (m : ℤ) : 0 ≤ p5RealGapWidth38 u m := by
  have h := periodic_pair_re_order38 u m
  rw [(lamPlus_real u m).1,(lamPlus_real u m).2] at h
  exact sub_nonneg.mpr (by simpa only [Complex.ofReal_re] using h)

theorem p5RealGapWidth_sqrt38 (u : PhysicalL2) (m : ℤ) :
    Real.sqrt (p5RealGapSquare38 u m) = p5RealGapWidth38 u m :=
  Real.sqrt_sq (p5RealGapWidth_nonneg38 u m)

def p5GapWidthL2_38 (u : PhysicalL2) : lp (fun _ : ℤ => ℝ) 2 := by
  refine ⟨p5RealGapWidth38 u,?_⟩
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
  have hs : Summable (fun m : ℤ => p5RealGapWidth38 u m^2) := p5RealGapSquare_summable38 u
  have hn : Summable (fun m : ℤ => ‖p5RealGapWidth38 u m‖^2) :=
    hs.congr (fun m => by rw [Real.norm_eq_abs,sq_abs])
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hn

theorem p5GapWidthL2_norm_sub_sq_le38 (u v : PhysicalL2) :
    ‖p5GapWidthL2_38 u-p5GapWidthL2_38 v‖^2 ≤
      ∑' m : ℤ, |p5RealGapSquare38 u m-p5RealGapSquare38 v m| := by
  have hsRight : Summable (fun m : ℤ => |p5RealGapSquare38 u m-p5RealGapSquare38 v m|) := by
    apply ((p5RealGapSquare_summable38 u).add (p5RealGapSquare_summable38 v)).of_nonneg_of_le
      (fun _ => abs_nonneg _)
    intro m
    have h := norm_sub_le (p5RealGapSquare38 u m) (p5RealGapSquare38 v m)
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ p5RealGapSquare38 u m from sq_nonneg _),
      abs_of_nonneg (show 0 ≤ p5RealGapSquare38 v m from sq_nonneg _)] using h
  have hsLeft : Summable (fun m : ℤ =>
      (p5RealGapWidth38 u m-p5RealGapWidth38 v m)^2) := by
    have hs := (lp.memℓp (p5GapWidthL2_38 u-p5GapWidthL2_38 v)).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,lp.coeFn_sub,Pi.sub_apply,
      p5GapWidthL2_38,Real.norm_eq_abs,sq_abs] using hs
  have hn := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)
    (p5GapWidthL2_38 u-p5GapWidthL2_38 v)
  have he : ‖p5GapWidthL2_38 u-p5GapWidthL2_38 v‖^2 =
      ∑' m : ℤ, (p5RealGapWidth38 u m-p5RealGapWidth38 v m)^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,lp.coeFn_sub,Pi.sub_apply,
      p5GapWidthL2_38,Real.norm_eq_abs,sq_abs] using hn
  rw [he]
  apply Summable.tsum_le_tsum _ hsLeft hsRight
  intro m
  have hh := p5Sqrt_sub_sq_le_abs_sub38 (p5RealGapSquare38 u m) (p5RealGapSquare38 v m)
    (sq_nonneg _) (sq_nonneg _)
  simpa only [p5RealGapWidth_sqrt38] using hh

theorem p5GapWidthL2_continuous38 : Continuous p5GapWidthL2_38 := by
  apply continuous_iff_continuousAt.mpr
  intro u₀
  have hsq : Tendsto (fun u : PhysicalL2 => ‖p5GapWidthL2_38 u-p5GapWidthL2_38 u₀‖^2)
      (𝓝 u₀) (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun u => p5GapWidthL2_norm_sub_sq_le38 u u₀)
      (p5RealGapSquare_strong_tendsto38 u₀)
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun u : PhysicalL2 => Real.sqrt (‖p5GapWidthL2_38 u-p5GapWidthL2_38 u₀‖^2))
    (𝓝 u₀) (𝓝 (Real.sqrt 0)) at ht
  have he : (fun u : PhysicalL2 => Real.sqrt (‖p5GapWidthL2_38 u-p5GapWidthL2_38 u₀‖^2)) =
      (fun u : PhysicalL2 => ‖p5GapWidthL2_38 u-p5GapWidthL2_38 u₀‖) :=
    funext (fun _ => Real.sqrt_sq (norm_nonneg _))
  rw [he,Real.sqrt_zero] at ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht

def p5FullRealPart38 : Lib.L2Z →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  lp.mapCLM 2 (fun _ : ℤ => Complex.reCLM) zero_le_one
    (fun _ => by rw [Complex.reCLM_norm])

def p5TauRealShiftL2_38 (u : PhysicalL2) : lp (fun _ : ℤ => ℝ) 2 :=
  p5FullRealPart38 (a5TauShift38 (realSlice u))

theorem p5TauRealShiftL2_continuous38 : Continuous p5TauRealShiftL2_38 := by
  apply continuous_iff_continuousAt.mpr
  intro u₀
  exact p5FullRealPart38.continuous.continuousAt.comp
    ((a5TauShift_analytic38 (realSlice u₀) (realSlice_mem_gkW u₀)).continuousAt.comp
      continuous_realSlice.continuousAt)

theorem p5TauRealShiftL2_value38 (u : PhysicalL2) (m : ℤ) :
    p5TauRealShiftL2_38 u m =
      (actualGapLowerAllE02_38 u m+actualGapUpperAllE02_38 u m)/2-(m : ℝ)*Real.pi := by
  change (a5TauShift38 (realSlice u) m).re = _
  rw [a5TauShift_value38 (realSlice u) (realSlice_mem_gkW u) m,(tauGamma_real38 u m).1]
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.intCast_re,
    Complex.ofReal_im,Complex.intCast_im,mul_zero,sub_zero]

def p5RealGapLowerShift38 (u : PhysicalL2) : lp (fun _ : ℤ => ℝ) 2 :=
  p5TauRealShiftL2_38 u-(1/2 : ℝ) • p5GapWidthL2_38 u

def p5RealGapUpperShift38 (u : PhysicalL2) : lp (fun _ : ℤ => ℝ) 2 :=
  p5TauRealShiftL2_38 u+(1/2 : ℝ) • p5GapWidthL2_38 u

theorem p5RealGapLowerShift_value38 (u : PhysicalL2) (m : ℤ) :
    p5RealGapLowerShift38 u m = actualGapLowerAllE02_38 u m-(m : ℝ)*Real.pi := by
  change p5TauRealShiftL2_38 u m-(1/2 : ℝ)*p5RealGapWidth38 u m = _
  rw [p5TauRealShiftL2_value38]
  dsimp only [p5RealGapWidth38]
  ring

theorem p5RealGapUpperShift_value38 (u : PhysicalL2) (m : ℤ) :
    p5RealGapUpperShift38 u m = actualGapUpperAllE02_38 u m-(m : ℝ)*Real.pi := by
  change p5TauRealShiftL2_38 u m+(1/2 : ℝ)*p5RealGapWidth38 u m = _
  rw [p5TauRealShiftL2_value38]
  dsimp only [p5RealGapWidth38]
  ring

theorem p5RealGapLowerShift_continuous38 : Continuous p5RealGapLowerShift38 := by
  have hc : Continuous (fun _ : PhysicalL2 => (1/2 : ℝ)) := continuous_const
  exact p5TauRealShiftL2_continuous38.sub (hc.smul p5GapWidthL2_continuous38)

theorem p5RealGapUpperShift_continuous38 : Continuous p5RealGapUpperShift38 := by
  have hc : Continuous (fun _ : PhysicalL2 => (1/2 : ℝ)) := continuous_const
  exact p5TauRealShiftL2_continuous38.add (hc.smul p5GapWidthL2_continuous38)

end
end NlsGge.GK38
