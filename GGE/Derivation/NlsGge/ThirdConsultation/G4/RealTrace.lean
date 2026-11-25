import Mathlib
import Armstrong.Work.ActualCartesianRealTraceAction
import Armstrong.Work.ActualCartesianXYModels
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G5033Host

/- M-001 RealTrace (proof development, AUTHOR; not reviewed).  Target NlsGge/ThirdConsultation/G4/RealTrace.lean.
   Real-trace identity (Re X_n)^2 + (Re Y_n)^2 = 2 I_n on the landed X-006 family, through the public
   sourceFamily fields only.  Lemma bodies are byte-identical to proof development M001_HOST_G2G4_A01.lean.txt
   lines 24-25 and 41-77.  No #print lines. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem norm_sq_real_pair (x y a : ℝ)
    (h : ‖((x : ℂ) - Complex.I * (y : ℂ)) / (Real.sqrt 2 : ℂ)‖ ^ 2 = a) :
    x ^ 2 + y ^ 2 = 2 * a := by
  have hb : ‖(Real.sqrt 2 : ℂ)‖ ^ 2 = 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have ha : ‖(x : ℂ) - Complex.I * (y : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.mul_im]
    ring
  rw [norm_div, div_pow, hb, ha] at h
  subst h
  ring

theorem norm_sq_of_im_zero (X Y : ℂ) (hXim : X.im = 0) (hYim : Y.im = 0) (a : ℝ)
    (h : ‖(X - Complex.I * Y) / (Real.sqrt 2 : ℂ)‖ ^ 2 = a) :
    X.re ^ 2 + Y.re ^ 2 = 2 * a := by
  have hX : ((X.re : ℝ) : ℂ) = X := Complex.ext (by simp) (by simp [hXim])
  have hY : ((Y.re : ℝ) : ℂ) = Y := Complex.ext (by simp) (by simp [hYim])
  rw [← hX, ← hY] at h
  exact norm_sq_real_pair _ _ _ h

/-- XY real-trace identity for the actual X-006 family: the real parts of the scalar
Cartesian models on the real slice satisfy (Re X)^2 + (Re Y)^2 = 2 I_n. -/
theorem cartesianX_sq_add_cartesianY_sq (n : ℤ) (u : PhysicalL2) :
    (cartesianX n (realSlice u)).re ^ 2 + (cartesianY n (realSlice u)).re ^ 2 =
      2 * actualGapActionAllE02_38 u n := by
  obtain ⟨hXim, hYim, hnorm⟩ :=
    NlsGge.GK38.gk16_same_family_xy_real_trace_action38 sourceFamily.W sourceFamily.W_open
      sourceFamily.W_real sourceFamily.W_gk sourceFamily.F sourceFamily.F_analytic
      sourceFamily.F_zero sourceFamily.F_period sourceFamily.F_real sourceFamily.V
      sourceFamily.V_real sourceFamily.beta sourceFamily.beta_spec n u
  exact norm_sq_of_im_zero _ _ hXim hYim _ hnorm

end
end NlsGge.GKDefinitionDesign
