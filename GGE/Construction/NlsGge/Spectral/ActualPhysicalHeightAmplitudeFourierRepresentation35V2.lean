import NlsGge.Measure.ActualPhysicalBoundedHeightAmplitudeLp1Classes35V2
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Truncated full-volume Fourier input is the genuine interval integral,
including the library's exact negative two-pi convention. -/
theorem fourier_indicator_Ioc_interval35 (f : ℝ → ℂ) (s ξ : ℝ) (hs : 0 ≤ s) :
    FourierTransform.fourier (Set.indicator (Set.Ioc (0 : ℝ) s) f) ξ =
      ∫ r in (0 : ℝ)..s,
        Complex.exp (((-2*Real.pi*r*ξ : ℝ) : ℂ)*Complex.I)*f r := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    intervalIntegral.integral_of_le hs]
  have hfun : (fun r : ℝ =>
      Complex.exp (((-2*Real.pi*r*ξ : ℝ) : ℂ)*Complex.I) •
        Set.indicator (Set.Ioc (0 : ℝ) s) f r) =
      Set.indicator (Set.Ioc (0 : ℝ) s)
        (fun r => Complex.exp (((-2*Real.pi*r*ξ : ℝ) : ℂ)*Complex.I)*f r) := by
    funext r
    by_cases hr : r ∈ Set.Ioc (0 : ℝ) s <;> simp [Set.indicator,hr,smul_eq_mul]
  rw [hfun,integral_indicator measurableSet_Ioc]

/-- The actual 00-channel L¹ class has the exact truncated weighted-source
Fourier integral. Integrability and its a.e. representative were realized
before this identity; no compactness or uniform-decay premise is assumed. -/
theorem actualPhysicalHeightAmplitude00Lp1_fourierRepresentation35
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) (ξ : ℝ) :
    Real.Lp.fourierTransformCLM ℝ ℂ
        (actualPhysicalHeightAmplitude00Lp1_35V2 u Y₀ hY₀ p) ξ =
      ∫ r in (0 : ℝ)..(p.1 : ℝ),
        Complex.exp (((-2*Real.pi*r*ξ : ℝ) : ℂ)*Complex.I)*
          (star (actualPhysicalL2SourcePotential u r)*
            Complex.exp ((2*(p.2 : ℝ)*r : ℝ) : ℂ)) := by
  change Real.Lp.fourierTransform
    (actualPhysicalHeightAmplitude00Lp1_35V2 u Y₀ hY₀ p) ξ = _
  rw [Real.Lp.fourierTransform_apply,
    Real.fourier_congr_ae (actualPhysicalHeightAmplitude00Lp1_35V2_coe_ae u Y₀ hY₀ p)]
  exact fourier_indicator_Ioc_interval35 _ _ _ p.1.2.1

/-- The opposite channel retains the unstarred actual source and negative
real height weight with the same exact Fourier convention. -/
theorem actualPhysicalHeightAmplitude11Lp1_fourierRepresentation35
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) (ξ : ℝ) :
    Real.Lp.fourierTransformCLM ℝ ℂ
        (actualPhysicalHeightAmplitude11Lp1_35V2 u Y₀ hY₀ p) ξ =
      ∫ r in (0 : ℝ)..(p.1 : ℝ),
        Complex.exp (((-2*Real.pi*r*ξ : ℝ) : ℂ)*Complex.I)*
          (actualPhysicalL2SourcePotential u r*
            Complex.exp ((-2*(p.2 : ℝ)*r : ℝ) : ℂ)) := by
  change Real.Lp.fourierTransform
    (actualPhysicalHeightAmplitude11Lp1_35V2 u Y₀ hY₀ p) ξ = _
  rw [Real.Lp.fourierTransform_apply,
    Real.fourier_congr_ae (actualPhysicalHeightAmplitude11Lp1_35V2_coe_ae u Y₀ hY₀ p)]
  exact fourier_indicator_Ioc_interval35 _ _ _ p.1.2.1

end NlsGge.SpectralFoundations
end
