import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations

/-- Complex primitive absolute continuity follows from the actual real and
imaginary primitives; no pointwise continuity of the integrand is assumed. -/
theorem complex_intervalIntegral_primitive_absolutelyContinuousV2
    {g : ℝ → ℂ} {a b c : ℝ}
    (hg : IntervalIntegrable g volume a b) (hc : c ∈ Set.uIcc a b) :
    AbsolutelyContinuousOnInterval (fun t => ∫ s in c..t, g s) a b := by
  have hre : IntervalIntegrable (fun s => (g s).re) volume a b :=
    intervalIntegrable_iff.mpr (Complex.reCLM.integrable_comp hg.def')
  have him : IntervalIntegrable (fun s => (g s).im) volume a b :=
    intervalIntegrable_iff.mpr (Complex.imCLM.integrable_comp hg.def')
  have hR := Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval
    (hre.absolutelyContinuousOnInterval_intervalIntegral hc)
  have hI := Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval
    (him.absolutelyContinuousOnInterval_intervalIntegral hc)
  have hR' : AbsolutelyContinuousOnInterval
      (fun t => Complex.ofReal (∫ s in c..t, (g s).re)) a b := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using hR
  have hI' : AbsolutelyContinuousOnInterval
      (fun t => Complex.ofReal (∫ s in c..t, (g s).im)) a b := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using hI
  apply (hR'.add (hI'.const_smul Complex.I)).congr
  intro t ht
  have hgt : IntervalIntegrable g volume c t := hg.mono_set (Set.uIcc_subset_uIcc hc ht)
  change Complex.ofReal (∫ s in c..t, (g s).re) +
    Complex.I • Complex.ofReal (∫ s in c..t, (g s).im) = ∫ s in c..t, g s
  have hreal : (∫ s in c..t, (g s).re) = (∫ s in c..t, g s).re := by
    simpa only [Complex.reCLM_apply] using Complex.reCLM.intervalIntegral_comp_comm hgt
  have himag : (∫ s in c..t, (g s).im) = (∫ s in c..t, g s).im := by
    simpa only [Complex.imCLM_apply] using Complex.imCLM.intervalIntegral_comp_comm hgt
  rw [hreal, himag]
  simpa only [smul_eq_mul, mul_comm Complex.I] using Complex.re_add_im (∫ s in c..t, g s)
end NlsGge.SpectralFoundations
end
