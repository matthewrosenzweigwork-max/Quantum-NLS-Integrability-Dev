import NlsGge.GK38.ActionGradientPotentialLine
import NlsGge.GK38.ActionGradientMixedDerivative
import NlsGge.GK38.ActionGradientCircleIBP
import NlsGge.GK38.ActionGradientScalarQuotient

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.Pilot
namespace NlsGge.GK38.ActionGradient
noncomputable section

theorem actionIntegrand_parameter_derivative (φ : PotPair) (z : ℂ)
    (hp : (φ, z) ∈ rootDomain38) (h : PotPair) :
    NlsGge.GK38.Lib.paramCircleDerivative38 actionIntegrand38 φ z h =
      z * deriv (directionQuotient φ h) z := by
  have hn := canonRoot_ne_zero38 φ hp.1 z hp.2
  have hNL := discrim_spectral_line_hasDeriv φ z h
  have hRL := root_line_hasDeriv φ z hp h
  have hAL := actionIntegrand_line_hasDeriv φ z hp h
  have hcalc : HasDerivAt (fun t : ℂ =>
      (z * deriv (discrim (φ + t • h)) z) / canonRoot38 (φ + t • h) z)
      ((z * fderiv ℂ (fun ψ : PotPair => deriv (discrim ψ) z) φ h * canonRoot38 φ z -
        (z * deriv (discrim φ) z) *
          (discrim φ z / canonRoot38 φ z * gradDiscrimCLM φ z h)) /
        canonRoot38 φ z ^ 2) 0 := by
    simpa only [zero_smul, add_zero] using
      scalar_const_mul_div_hasDeriv z hNL hRL
        (by simpa only [zero_smul, add_zero] using hn)
  have he := hAL.unique hcalc
  have hq := scalar_div_hasDeriv (gradDiscrim_spectral_hasDeriv φ z h)
    (root_spectral_hasDeriv φ z hp) hn
  have hd : deriv (directionQuotient φ h) z =
      (fderiv ℂ (fun ψ : PotPair => deriv (discrim ψ) z) φ h * canonRoot38 φ z -
        gradDiscrimCLM φ z h * (discrim φ z / canonRoot38 φ z * deriv (discrim φ) z)) /
        canonRoot38 φ z ^ 2 := hq.deriv
  rw [he, hd]
  simp only [div_eq_mul_inv]
  ring

end
end NlsGge.GK38.ActionGradient
