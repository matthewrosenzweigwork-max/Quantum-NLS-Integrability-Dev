import NlsGge.GK38.ActionGradientQuotient
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.Pilot
namespace NlsGge.GK38.ActionGradient
noncomputable section

theorem root_parameter_hasFDeriv (φ : PotPair) (z : ℂ) (hp : (φ, z) ∈ rootDomain38) :
    HasFDerivAt (fun ψ : PotPair => canonRoot38 ψ z)
      (fderiv ℂ (fun ψ : PotPair => canonRoot38 ψ z) φ) φ := by
  have ha : AnalyticAt ℂ (fun ψ : PotPair => canonRoot38 ψ z) φ :=
    (canonRoot_analytic38 (φ, z) hp).comp (f := fun ψ : PotPair => (ψ, z))
      ((analyticAt_id (𝕜 := ℂ)).prod (analyticAt_const (v := z)))
  exact ha.differentiableAt.hasFDerivAt

theorem root_parameter_derivative_apply (φ : PotPair) (z : ℂ)
    (hp : (φ, z) ∈ rootDomain38) (h : PotPair) :
    fderiv ℂ (fun ψ : PotPair => canonRoot38 ψ z) φ h =
      discrim φ z / canonRoot38 φ z * gradDiscrimCLM φ z h := by
  have hr := root_parameter_hasFDeriv φ z hp
  have hd := hasFDerivAt_gradDiscrimCLM φ z
  have hmem : ∀ᶠ ψ : PotPair in 𝓝 φ, (ψ, z) ∈ rootDomain38 :=
    (isOpen_rootDomain38.preimage (continuous_id.prodMk continuous_const)).mem_nhds hp
  have he : (fun ψ : PotPair => canonRoot38 ψ z * canonRoot38 ψ z) =ᶠ[𝓝 φ]
      (fun ψ : PotPair => discrim ψ z * discrim ψ z - 4) := by
    filter_upwards [hmem] with ψ hψ
    have hs := canonRoot_sq38 ψ hψ.1 z hψ.2
    simpa only [perChar_eq, pow_two] using hs
  have hh := congrArg (fun L : PotPair →L[ℂ] ℂ => L h)
    ((hr.mul hr).unique (((hd.mul hd).sub_const (4 : ℂ)).congr_of_eventuallyEq he))
  change canonRoot38 φ z * fderiv ℂ (fun ψ : PotPair => canonRoot38 ψ z) φ h +
      canonRoot38 φ z * fderiv ℂ (fun ψ : PotPair => canonRoot38 ψ z) φ h =
    discrim φ z * gradDiscrimCLM φ z h + discrim φ z * gradDiscrimCLM φ z h at hh
  have hn := canonRoot_ne_zero38 φ hp.1 z hp.2
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hn).2
  linear_combination (1 / 2 : ℂ) * hh

theorem root_spectral_hasDeriv (φ : PotPair) (z : ℂ) (hp : (φ, z) ∈ rootDomain38) :
    HasDerivAt (canonRoot38 φ)
      (discrim φ z / canonRoot38 φ z * deriv (discrim φ) z) z := by
  have hr : HasDerivAt (canonRoot38 φ) (deriv (canonRoot38 φ) z) z :=
    ((canonRoot_analytic38 (φ, z) hp).comp
      ((analyticAt_const (v := φ)).prod (analyticAt_id (𝕜 := ℂ)))).differentiableAt.hasDerivAt
  have hd := (analyticOnNhd_discrim_z φ z (mem_univ _)).differentiableAt.hasDerivAt
  have hmem : ∀ᶠ w : ℂ in 𝓝 z, w ∈ actionCutDomain38 φ :=
    (isOpen_actionCutDomain38 φ hp.1).mem_nhds hp.2
  have he : (fun w : ℂ => canonRoot38 φ w * canonRoot38 φ w) =ᶠ[𝓝 z]
      (fun w : ℂ => discrim φ w * discrim φ w - 4) := by
    filter_upwards [hmem] with w hw
    simpa only [perChar_eq, pow_two] using canonRoot_sq38 φ hp.1 w hw
  have hh := (hr.mul hr).unique (((hd.mul hd).sub_const (4 : ℂ)).congr_of_eventuallyEq he)
  have hn := canonRoot_ne_zero38 φ hp.1 z hp.2
  apply hr.congr_deriv
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hn).2
  linear_combination (1 / 2 : ℂ) * hh

end
end NlsGge.GK38.ActionGradient
