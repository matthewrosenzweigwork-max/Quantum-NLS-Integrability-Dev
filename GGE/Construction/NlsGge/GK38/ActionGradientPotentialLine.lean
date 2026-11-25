import NlsGge.GK38.ActionGradientRootVariation

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.Pilot
namespace NlsGge.GK38.ActionGradient
noncomputable section

theorem potential_line_hasDeriv (φ h : PotPair) :
    HasDerivAt (fun t : ℂ => φ + t • h) h 0 := by
  convert (hasDerivAt_const (0 : ℂ) φ).add ((hasDerivAt_id (0 : ℂ)).smul_const h) using 1 <;>
    (first | rfl | simp only [one_smul, zero_add])

theorem discrim_spectral_line_hasDeriv (φ : PotPair) (z : ℂ) (h : PotPair) :
    HasDerivAt (fun t : ℂ => deriv (discrim (φ + t • h)) z)
      (fderiv ℂ (fun ψ : PotPair => deriv (discrim ψ) z) φ h) 0 := by
  have ha : AnalyticAt ℂ (fun ψ : PotPair => deriv (discrim ψ) z) φ :=
    (NlsGge.GK38.analyticOnNhd_discrimDeriv_joint38 (φ, z) (mem_univ _)).comp
      (f := fun ψ : PotPair => (ψ, z))
      ((analyticAt_id (𝕜 := ℂ)).prod (analyticAt_const (v := z)))
  have hd := ha.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℂ) (potential_line_hasDeriv φ h) (by simp)
  simpa only [Function.comp_def] using hd

theorem root_line_hasDeriv (φ : PotPair) (z : ℂ) (hp : (φ, z) ∈ rootDomain38) (h : PotPair) :
    HasDerivAt (fun t : ℂ => canonRoot38 (φ + t • h) z)
      (discrim φ z / canonRoot38 φ z * gradDiscrimCLM φ z h) 0 := by
  have hd := (root_parameter_hasFDeriv φ z hp).comp_hasDerivAt_of_eq
    (0 : ℂ) (potential_line_hasDeriv φ h) (by simp)
  rw [root_parameter_derivative_apply φ z hp h] at hd
  simpa only [Function.comp_def] using hd

theorem actionIntegrand_line_hasDeriv (φ : PotPair) (z : ℂ)
    (hp : (φ, z) ∈ rootDomain38) (h : PotPair) :
    HasDerivAt (fun t : ℂ => actionIntegrand38 (φ + t • h) z)
      (NlsGge.GK38.Lib.paramCircleDerivative38 actionIntegrand38 φ z h) 0 := by
  have ha := NlsGge.GK38.Lib.paramCircle_hasFDerivAt38
    (F := actionIntegrand38) (actionIntegrand_joint_analytic38 (φ, z) hp)
  have hd := ha.comp_hasDerivAt_of_eq (0 : ℂ) (potential_line_hasDeriv φ h) (by simp)
  simpa only [Function.comp_def] using hd

end
end NlsGge.GK38.ActionGradient
