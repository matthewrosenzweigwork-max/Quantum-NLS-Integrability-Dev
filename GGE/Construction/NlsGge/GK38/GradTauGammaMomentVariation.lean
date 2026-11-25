import NlsGge.GK38.TauGamma
import NlsGge.GK38.ActionGradientPotentialLine
import NlsGge.GK38.ActionGradientMixedDerivative
import NlsGge.GK38.ActionGradientScalarQuotient

/-! K4a: the exact mixed derivative behind the periodic-moment contour formula.
No logarithm branch, root branch or regularity beyond complex L2 is needed. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

def k4aDirectionQuotient38 (φ h : PotPair) (z : ℂ) : ℂ :=
  discrim φ z * gradDiscrimCLM φ z h / perChar φ z

theorem k4aDirectionQuotient_hasDeriv38 (φ h : PotPair) (z : ℂ)
    (hn : perChar φ z ≠ 0) :
    HasDerivAt (k4aDirectionQuotient38 φ h)
      (((deriv (discrim φ) z * gradDiscrimCLM φ z h +
          discrim φ z * fderiv ℂ (fun ψ : PotPair => deriv (discrim ψ) z) φ h) *
            perChar φ z - discrim φ z * gradDiscrimCLM φ z h *
              (2 * discrim φ z * deriv (discrim φ) z)) / perChar φ z ^ 2) z := by
  have hΔ := (analyticOnNhd_discrim_z φ z (mem_univ _)).differentiableAt.hasDerivAt
  have hD := ActionGradient.gradDiscrim_spectral_hasDeriv φ z h
  have hp := (analyticOnNhd_perChar_z φ z (mem_univ _)).differentiableAt.hasDerivAt
  rw [perChar_deriv_discrim38] at hp
  exact ActionGradient.scalar_div_hasDeriv (hΔ.mul hD) hp hn

theorem k4aMomentIntegrand_parameter_derivative38 (φ h : PotPair) (z : ℂ)
    (k : ℕ) (hn : perChar φ z ≠ 0) :
    Lib.paramCircleDerivative38 (fun ψ => momentIntegrand38 ψ k) φ z h =
      2 * z ^ k * deriv (k4aDirectionQuotient38 φ h) z := by
  have hA : AnalyticAt ℂ
      (Function.uncurry (fun ψ => momentIntegrand38 ψ k)) (φ, z) :=
    ((analyticAt_snd.pow k).mul (analyticOnNhd_perCharDeriv_joint38 (φ, z) (mem_univ _))).div
      (analyticOnNhd_perChar_joint38 (φ, z) (mem_univ _)) hn
  have hM := (Lib.paramCircle_hasFDerivAt38 hA).comp_hasDerivAt_of_eq
    (0 : ℂ) (ActionGradient.potential_line_hasDeriv φ h) (by simp)
  simp only [Function.comp_def] at hM
  have hΔ := (hasFDerivAt_gradDiscrimCLM φ z).comp_hasDerivAt_of_eq
    (0 : ℂ) (ActionGradient.potential_line_hasDeriv φ h) (by simp)
  simp only [Function.comp_def] at hΔ
  have hd := ActionGradient.discrim_spectral_line_hasDeriv φ z h
  have hp : HasDerivAt (fun t : ℂ => perChar (φ + t • h) z)
      (2 * discrim φ z * gradDiscrimCLM φ z h) 0 := by
    simpa only [perChar_eq, Pi.pow_apply, zero_smul, add_zero,
      show (2 - 1 : ℕ) = 1 from rfl, pow_one, Nat.cast_ofNat]
      using (hΔ.pow 2).sub_const (4 : ℂ)
  have hnum : HasDerivAt
      (fun t : ℂ => 2 * discrim (φ + t • h) z * deriv (discrim (φ + t • h)) z)
      (2 * (gradDiscrimCLM φ z h * deriv (discrim φ) z +
        discrim φ z * fderiv ℂ (fun ψ : PotPair => deriv (discrim ψ) z) φ h)) 0 := by
    simpa only [Pi.mul_apply, zero_smul, add_zero, mul_assoc] using (hΔ.mul hd).const_mul (2 : ℂ)
  have hcalc := ActionGradient.scalar_const_mul_div_hasDeriv (z ^ k) hnum hp
    (by simpa only [zero_smul, add_zero] using hn)
  have hfun : (fun t : ℂ => momentIntegrand38 (φ + t • h) k z) =
      (fun t : ℂ => z ^ k *
        (2 * discrim (φ + t • h) z * deriv (discrim (φ + t • h)) z) /
          perChar (φ + t • h) z) := by
    funext t
    rw [momentIntegrand38, perChar_deriv_discrim38]
  rw [← hfun] at hcalc
  have he := hM.unique hcalc
  rw [he, (k4aDirectionQuotient_hasDeriv38 φ h z hn).deriv]
  simp only [zero_smul, add_zero, div_eq_mul_inv]
  ring

end
end NlsGge.GK38
