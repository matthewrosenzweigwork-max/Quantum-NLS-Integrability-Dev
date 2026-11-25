import NlsGge.Spectral.ComplexAbsolutelyContinuousAEODEIntegralIdentityV1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.SpectralFoundations

/-- Existing pointwise-differentiable tests with integrable derivative are
absolutely continuous; no new AC hypothesis is imposed on the test class. -/
theorem complex_test_absolutelyContinuous_of_hasDerivAt_integrable
    {ψ ψ' : ℝ → ℂ} {a b : ℝ}
    (hψ : ∀ t ∈ Set.uIcc a b, HasDerivAt ψ (ψ' t) t)
    (hψint : IntervalIntegrable ψ' volume a b) :
    AbsolutelyContinuousOnInterval ψ a b := by
  have hp := complex_intervalIntegral_primitive_absolutelyContinuousV2 hψint
    (Set.left_mem_uIcc : a ∈ Set.uIcc a b)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => ψ a) a b := by
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    refine ⟨1, by norm_num, ?_⟩
    intro E hE hlen
    simpa using hε
  have hac : AbsolutelyContinuousOnInterval
      (fun t => ψ a + ∫ s in a..t, ψ' s) a b :=
    hc.add hp
  apply hac.congr
  intro t ht
  have hi : IntervalIntegrable ψ' volume a t :=
    hψint.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc ht)
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hψ x ((Set.uIcc_subset_uIcc Set.left_mem_uIcc ht) hx)) hi
  change ψ a + (∫ s in a..t, ψ' s) = ψ t
  rw [heq]
  ring

/-- Complex bilinear integration by parts for an AC function and the exact
pointwise differentiable/integrable test regularity used by the source weak
derivative definition. The boundary term is explicit. -/
theorem complex_ac_pointwise_test_integration_by_parts
    {f g ψ ψ' : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntervalIntegrable g volume a b)
    (hder : ∀ᵐ t ∂volume, t ∈ Set.uIcc a b → HasDerivAt f (g t) t)
    (hψ : ∀ t ∈ Set.uIcc a b, HasDerivAt ψ (ψ' t) t)
    (hψint : IntervalIntegrable ψ' volume a b) :
    (∫ t in a..b, f t * ψ' t) =
      f b * ψ b - f a * ψ a - ∫ t in a..b, g t * ψ t := by
  have hψac := complex_test_absolutelyContinuous_of_hasDerivAt_integrable hψ hψint
  have hprod : AbsolutelyContinuousOnInterval (fun t => f t * ψ t) a b := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! hf.smul hψac
  have hgψ : IntervalIntegrable (fun t => g t * ψ t) volume a b :=
    hg.mul_continuousOn hψac.continuousOn
  have hfψ' : IntervalIntegrable (fun t => f t * ψ' t) volume a b :=
    hψint.continuousOn_mul hf.continuousOn
  have hdprod : ∀ᵐ t ∂volume, t ∈ Set.uIcc a b →
      HasDerivAt (fun s => f s * ψ s) (g t * ψ t + f t * ψ' t) t := by
    filter_upwards [hder] with t ht
    intro hmem
    exact (ht hmem).mul (hψ t hmem)
  have heq := complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt
    hprod (hgψ.add hfψ') hdprod b Set.right_mem_uIcc
  rw [intervalIntegral.integral_add hgψ hfψ'] at heq
  linear_combination -heq

end NlsGge.SpectralFoundations
end
