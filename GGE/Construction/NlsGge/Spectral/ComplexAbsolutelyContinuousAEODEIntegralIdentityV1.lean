import NlsGge.Spectral.ComplexIntervalIntegralPrimitiveAbsolutelyContinuousV2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.SpectralFoundations

/-- An absolutely continuous complex function with an integrable AE
derivative satisfies the actual primitive identity. This supplies the
rough-field ODE-to-Volterra bridge without assuming a classical derivative
at every point. -/
theorem complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt
    {f g : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntervalIntegrable g volume a b)
    (hder : ∀ᵐ x ∂volume, x ∈ Set.uIcc a b → HasDerivAt f (g x) x) :
    ∀ x ∈ Set.uIcc a b, f x = f a + ∫ t in a..x, g t := by
  let G : ℝ → ℂ := fun x => f x - ∫ t in a..x, g t
  have hprim := complex_intervalIntegral_primitive_absolutelyContinuousV2 hg
    (Set.left_mem_uIcc : a ∈ Set.uIcc a b)
  have hG : AbsolutelyContinuousOnInterval G a b := hf.sub hprim
  have hzero : ∀ᵐ x ∂volume, x ∈ Set.uIcc a b → HasDerivAt G 0 x := by
    filter_upwards [hder, hg.ae_hasDerivAt_integral] with x hx hix
    intro hmem
    simpa only [G, sub_self] using! (hx hmem).sub
      (hix hmem a (Set.left_mem_uIcc : a ∈ Set.uIcc a b))
  obtain ⟨C, hC⟩ := hG.const_of_ae_hasDerivAt_zero hzero
  have hCa : C = f a := by
    have ha := hC a (Set.left_mem_uIcc : a ∈ Set.uIcc a b)
    simpa only [G, intervalIntegral.integral_same, sub_zero] using ha.symm
  intro x hx
  have h := (hC x hx).trans hCa
  exact sub_eq_iff_eq_add.mp h
end NlsGge.SpectralFoundations
end
