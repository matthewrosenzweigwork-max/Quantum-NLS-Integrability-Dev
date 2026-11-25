import NlsGge.GK38.AbelianComplexHomotopyCauchy
import Mathlib.Tactic.FunProp

/-! SOURCE ONLY: actual curve and scalar pullback integrabilities BEFORE
the curve/interval integral identity. Exact target+English preceded proof.
UNCOMPILED, outside the currently released rectangle four-leaf method. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology unitInterval Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Complex_curve_integral_param38 {a b : ℂ} (γ : Path a b) (g : ℝ → ℂ)
    (hg : ContDiff ℝ 1 g) (hγ : ∀ u : I, γ u = g (u : ℝ)) (f : ℂ → ℂ)
    (hf : ContinuousOn f (g '' (Set.Icc (0 : ℝ) 1))) :
    CurveIntegrable (p6ComplexForm38 f) γ ∧
    IntervalIntegrable (fun t : ℝ => f (g t)*deriv g t) volume 0 1 ∧
    (∫ᶜ z in γ, p6ComplexForm38 f z) = ∫ t : ℝ in (0 : ℝ)..1, f (g t)*deriv g t := by
  have heq : EqOn γ.extend g (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (γ.extend_extends' ⟨t,ht⟩).trans (hγ ⟨t,ht⟩)
  have hC1 : ContDiffOn ℝ 1 γ.extend (Set.Icc (0 : ℝ) 1) :=
    hg.contDiffOn.congr heq
  have hω : ContinuousOn (p6ComplexForm38 f) (g '' (Set.Icc (0 : ℝ) 1)) :=
    (ContinuousLinearMap.mul ℂ ℂ).continuous.comp_continuousOn hf
  have hcurve : CurveIntegrable (p6ComplexForm38 f) γ :=
    hω.curveIntegrable_of_contDiffOn hC1 (fun u => ⟨(u : ℝ),u.property,(hγ u).symm⟩)
  have hfg : ContinuousOn (fun t : ℝ => f (g t)) (Set.Icc (0 : ℝ) 1) :=
    hf.comp hg.continuous.continuousOn (fun t ht => mem_image_of_mem g ht)
  have hscalar : IntervalIntegrable (fun t : ℝ => f (g t)*deriv g t) volume 0 1 :=
    (hfg.mul hg.continuous_deriv_one.continuousOn).intervalIntegrable_of_Icc zero_le_one
  refine ⟨hcurve,hscalar,?_⟩
  rw [curveIntegral_eq_intervalIntegral_deriv]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro t ht
  have hevent : γ.extend =ᶠ[𝓝 t] g := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact heq (Ioo_subset_Icc_self hu)
  change (p6ComplexForm38 f (γ.extend t)) (deriv γ.extend t) = f (g t)*deriv g t
  rw [heq (Ioo_subset_Icc_self ht), hevent.deriv_eq]
  rfl

end
end NlsGge.GK38
