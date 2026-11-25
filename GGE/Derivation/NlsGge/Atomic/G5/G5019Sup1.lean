import Mathlib

/- G5-019 SUPPORT 1 `G5019Sup1` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5019Sup1.lean, namespace NlsGge.GKDefinitionDesign.G5019Sup1.
   dslope at a fixed base point of a jointly entire function is jointly continuous (segment-integral formula). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory

namespace NlsGge.GKDefinitionDesign
namespace G5019Sup1
noncomputable section

theorem dslope_eq_integral (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) (a b : ℂ) :
    dslope f a b = ∫ t in (0 : ℝ)..1, deriv f (a + (t : ℂ) * (b - a)) := by
  by_cases hab : b = a
  · subst hab
    simp [dslope_same]
  · have hder : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (a + (s : ℂ) * (b - a)))
        ((b - a) * deriv f (a + (t : ℂ) * (b - a))) t := by
      intro t
      have h1 : HasDerivAt (fun z : ℂ => a + z * (b - a)) (b - a) (t : ℂ) := by
        simpa using ((hasDerivAt_id (t : ℂ)).mul_const (b - a)).const_add a
      have h2 : HasDerivAt f (deriv f (a + (t : ℂ) * (b - a))) (a + (t : ℂ) * (b - a)) :=
        (hf _ (mem_univ _)).differentiableAt.hasDerivAt
      have h3 : HasDerivAt (fun z : ℂ => f (a + z * (b - a)))
          ((b - a) * deriv f (a + (t : ℂ) * (b - a))) (t : ℂ) := by
        have := h2.scomp (t : ℂ) h1
        simpa [Function.comp_def] using this
      exact h3.comp_ofReal
    have hd : Continuous (deriv f) := continuousOn_univ.mp hf.deriv.continuousOn
    have hcont : Continuous (fun t : ℝ => deriv f (a + (t : ℂ) * (b - a))) :=
      hd.comp (by fun_prop)
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
      (fun t _ => hder t) ((continuous_const.mul hcont).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul] at hint
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero,
      add_sub_cancel] at hint
    rw [dslope_of_ne _ hab, slope_def_field]
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
    rw [div_eq_iff hba, mul_comm]
    exact hint.symm

theorem deriv_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (J : E × ℂ → ℂ)
    (hJ : AnalyticOnNhd ℂ J univ) (x : E) (w : ℂ) :
    deriv (fun z : ℂ => J (x, z)) w = fderiv ℂ J (x, w) (0, 1) := by
  have h1 : HasDerivAt (fun z : ℂ => ((x, z) : E × ℂ)) ((0 : E), (1 : ℂ)) w :=
    (hasDerivAt_const w x).prodMk (hasDerivAt_id w)
  have h2 : HasFDerivAt J (fderiv ℂ J (x, w)) (x, w) :=
    (hJ (x, w) (mem_univ _)).differentiableAt.hasFDerivAt
  exact (h2.comp_hasDerivAt w h1).deriv

theorem dslope_symm (f : ℂ → ℂ) (a b : ℂ) : dslope f a b = dslope f b a := by
  by_cases h : a = b
  · rw [h]
  · rw [dslope_of_ne _ (Ne.symm h), dslope_of_ne _ h, slope_comm]

theorem continuous_dslope_fixed_base {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E × ℂ → ℂ) (hJ : AnalyticOnNhd ℂ J univ) (c : ℂ) :
    Continuous (fun p : E × ℂ => dslope (fun z : ℂ => J (p.1, z)) c p.2) := by
  have hslice : ∀ x : E, AnalyticOnNhd ℂ (fun z : ℂ => J (x, z)) univ := fun x z _ =>
    (hJ (x, z) (mem_univ _)).comp (analyticAt_const.prod analyticAt_id)
  have hD : Continuous (fun q : E × ℂ => fderiv ℂ J q (0, 1)) :=
    (continuousOn_univ.mp hJ.fderiv.continuousOn).clm_apply continuous_const
  have hK : Continuous (Function.uncurry (fun (p : E × ℂ) (t : ℝ) =>
      fderiv ℂ J (p.1, c + (t : ℂ) * (p.2 - c)) (0, 1))) :=
    hD.comp (by fun_prop)
  have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := MeasureTheory.volume) hK 0 1
  convert this using 1
  ext p
  rw [dslope_eq_integral _ (hslice p.1) c p.2]
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact deriv_slice J hJ p.1 _

end
end G5019Sup1
end NlsGge.GKDefinitionDesign
