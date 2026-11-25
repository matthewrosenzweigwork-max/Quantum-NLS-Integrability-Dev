import NlsGge.Spectral.ActualPhysicalSourceWeightedCauchySchwarz33V2
import NlsGge.Schur.ActualPhysicalSourceIntervalCauchySchwarz33V2
import NlsGge.Spectral.ActualPhysicalL2DoubledIntervalMemLpV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual decaying 00 inner kernel, tested against a bounded continuous
function. Integrability is realized from the original rough physical field.
This is a local integral bound, not a high-energy or spectral-label claim. -/
theorem actualPhysicalDecayingInnerIntegral_bound34
    (u : PhysicalL2) (Y : ℝ) (hY : 0 < Y)
    (F : ℝ → ℂ) (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖F r‖ ≤ C)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable
      (fun r => (Real.exp (-2*Y*(s-r)) : ℂ) *
        star (naturalPhysicalCoverL2 u (r : SpectralCircle)) * F r) volume 0 s ∧
    ‖∫ r in (0 : ℝ)..s, (Real.exp (-2*Y*(s-r)) : ℂ) *
        star (naturalPhysicalCoverL2 u (r : SpectralCircle)) * F r‖ ≤
      C * Real.sqrt (‖u‖^2/(4*Y)) := by
  let U : ℝ → ℂ := fun r => naturalPhysicalCoverL2 u (r : SpectralCircle)
  have hU : IntervalIntegrable U volume 0 1 := by
    apply (naturalPhysicalCoverL2_intervalIntegrable_doubled u).mono_set
    simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro r hr
    exact ⟨hr.1, hr.2.trans (by norm_num)⟩
  have hrestrict : Set.uIcc (0 : ℝ) s ⊆ Set.uIcc (0 : ℝ) 1 := by
    simp only [Set.uIcc_of_le hs.1, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro r hr
    exact ⟨hr.1, hr.2.trans hs.2⟩
  have hUstar : IntervalIntegrable (fun r => star (U r)) volume 0 1 := by
    have hm : AEStronglyMeasurable (fun r => star (U r))
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
      simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Pi.star_apply]
        using! hU.aestronglyMeasurable.star
    apply hU.mono_fun hm
    exact Filter.Eventually.of_forall (fun r => (norm_star (U r)).le)
  have hFu : ContinuousOn F (Set.uIcc (0 : ℝ) 1) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hF
  have he : ContinuousOn (fun r : ℝ => (Real.exp (-2*Y*(s-r)) : ℂ))
      (Set.uIcc (0 : ℝ) 1) := by fun_prop
  have hi : IntervalIntegrable
      (fun r => (Real.exp (-2*Y*(s-r)) : ℂ)*star (U r)*F r) volume 0 s := by
    have h := hUstar.mul_continuousOn (he.mul hFu)
    have h' : IntervalIntegrable
        (fun r => (Real.exp (-2*Y*(s-r)) : ℂ)*star (U r)*F r) volume 0 1 := by
      convert h using 1
      funext r
      dsimp only [Pi.mul_apply]
      ring
    exact h'.mono_set hrestrict
  have her : ContinuousOn (fun r : ℝ => Real.exp (-2*Y*(s-r)))
      (Set.uIcc (0 : ℝ) 1) := by fun_prop
  have hm : IntervalIntegrable
      (fun r => C*(‖U r‖*Real.exp (-2*Y*(s-r)))) volume 0 s :=
    ((hU.norm.mul_continuousOn her).const_mul C).mono_set hrestrict
  have hn : ∀ᵐ r ∂volume, r ∈ Set.Ioc (0 : ℝ) s →
      ‖(Real.exp (-2*Y*(s-r)) : ℂ)*star (U r)*F r‖ ≤
        C*(‖U r‖*Real.exp (-2*Y*(s-r))) := by
    apply Filter.Eventually.of_forall
    intro r hr
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (Real.exp (-2*Y*(s-r))*‖U r‖)*C :=
        mul_le_mul_of_nonneg_left (hbound r ⟨hr.1.le, hr.2.trans hs.2⟩)
          (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      _ = _ := by ring
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ r in (0 : ℝ)..s, C*(‖U r‖*Real.exp (-2*Y*(s-r))) :=
      intervalIntegral.norm_integral_le_of_norm_le hs.1 hn hm
    _ = C*(∫ r in (0 : ℝ)..s, ‖U r‖*Real.exp (-2*Y*(s-r))) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ C*Real.sqrt (‖u‖^2/(4*Y)) :=
      mul_le_mul_of_nonneg_left
        (actualPhysicalRawCover_weightedIntegral_norm_le33 u Y s hY hs) hC

end NlsGge.SpectralFoundations
end
