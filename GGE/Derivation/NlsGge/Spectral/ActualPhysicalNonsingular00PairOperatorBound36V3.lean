import NlsGge.Spectral.ActualPhysicalDecayingPairIntegralBound34V1
import NlsGge.Schur.ActualPhysicalSourceIntervalCauchySchwarz33V2
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- A nonsingular phase-insensitive bound for the actual 00 Volterra pair,
valid also at height zero. The factorization is used only for continuity and
the direct kernel bound for the norm; no Fubini or decay claim is used. -/
theorem actualPhysicalNonsingular00PairOperator_bound36V3
    (u : PhysicalL2) (Y : ℝ) (hY : 0 ≤ Y)
    (p q F : ℝ → ℂ)
    (hp : ContinuousOn p (Set.Icc (0 : ℝ) 1))
    (hq : ContinuousOn q (Set.Icc (0 : ℝ) 1))
    (hnp : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖p s‖ = 1)
    (hnq : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖q s‖ = 1)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖F s‖ ≤ C)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable
      (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle) * p s *
        (∫ r in (0 : ℝ)..s,
          (Real.exp (-2*Y*(s-r)) : ℂ) * star (naturalPhysicalCoverL2 u (r : SpectralCircle)) *
            (q r*F r))) volume 0 t ∧
    ‖∫ s in (0 : ℝ)..t, naturalPhysicalCoverL2 u (s : SpectralCircle) * p s *
        (∫ r in (0 : ℝ)..s,
          (Real.exp (-2*Y*(s-r)) : ℂ) * star (naturalPhysicalCoverL2 u (r : SpectralCircle)) *
            (q r*F r))‖ ≤ C * ‖u‖^2 := by
  let U : ℝ → ℂ := fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)
  let G : ℝ → ℂ := fun r => q r*F r
  let P : ℝ → ℂ := fun s => ∫ r in (0 : ℝ)..s,
    (Real.exp (-2*Y*(s-r)) : ℂ) * star (U r) * G r
  have hG : ContinuousOn G (Set.Icc (0 : ℝ) 1) := hq.mul hF
  have hGb : ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖G r‖ ≤ C := by
    intro r hr
    simpa only [G, norm_mul, hnq r hr, one_mul] using hbound r hr
  have hU : IntervalIntegrable U volume 0 1 := by
    apply (naturalPhysicalCoverL2_intervalIntegrable_doubled u).mono_set
    simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro r hr
    exact ⟨hr.1, hr.2.trans (by norm_num)⟩
  have hUstar : IntervalIntegrable (fun s => star (U s)) volume 0 1 := by
    have hm : AEStronglyMeasurable (fun s => star (U s))
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
      simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Pi.star_apply]
        using! hU.aestronglyMeasurable.star
    apply hU.mono_fun hm
    exact Filter.Eventually.of_forall (fun s => (norm_star (U s)).le)
  have hGu : ContinuousOn G (Set.uIcc (0 : ℝ) 1) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hG
  have hep : ContinuousOn (fun r : ℝ => (Real.exp (2*Y*r) : ℂ))
      (Set.uIcc (0 : ℝ) 1) := by fun_prop
  have hprim : ContinuousOn
      (fun s => ∫ r in (0 : ℝ)..s, star (U r) *
        ((Real.exp (2*Y*r) : ℂ)*G r)) (Set.uIcc (0 : ℝ) 1) :=
    intervalIntegral.continuousOn_primitive_interval' (μ := volume)
      (hUstar.mul_continuousOn (hep.mul hGu)) Set.left_mem_uIcc
  have hem : ContinuousOn (fun s : ℝ => (Real.exp (-2*Y*s) : ℂ))
      (Set.uIcc (0 : ℝ) 1) := by fun_prop
  have hP : ContinuousOn P (Set.uIcc (0 : ℝ) 1) := by
    have heq : P = fun s => (Real.exp (-2*Y*s) : ℂ) *
        (∫ r in (0 : ℝ)..s, star (U r) * ((Real.exp (2*Y*r) : ℂ)*G r)) := by
      funext s
      exact decayingInnerIntegral_factor34 U G Y s
    rw [heq]
    exact hem.mul hprim
  have hrestrict (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      Set.uIcc (0 : ℝ) s ⊆ Set.uIcc (0 : ℝ) 1 := by
    simp only [Set.uIcc_of_le hs.1, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro r hr
    exact ⟨hr.1, hr.2.trans hs.2⟩
  have hPbound (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : ‖P s‖ ≤ C*‖u‖ := by
    have hmajor : IntervalIntegrable (fun r => C*‖U r‖) volume 0 s :=
      (hU.norm.const_mul C).mono_set (hrestrict s hs)
    have hn : ∀ᵐ r ∂volume, r ∈ Set.Ioc (0 : ℝ) s →
        ‖(Real.exp (-2*Y*(s-r)) : ℂ)*star (U r)*G r‖ ≤ C*‖U r‖ := by
      apply Filter.Eventually.of_forall
      intro r hr
      have hr' : r ∈ Set.Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.trans hs.2⟩
      have harg : -2*Y*(s-r) ≤ 0 := by
        have := mul_nonneg hY (sub_nonneg.mpr hr.2)
        nlinarith
      have hexp : Real.exp (-2*Y*(s-r)) ≤ 1 := Real.exp_le_one_iff.mpr harg
      rw [norm_mul, norm_mul, norm_mul, norm_star,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hqF : ‖q r‖*‖F r‖ ≤ C := by
        rw [hnq r hr']
        simpa only [one_mul] using hbound r hr'
      calc
        Real.exp (-2*Y*(s-r))*‖U r‖*(‖q r‖*‖F r‖) ≤
            Real.exp (-2*Y*(s-r))*‖U r‖*C :=
          mul_le_mul_of_nonneg_left hqF
            (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
        _ ≤ 1*‖U r‖*C := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hexp (norm_nonneg _)) hC
        _ = C*‖U r‖ := by ring
    calc
      ‖P s‖ ≤ ∫ r in (0 : ℝ)..s, C*‖U r‖ :=
        intervalIntegral.norm_integral_le_of_norm_le hs.1 hn hmajor
      _ = C*(∫ r in (0 : ℝ)..s, ‖U r‖) := intervalIntegral.integral_const_mul _ _
      _ ≤ C*‖u‖ := mul_le_mul_of_nonneg_left
        (actualPhysicalRawCover_subintervalIntegral_norm_le33 u s hs) hC
  have hpu : ContinuousOn p (Set.uIcc (0 : ℝ) 1) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hp
  have houter : IntervalIntegrable (fun s => U s*p s*P s) volume 0 t := by
    convert (hU.mul_continuousOn (hpu.mul hP)).mono_set (hrestrict t ht) using 1
    funext s
    dsimp only [Pi.mul_apply]
    ring
  have hmajor : IntervalIntegrable (fun s => (C*‖u‖)*‖U s‖) volume 0 t :=
    (hU.norm.const_mul (C*‖u‖)).mono_set (hrestrict t ht)
  have hn : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0 : ℝ) t →
      ‖U s*p s*P s‖ ≤ (C*‖u‖)*‖U s‖ := by
    apply Filter.Eventually.of_forall
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.trans ht.2⟩
    rw [norm_mul, norm_mul, hnp s hs']
    simp only [mul_one]
    calc
      ‖U s‖*‖P s‖ ≤ ‖U s‖*(C*‖u‖) :=
        mul_le_mul_of_nonneg_left (hPbound s hs') (norm_nonneg _)
      _ = (C*‖u‖)*‖U s‖ := by ring
  refine ⟨houter, ?_⟩
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, (C*‖u‖)*‖U s‖ :=
      intervalIntegral.norm_integral_le_of_norm_le ht.1 hn hmajor
    _ = (C*‖u‖)*(∫ s in (0 : ℝ)..t, ‖U s‖) := intervalIntegral.integral_const_mul _ _
    _ ≤ (C*‖u‖)*‖u‖ := mul_le_mul_of_nonneg_left
      (actualPhysicalRawCover_subintervalIntegral_norm_le33 u t ht)
      (mul_nonneg hC (norm_nonneg u))
    _ = C*‖u‖^2 := by ring

end NlsGge.SpectralFoundations
end
