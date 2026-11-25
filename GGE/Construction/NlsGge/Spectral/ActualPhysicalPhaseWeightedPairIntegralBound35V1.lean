import NlsGge.Spectral.NonnegativeWeightedProductMinimum33V1
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

/-- Continuous norm-one phases and a bounded test under the actual source's weighted
two-step Volterra integral. Both inner and outer integrability are realized
from the physical L2 representative. This estimate is an intermediate
operator bound, not an assumed Dyson estimate or a high-energy conclusion. -/
theorem actualPhysicalPhaseWeightedPairIntegral_bound35
    (u : PhysicalL2) (Y : ℝ) (hY : 0 < Y)
    (p q F : ℝ → ℂ)
    (hp : ContinuousOn p (Set.Icc (0 : ℝ) 1))
    (hq : ContinuousOn q (Set.Icc (0 : ℝ) 1))
    (hnp : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖p s‖ = 1)
    (hnq : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖q s‖ = 1)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖F s‖ ≤ C)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable
      (fun s => (Real.exp (-2*Y*(t-s)) : ℂ) * p s *
        star (naturalPhysicalCoverL2 u (s : SpectralCircle)) *
        (∫ r in (0 : ℝ)..s, naturalPhysicalCoverL2 u (r : SpectralCircle) * (q r*F r)))
      volume 0 t ∧
    ‖∫ s in (0 : ℝ)..t, (Real.exp (-2*Y*(t-s)) : ℂ) * p s *
        star (naturalPhysicalCoverL2 u (s : SpectralCircle)) *
        (∫ r in (0 : ℝ)..s, naturalPhysicalCoverL2 u (r : SpectralCircle) * (q r*F r))‖ ≤
      (C*‖u‖) * Real.sqrt (‖u‖^2/(4*Y)) := by
  let U : ℝ → ℂ := fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)
  let G : ℝ → ℂ := fun r => q r*F r
  have hG : ContinuousOn G (Set.Icc (0 : ℝ) 1) := hq.mul hF
  have hGb : ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖G r‖ ≤ C := by
    intro r hr
    simpa only [G, norm_mul, hnq r hr, one_mul] using hbound r hr
  let P : ℝ → ℂ := fun s => ∫ r in (0 : ℝ)..s, U r * G r
  have hU : IntervalIntegrable U volume 0 1 := by
    apply (naturalPhysicalCoverL2_intervalIntegrable_doubled u).mono_set
    simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hFu : ContinuousOn G (Set.uIcc (0 : ℝ) 1) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hG
  have hUF := hU.mul_continuousOn hFu
  have hP : ContinuousOn P (Set.uIcc (0 : ℝ) 1) :=
    intervalIntegral.continuousOn_primitive_interval' (μ := volume) hUF Set.left_mem_uIcc
  have hrestrict (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      Set.uIcc (0 : ℝ) s ⊆ Set.uIcc (0 : ℝ) 1 := by
    simp only [Set.uIcc_of_le hs.1, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro r hr
    exact ⟨hr.1, hr.2.trans hs.2⟩
  have hPbound (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : ‖P s‖ ≤ C*‖u‖ := by
    have hmajor : IntervalIntegrable (fun r => C*‖U r‖) volume 0 s :=
      (hU.norm.const_mul C).mono_set (hrestrict s hs)
    have hn : ∀ᵐ r ∂volume, r ∈ Set.Ioc (0 : ℝ) s → ‖U r*G r‖ ≤ C*‖U r‖ := by
      apply Filter.Eventually.of_forall
      intro r hr
      rw [norm_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hGb r ⟨hr.1.le, hr.2.trans hs.2⟩)
        (norm_nonneg _)
    calc
      ‖P s‖ ≤ ∫ r in (0 : ℝ)..s, C*‖U r‖ :=
        intervalIntegral.norm_integral_le_of_norm_le hs.1 hn hmajor
      _ = C*(∫ r in (0 : ℝ)..s, ‖U r‖) := intervalIntegral.integral_const_mul _ _
      _ ≤ C*‖u‖ := mul_le_mul_of_nonneg_left
        (actualPhysicalRawCover_subintervalIntegral_norm_le33 u s hs) hC
  have hUstar : IntervalIntegrable (fun s => star (U s)) volume 0 1 := by
    have hm : AEStronglyMeasurable (fun s => star (U s))
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
      simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Pi.star_apply]
        using! hU.aestronglyMeasurable.star
    apply hU.mono_fun hm
    exact Filter.Eventually.of_forall (fun s => (norm_star (U s)).le)
  have hkernel : ContinuousOn (fun s : ℝ => (Real.exp (-2*Y*(t-s)) : ℂ))
      (Set.uIcc (0 : ℝ) 1) := by fun_prop
  have hpu : ContinuousOn p (Set.uIcc (0 : ℝ) 1) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hp
  have houter : IntervalIntegrable
      (fun s => (Real.exp (-2*Y*(t-s)) : ℂ)*p s*star (U s)*P s) volume 0 t := by
    have hi := hUstar.mul_continuousOn (hkernel.mul (hpu.mul hP))
    have hi' : IntervalIntegrable
        (fun s => (Real.exp (-2*Y*(t-s)) : ℂ)*p s*star (U s)*P s) volume 0 1 := by
      convert hi using 1
      funext s
      dsimp only [Pi.mul_apply]
      ring
    exact hi'.mono_set (hrestrict t ht)
  have hmajor : IntervalIntegrable
      (fun s => (C*‖u‖)*(‖U s‖*Real.exp (-2*Y*(t-s)))) volume 0 t := by
    have he : ContinuousOn (fun s : ℝ => Real.exp (-2*Y*(t-s)))
        (Set.uIcc (0 : ℝ) 1) := by fun_prop
    exact ((hU.norm.mul_continuousOn he).const_mul (C*‖u‖)).mono_set (hrestrict t ht)
  have hn : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0 : ℝ) t →
      ‖(Real.exp (-2*Y*(t-s)) : ℂ)*p s*star (U s)*P s‖ ≤
        (C*‖u‖)*(‖U s‖*Real.exp (-2*Y*(t-s))) := by
    apply Filter.Eventually.of_forall
    intro s hs
    rw [norm_mul, norm_mul, norm_mul, hnp s ⟨hs.1.le, hs.2.trans ht.2⟩, mul_one, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact nonnegativeWeightedProduct_minimum33
      (Real.exp (-2*Y*(t-s))) (‖U s‖) (‖P s‖) (C*‖u‖)
      (Real.exp_pos _).le (norm_nonneg _) (hPbound s ⟨hs.1.le, hs.2.trans ht.2⟩)
  refine ⟨houter, ?_⟩
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, (C*‖u‖)*(‖U s‖*Real.exp (-2*Y*(t-s))) :=
      intervalIntegral.norm_integral_le_of_norm_le ht.1 hn hmajor
    _ = (C*‖u‖)*(∫ s in (0 : ℝ)..t, ‖U s‖*Real.exp (-2*Y*(t-s))) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (C*‖u‖)*Real.sqrt (‖u‖^2/(4*Y)) :=
      mul_le_mul_of_nonneg_left (actualPhysicalRawCover_weightedIntegral_norm_le33 u Y t hY ht)
        (mul_nonneg hC (norm_nonneg u))

end NlsGge.SpectralFoundations
end
