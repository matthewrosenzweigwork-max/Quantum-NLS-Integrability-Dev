import NlsGge.Spectral.ActualPhysicalDecayingPairIntegralBound34V1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual physical 00 pair integral with continuous norm-one phases
is integrable and has the same vanishing L2 coefficient. Its complex potential
and conjugation are preserved. No coefficient estimate is assumed. -/
theorem actualPhysicalPhaseDecayingPairIntegral_bound35
    (u : PhysicalL2) (Y : ℝ) (hY : 0 < Y)
    (p q F : ℝ → ℂ)
    (hp : ContinuousOn p (Set.Icc (0 : ℝ) 1))
    (hq : ContinuousOn q (Set.Icc (0 : ℝ) 1))
    (hnp : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖p s‖ = 1)
    (hnq : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖q s‖ = 1)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖F r‖ ≤ C)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable
      (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)*p s*
        (∫ r in (0 : ℝ)..s, (Real.exp (-2*Y*(s-r)) : ℂ)*
          star (naturalPhysicalCoverL2 u (r : SpectralCircle))*(q r*F r))) volume 0 t ∧
    ‖∫ s in (0 : ℝ)..t, naturalPhysicalCoverL2 u (s : SpectralCircle)*p s*
        (∫ r in (0 : ℝ)..s, (Real.exp (-2*Y*(s-r)) : ℂ)*
          star (naturalPhysicalCoverL2 u (r : SpectralCircle))*(q r*F r))‖ ≤
      (C*‖u‖)*Real.sqrt (‖u‖^2/(4*Y)) := by
  let U : ℝ → ℂ := fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)
  let G : ℝ → ℂ := fun r => q r*F r
  have hG : ContinuousOn G (Set.Icc (0 : ℝ) 1) := hq.mul hF
  have hGb : ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖G r‖ ≤ C := by
    intro r hr
    simpa only [G, norm_mul, hnq r hr, one_mul] using hbound r hr
  let P : ℝ → ℂ := fun s => ∫ r in (0 : ℝ)..s,
    (Real.exp (-2*Y*(s-r)) : ℂ)*star (U r)*G r
  have hU : IntervalIntegrable U volume 0 1 := by
    apply (naturalPhysicalCoverL2_intervalIntegrable_doubled u).mono_set
    simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro s hs
    exact ⟨hs.1, hs.2.trans (by norm_num)⟩
  have hUstar : IntervalIntegrable (fun s => star (U s)) volume 0 1 := by
    have hm : AEStronglyMeasurable (fun s => star (U s))
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
      simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Pi.star_apply]
        using! hU.aestronglyMeasurable.star
    apply hU.mono_fun hm
    exact Filter.Eventually.of_forall (fun s => (norm_star (U s)).le)
  have hFu : ContinuousOn G (Set.uIcc (0 : ℝ) 1) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hG
  have hep : ContinuousOn (fun r : ℝ => (Real.exp (2*Y*r) : ℂ))
      (Set.uIcc (0 : ℝ) 1) := by fun_prop
  have hprim : ContinuousOn
      (fun s => ∫ r in (0 : ℝ)..s, star (U r)*((Real.exp (2*Y*r) : ℂ)*G r))
      (Set.uIcc (0 : ℝ) 1) :=
    intervalIntegral.continuousOn_primitive_interval' (μ := volume)
      (hUstar.mul_continuousOn (hep.mul hFu)) Set.left_mem_uIcc
  have hem : ContinuousOn (fun s : ℝ => (Real.exp (-2*Y*s) : ℂ))
      (Set.uIcc (0 : ℝ) 1) := by fun_prop
  have hP : ContinuousOn P (Set.uIcc (0 : ℝ) 1) := by
    have heq : P = fun s => (Real.exp (-2*Y*s) : ℂ)*
        (∫ r in (0 : ℝ)..s, star (U r)*((Real.exp (2*Y*r) : ℂ)*G r)) := by
      funext s
      exact decayingInnerIntegral_factor34 U G Y s
    rw [heq]
    exact hem.mul hprim
  have hrestrict : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc (0 : ℝ) 1 := by
    simp only [Set.uIcc_of_le ht.1, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro s hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hpu : ContinuousOn p (Set.uIcc (0 : ℝ) 1) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hp
  have hi : IntervalIntegrable (fun s => U s*p s*P s) volume 0 t := by
    convert (hU.mul_continuousOn (hpu.mul hP)).mono_set hrestrict using 1
    funext s
    dsimp only [Pi.mul_apply]
    ring
  have hm : IntervalIntegrable
      (fun s => (C*Real.sqrt (‖u‖^2/(4*Y)))*‖U s‖) volume 0 t :=
    (hU.norm.const_mul _).mono_set hrestrict
  have hn : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0 : ℝ) t →
      ‖U s*p s*P s‖ ≤ (C*Real.sqrt (‖u‖^2/(4*Y)))*‖U s‖ := by
    apply Filter.Eventually.of_forall
    intro s hs
    rw [norm_mul, norm_mul, hnp s ⟨hs.1.le, hs.2.trans ht.2⟩, mul_one, mul_comm (C*Real.sqrt (‖u‖^2/(4*Y)))]
    exact mul_le_mul_of_nonneg_left
      (actualPhysicalDecayingInnerIntegral_bound34 u Y hY G hG C hC hGb s
        ⟨hs.1.le, hs.2.trans ht.2⟩).2 (norm_nonneg _)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, (C*Real.sqrt (‖u‖^2/(4*Y)))*‖U s‖ :=
      intervalIntegral.norm_integral_le_of_norm_le ht.1 hn hm
    _ = (C*Real.sqrt (‖u‖^2/(4*Y)))*(∫ s in (0 : ℝ)..t, ‖U s‖) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (C*Real.sqrt (‖u‖^2/(4*Y)))*‖u‖ :=
      mul_le_mul_of_nonneg_left (actualPhysicalRawCover_subintervalIntegral_norm_le33 u t ht)
        (mul_nonneg hC (Real.sqrt_nonneg _))
    _ = _ := by ring

end NlsGge.SpectralFoundations
end
