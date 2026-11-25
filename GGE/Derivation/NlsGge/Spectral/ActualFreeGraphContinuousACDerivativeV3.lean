import NlsGge.Spectral.ActualFreeDomainFourierACAndTwistedTraceV3
import NlsGge.Spectral.ComplexIntervalIntegralPrimitiveAbsolutelyContinuousV2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.Schur
open NlsGge.SpectralFoundations

/-- The actual graph derivative is genuinely L¹ on the source interval. -/
theorem sourceFreeCoordinateDerivative_intervalIntegrable
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n) (b : Bool) :
    IntervalIntegrable (fun t => sourceFreeCoordinateDerivative n x hx b t) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mpr
  exact (Lp.memLp (sourceFreeCoordinateDerivative n x hx b)).integrable (by norm_num)

/-- The actual continuous Fourier representative of every weighted-domain
vector is absolutely continuous; no additional state regularity is assumed. -/
theorem absolutelyContinuous_freeDomainContinuousComponent_source
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n) (b : Bool) :
    AbsolutelyContinuousOnInterval
      (fun t : ℝ => freeDomainContinuousComponent n x b (t : SpectralCircle)) 0 1 := by
  have hg := sourceFreeCoordinateDerivative_intervalIntegrable n x hx b
  have hp := complex_intervalIntegral_primitive_absolutelyContinuousV2 (c := 0) hg Set.left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => freeDomainContinuousComponent n x b ((0 : ℝ) : SpectralCircle)) 0 1 := by
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    refine ⟨1, by norm_num, ?_⟩
    intro E hE hlen
    simpa using hε
  apply (hc.add hp).congr
  intro t ht
  have htcc : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  exact ((freeDomainContinuousComponent_integral_and_twistedTrace n x hx b).1 t htcc).symm

/-- The derivative of the actual continuous Fourier reconstruction agrees
almost everywhere with the genuine free graph derivative class. -/
theorem freeDomainContinuousComponent_source_ae_hasDerivAt
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n) (b : Bool) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 →
      HasDerivAt
        (fun s : ℝ => freeDomainContinuousComponent n x b (s : SpectralCircle))
        (sourceFreeCoordinateDerivative n x hx b t) t := by
  have hg := sourceFreeCoordinateDerivative_intervalIntegrable n x hx b
  have h0 : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by simp [ae_iff, measure_singleton]
  have h1 : ∀ᵐ t ∂volume, t ≠ (1 : ℝ) := by simp [ae_iff, measure_singleton]
  filter_upwards [hg.ae_hasDerivAt_integral, h0, h1] with t hd ht0 ht1
  intro ht
  have htcc : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  have hlo := lt_of_le_of_ne htcc.1 (Ne.symm ht0)
  have hhi := lt_of_le_of_ne htcc.2 ht1
  have hder := (hd ht 0 Set.left_mem_uIcc).const_add
    (freeDomainContinuousComponent n x b ((0 : ℝ) : SpectralCircle))
  apply hder.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hlo hhi] with s hs
  exact (freeDomainContinuousComponent_integral_and_twistedTrace n x hx b).1 s
    ⟨hs.1.le, hs.2.le⟩

end NlsGge.Schur
end
