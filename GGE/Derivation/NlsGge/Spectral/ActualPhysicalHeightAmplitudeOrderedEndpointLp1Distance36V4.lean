import NlsGge.Spectral.ActualPhysicalHeightAmplitudeEndpointPointwise36V4
import NlsGge.Measure.ActualPhysicalBoundedHeightAmplitudeLp1Distance35V1
import NlsGge.Measure.ActualPhysicalSourceNormPrimitiveContinuity35V2
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis

/-- Actual 00-channel class distance for ordered endpoints is controlled by
actual physical-source mass on the intervening interval. -/
theorem actualPhysicalHeightAmplitude00_orderedEndpointLp1Distance36V4
    (u : PhysicalL2) (Y₀ s s' Y : ℝ) (hY₀ : 0 ≤ Y₀)
    (hs₀ : 0 ≤ s) (hss' : s ≤ s') (hs'₁ : s' ≤ 1)
    (hY : Y ∈ Set.Icc (0 : ℝ) Y₀) :
    dist
      (actualPhysicalHeightAmplitude00Lp1_35V2 u Y₀ hY₀
        ⟨⟨s, ⟨hs₀, hss'.trans hs'₁⟩⟩, ⟨Y, hY⟩⟩)
      (actualPhysicalHeightAmplitude00Lp1_35V2 u Y₀ hY₀
        ⟨⟨s', ⟨hs₀.trans hss', hs'₁⟩⟩, ⟨Y, hY⟩⟩)
      ≤ Real.exp (2 * Y₀) *
        (actualPhysicalSourceNormPrimitive35V2 u s' -
          actualPhysicalSourceNormPrimitive35V2 u s) := by
  let p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀ :=
    ⟨⟨s, ⟨hs₀, hss'.trans hs'₁⟩⟩, ⟨Y, hY⟩⟩
  let q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀ :=
    ⟨⟨s', ⟨hs₀.trans hss', hs'₁⟩⟩, ⟨Y, hY⟩⟩
  let c : ℝ := Real.exp (2 * Y₀)
  have hA : Integrable (actualPhysicalHeightAmplitude00_35V3 u s Y) volume :=
    actualPhysicalHeightAmplitude00_integrable35V3 u hs₀ (hss'.trans hs'₁)
      hY₀ hY.1 hY.2
  have hB : Integrable (actualPhysicalHeightAmplitude00_35V3 u s' Y) volume :=
    actualPhysicalHeightAmplitude00_integrable35V3 u (hs₀.trans hss') hs'₁
      hY₀ hY.1 hY.2
  have hsubEq :
      (fun r : ℝ => actualPhysicalHeightAmplitude00_35V3 u s Y r -
        actualPhysicalHeightAmplitude00_35V3 u s' Y r) =
        actualPhysicalHeightAmplitude00_35V3 u s Y -
          actualPhysicalHeightAmplitude00_35V3 u s' Y := by
    funext r
    rfl
  have hleft : Integrable (fun r : ℝ =>
      dist (actualPhysicalHeightAmplitude00_35V3 u s Y r)
        (actualPhysicalHeightAmplitude00_35V3 u s' Y r)) volume := by
    have hsub : Integrable (fun r : ℝ =>
        actualPhysicalHeightAmplitude00_35V3 u s Y r -
          actualPhysicalHeightAmplitude00_35V3 u s' Y r) volume := by
      rw [hsubEq]
      exact hA.sub hB
    simpa only [dist_eq_norm] using hsub.norm
  have hsource : IntegrableOn
      (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖)
      (Set.Ioc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp
      (actualPhysicalSourceNormIntervalIntegrable35V2 u)
  have hsource_ss' : IntegrableOn
      (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖)
      (Set.Ioc s s') volume :=
    hsource.mono_set (Set.Ioc_subset_Ioc hs₀ hs'₁)
  have hmajorant_on : IntegrableOn
      (fun r : ℝ => c * ‖actualPhysicalL2SourcePotential u r‖)
      (Set.Ioc s s') volume := hsource_ss'.const_mul c
  have hmajorant : Integrable
      (Set.indicator (Set.Ioc s s')
        (fun r : ℝ => c * ‖actualPhysicalL2SourcePotential u r‖)) volume :=
    hmajorant_on.integrable_indicator measurableSet_Ioc
  have hpoint : ∀ᵐ r ∂(volume : Measure ℝ),
      dist (actualPhysicalHeightAmplitude00_35V3 u s Y r)
          (actualPhysicalHeightAmplitude00_35V3 u s' Y r) ≤
        Set.indicator (Set.Ioc s s')
          (fun x : ℝ => c * ‖actualPhysicalL2SourcePotential u x‖) r := by
    filter_upwards [] with r
    simpa [c, dist_eq_norm] using
      actualPhysicalHeightAmplitude00_orderedEndpointPointwise36V4
        u Y₀ s s' Y r hY₀ hs₀ hss' hs'₁ hY
  have hIntegral := integral_mono_ae hleft hmajorant hpoint
  have hmass :
      ∫ r in Set.Ioc s s', ‖actualPhysicalL2SourcePotential u r‖ =
        actualPhysicalSourceNormPrimitive35V2 u s' -
          actualPhysicalSourceNormPrimitive35V2 u s := by
    have hsource_s : IntegrableOn
        (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖)
        (Set.Ioc (0 : ℝ) s) volume := hsource.mono_set (Set.Ioc_subset_Ioc le_rfl (hss'.trans hs'₁))
    have hsource_s' : IntegrableOn
        (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖)
        (Set.Ioc (0 : ℝ) s') volume := hsource.mono_set (Set.Ioc_subset_Ioc le_rfl hs'₁)
    have hsInt : IntervalIntegrable
        (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖) volume 0 s :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hs₀).2 hsource_s
    have hs'Int : IntervalIntegrable
        (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖) volume 0 s' :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (hs₀.trans hss')).2 hsource_s'
    have hdiff := intervalIntegral.integral_interval_sub_left hs'Int hsInt
    calc
      ∫ r in Set.Ioc s s', ‖actualPhysicalL2SourcePotential u r‖
          = ∫ r in s..s', ‖actualPhysicalL2SourcePotential u r‖ :=
              (intervalIntegral.integral_of_le hss').symm
      _ = actualPhysicalSourceNormPrimitive35V2 u s' -
            actualPhysicalSourceNormPrimitive35V2 u s := by
              simpa only [actualPhysicalSourceNormPrimitive35V2] using hdiff.symm
  have hmajorant_integral :
      ∫ r : ℝ, Set.indicator (Set.Ioc s s')
        (fun x : ℝ => c * ‖actualPhysicalL2SourcePotential u x‖) r ∂volume =
        c * (actualPhysicalSourceNormPrimitive35V2 u s' -
          actualPhysicalSourceNormPrimitive35V2 u s) := by
    rw [integral_indicator measurableSet_Ioc, integral_const_mul, hmass]
  rw [actualPhysicalHeightAmplitude00Lp1_35V2_dist_eq_integral u Y₀ hY₀ p q]
  calc
    (∫ r : ℝ, dist (actualPhysicalHeightAmplitude00_35V3 u p.1 p.2 r)
        (actualPhysicalHeightAmplitude00_35V3 u q.1 q.2 r) ∂volume)
      ≤ ∫ r : ℝ, Set.indicator (Set.Ioc s s')
          (fun x : ℝ => c * ‖actualPhysicalL2SourcePotential u x‖) r ∂volume := hIntegral
    _ = c * (actualPhysicalSourceNormPrimitive35V2 u s' -
        actualPhysicalSourceNormPrimitive35V2 u s) := hmajorant_integral

/-- The actual 11-channel ordered-endpoint distance bound keeps its unstarred
physical potential and original negative exponential. -/
theorem actualPhysicalHeightAmplitude11_orderedEndpointLp1Distance36V4
    (u : PhysicalL2) (Y₀ s s' Y : ℝ) (hY₀ : 0 ≤ Y₀)
    (hs₀ : 0 ≤ s) (hss' : s ≤ s') (hs'₁ : s' ≤ 1)
    (hY : Y ∈ Set.Icc (0 : ℝ) Y₀) :
    dist
      (actualPhysicalHeightAmplitude11Lp1_35V2 u Y₀ hY₀
        ⟨⟨s, ⟨hs₀, hss'.trans hs'₁⟩⟩, ⟨Y, hY⟩⟩)
      (actualPhysicalHeightAmplitude11Lp1_35V2 u Y₀ hY₀
        ⟨⟨s', ⟨hs₀.trans hss', hs'₁⟩⟩, ⟨Y, hY⟩⟩)
      ≤ Real.exp (2 * Y₀) *
        (actualPhysicalSourceNormPrimitive35V2 u s' -
          actualPhysicalSourceNormPrimitive35V2 u s) := by
  let p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀ :=
    ⟨⟨s, ⟨hs₀, hss'.trans hs'₁⟩⟩, ⟨Y, hY⟩⟩
  let q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀ :=
    ⟨⟨s', ⟨hs₀.trans hss', hs'₁⟩⟩, ⟨Y, hY⟩⟩
  let c : ℝ := Real.exp (2 * Y₀)
  have hA : Integrable (actualPhysicalHeightAmplitude11_35V3 u s Y) volume :=
    actualPhysicalHeightAmplitude11_integrable35V3 u hs₀ (hss'.trans hs'₁)
      hY₀ hY.1 hY.2
  have hB : Integrable (actualPhysicalHeightAmplitude11_35V3 u s' Y) volume :=
    actualPhysicalHeightAmplitude11_integrable35V3 u (hs₀.trans hss') hs'₁
      hY₀ hY.1 hY.2
  have hsubEq :
      (fun r : ℝ => actualPhysicalHeightAmplitude11_35V3 u s Y r -
        actualPhysicalHeightAmplitude11_35V3 u s' Y r) =
        actualPhysicalHeightAmplitude11_35V3 u s Y -
          actualPhysicalHeightAmplitude11_35V3 u s' Y := by
    funext r
    rfl
  have hleft : Integrable (fun r : ℝ =>
      dist (actualPhysicalHeightAmplitude11_35V3 u s Y r)
        (actualPhysicalHeightAmplitude11_35V3 u s' Y r)) volume := by
    have hsub : Integrable (fun r : ℝ =>
        actualPhysicalHeightAmplitude11_35V3 u s Y r -
          actualPhysicalHeightAmplitude11_35V3 u s' Y r) volume := by
      rw [hsubEq]
      exact hA.sub hB
    simpa only [dist_eq_norm] using hsub.norm
  have hsource : IntegrableOn
      (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖)
      (Set.Ioc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp
      (actualPhysicalSourceNormIntervalIntegrable35V2 u)
  have hsource_ss' : IntegrableOn
      (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖)
      (Set.Ioc s s') volume :=
    hsource.mono_set (Set.Ioc_subset_Ioc hs₀ hs'₁)
  have hmajorant_on : IntegrableOn
      (fun r : ℝ => c * ‖actualPhysicalL2SourcePotential u r‖)
      (Set.Ioc s s') volume := hsource_ss'.const_mul c
  have hmajorant : Integrable
      (Set.indicator (Set.Ioc s s')
        (fun r : ℝ => c * ‖actualPhysicalL2SourcePotential u r‖)) volume :=
    hmajorant_on.integrable_indicator measurableSet_Ioc
  have hpoint : ∀ᵐ r ∂(volume : Measure ℝ),
      dist (actualPhysicalHeightAmplitude11_35V3 u s Y r)
          (actualPhysicalHeightAmplitude11_35V3 u s' Y r) ≤
        Set.indicator (Set.Ioc s s')
          (fun x : ℝ => c * ‖actualPhysicalL2SourcePotential u x‖) r := by
    filter_upwards [] with r
    simpa [c, dist_eq_norm] using
      actualPhysicalHeightAmplitude11_orderedEndpointPointwise36V4
        u Y₀ s s' Y r hY₀ hs₀ hss' hs'₁ hY
  have hIntegral := integral_mono_ae hleft hmajorant hpoint
  have hmass :
      ∫ r in Set.Ioc s s', ‖actualPhysicalL2SourcePotential u r‖ =
        actualPhysicalSourceNormPrimitive35V2 u s' -
          actualPhysicalSourceNormPrimitive35V2 u s := by
    have hsource_s : IntegrableOn
        (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖)
        (Set.Ioc (0 : ℝ) s) volume := hsource.mono_set (Set.Ioc_subset_Ioc le_rfl (hss'.trans hs'₁))
    have hsource_s' : IntegrableOn
        (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖)
        (Set.Ioc (0 : ℝ) s') volume := hsource.mono_set (Set.Ioc_subset_Ioc le_rfl hs'₁)
    have hsInt : IntervalIntegrable
        (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖) volume 0 s :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hs₀).2 hsource_s
    have hs'Int : IntervalIntegrable
        (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖) volume 0 s' :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (hs₀.trans hss')).2 hsource_s'
    have hdiff := intervalIntegral.integral_interval_sub_left hs'Int hsInt
    calc
      ∫ r in Set.Ioc s s', ‖actualPhysicalL2SourcePotential u r‖
          = ∫ r in s..s', ‖actualPhysicalL2SourcePotential u r‖ :=
              (intervalIntegral.integral_of_le hss').symm
      _ = actualPhysicalSourceNormPrimitive35V2 u s' -
            actualPhysicalSourceNormPrimitive35V2 u s := by
              simpa only [actualPhysicalSourceNormPrimitive35V2] using hdiff.symm
  have hmajorant_integral :
      ∫ r : ℝ, Set.indicator (Set.Ioc s s')
        (fun x : ℝ => c * ‖actualPhysicalL2SourcePotential u x‖) r ∂volume =
        c * (actualPhysicalSourceNormPrimitive35V2 u s' -
          actualPhysicalSourceNormPrimitive35V2 u s) := by
    rw [integral_indicator measurableSet_Ioc, integral_const_mul, hmass]
  rw [actualPhysicalHeightAmplitude11Lp1_35V2_dist_eq_integral u Y₀ hY₀ p q]
  calc
    (∫ r : ℝ, dist (actualPhysicalHeightAmplitude11_35V3 u p.1 p.2 r)
        (actualPhysicalHeightAmplitude11_35V3 u q.1 q.2 r) ∂volume)
      ≤ ∫ r : ℝ, Set.indicator (Set.Ioc s s')
          (fun x : ℝ => c * ‖actualPhysicalL2SourcePotential u x‖) r ∂volume := hIntegral
    _ = c * (actualPhysicalSourceNormPrimitive35V2 u s' -
        actualPhysicalSourceNormPrimitive35V2 u s) := hmajorant_integral

end NlsGge.SpectralFoundations
end
