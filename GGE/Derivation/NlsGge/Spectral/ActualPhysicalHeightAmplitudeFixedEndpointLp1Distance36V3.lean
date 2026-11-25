import NlsGge.Measure.ActualPhysicalHeightAmplitudeFixedEndpointLipschitz35V2
import NlsGge.Measure.ActualPhysicalBoundedHeightAmplitudeLp1Distance35V1
import NlsGge.Measure.ActualPhysicalSourceNormPrimitiveContinuity35V2
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis

/-- The increment of the actual physical-source norm primitive is bounded
by the source mass on the unordered interval between the two endpoints. -/
theorem actualPhysicalSourceNormPrimitive35V2_abs_sub_le_uIoc
    (u : PhysicalL2) (s s' : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hs' : s' ∈ Set.Icc (0 : ℝ) 1) :
    |actualPhysicalSourceNormPrimitive35V2 u s -
        actualPhysicalSourceNormPrimitive35V2 u s'| ≤
      ∫ r in Set.uIoc s' s, ‖actualPhysicalL2SourcePotential u r‖ := by
  let f : ℝ → ℝ := fun r => ‖actualPhysicalL2SourcePotential u r‖
  have hsource : IntegrableOn f (Set.Ioc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp
      (actualPhysicalSourceNormIntervalIntegrable35V2 u)
  have hsIntOn : IntegrableOn f (Set.Ioc (0 : ℝ) s) volume :=
    hsource.mono_set (Set.Ioc_subset_Ioc le_rfl hs.2)
  have hs'IntOn : IntegrableOn f (Set.Ioc (0 : ℝ) s') volume :=
    hsource.mono_set (Set.Ioc_subset_Ioc le_rfl hs'.2)
  have hsInt : IntervalIntegrable f volume 0 s :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1).2 hsIntOn
  have hs'Int : IntervalIntegrable f volume 0 s' :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hs'.1).2 hs'IntOn
  have hdiff : actualPhysicalSourceNormPrimitive35V2 u s -
      actualPhysicalSourceNormPrimitive35V2 u s' = ∫ r in s'..s, f r := by
    simp only [actualPhysicalSourceNormPrimitive35V2]
    exact intervalIntegral.integral_interval_sub_left hsInt hs'Int
  calc
    |actualPhysicalSourceNormPrimitive35V2 u s -
        actualPhysicalSourceNormPrimitive35V2 u s'| =
        ‖∫ r in s'..s, f r‖ := by rw [← hdiff, Real.norm_eq_abs]
    _ ≤ ∫ r in Set.uIoc s' s, ‖f r‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ = ∫ r in Set.uIoc s' s, ‖actualPhysicalL2SourcePotential u r‖ := by
      simp [f]

/-- At a fixed physical endpoint, the actual 00-channel L¹ amplitude class is
Lipschitz in height, with its constant given by the actual source-norm mass. -/
theorem actualPhysicalHeightAmplitude00_fixedEndpointLp1Distance36V3
    (u : PhysicalL2) (Y₀ s Y Y' : ℝ) (hY₀ : 0 ≤ Y₀)
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hY : Y ∈ Set.Icc (0 : ℝ) Y₀) (hY' : Y' ∈ Set.Icc (0 : ℝ) Y₀) :
    dist
      (actualPhysicalHeightAmplitude00Lp1_35V2 u Y₀ hY₀
        ⟨⟨s, ⟨hs₀, hs₁⟩⟩, ⟨Y, hY⟩⟩)
      (actualPhysicalHeightAmplitude00Lp1_35V2 u Y₀ hY₀
        ⟨⟨s, ⟨hs₀, hs₁⟩⟩, ⟨Y', hY'⟩⟩)
      ≤ 2 * Real.exp (2 * Y₀) * |Y - Y'| *
        actualPhysicalSourceNormPrimitive35V2 u s := by
  let p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀ :=
    ⟨⟨s, ⟨hs₀, hs₁⟩⟩, ⟨Y, hY⟩⟩
  let q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀ :=
    ⟨⟨s, ⟨hs₀, hs₁⟩⟩, ⟨Y', hY'⟩⟩
  let c : ℝ := 2 * Real.exp (2 * Y₀) * |Y - Y'|
  have hleft : Integrable (fun r : ℝ =>
      dist (actualPhysicalHeightAmplitude00_35V3 u p.1 p.2 r)
        (actualPhysicalHeightAmplitude00_35V3 u q.1 q.2 r)) volume := by
    have hA := actualPhysicalHeightAmplitude00_integrable35V3 u hs₀ hs₁ hY₀ hY.1 hY.2
    have hB := actualPhysicalHeightAmplitude00_integrable35V3 u hs₀ hs₁ hY₀ hY'.1 hY'.2
    have hsubEq :
        (fun r : ℝ => actualPhysicalHeightAmplitude00_35V3 u p.1 p.2 r -
          actualPhysicalHeightAmplitude00_35V3 u q.1 q.2 r) =
          actualPhysicalHeightAmplitude00_35V3 u p.1 p.2 -
            actualPhysicalHeightAmplitude00_35V3 u q.1 q.2 := by
      funext r
      rfl
    have hsub : Integrable
        (fun r : ℝ => actualPhysicalHeightAmplitude00_35V3 u p.1 p.2 r -
          actualPhysicalHeightAmplitude00_35V3 u q.1 q.2 r) volume := by
      rw [hsubEq]
      exact hA.sub hB
    simpa only [dist_eq_norm] using hsub.norm
  have hsource : IntegrableOn
      (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖)
      (Set.Ioc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp
      (actualPhysicalSourceNormIntervalIntegrable35V2 u)
  have hsource_s : IntegrableOn
      (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖)
      (Set.Ioc (0 : ℝ) s) volume :=
    hsource.mono_set (Set.Ioc_subset_Ioc le_rfl hs₁)
  have hmajorant_on : IntegrableOn
      (fun r : ℝ => c * ‖actualPhysicalL2SourcePotential u r‖)
      (Set.Ioc (0 : ℝ) s) volume := hsource_s.const_mul c
  have hmajorant : Integrable
      (Set.indicator (Set.Ioc (0 : ℝ) s)
        (fun r : ℝ => c * ‖actualPhysicalL2SourcePotential u r‖)) volume :=
    hmajorant_on.integrable_indicator measurableSet_Ioc
  have hpoint : ∀ᵐ r ∂(volume : Measure ℝ),
      dist (actualPhysicalHeightAmplitude00_35V3 u p.1 p.2 r)
          (actualPhysicalHeightAmplitude00_35V3 u q.1 q.2 r) ≤
        Set.indicator (Set.Ioc (0 : ℝ) s)
          (fun x : ℝ => c * ‖actualPhysicalL2SourcePotential u x‖) r := by
    filter_upwards [] with r
    simpa [p, q, c, dist_eq_norm] using
      actualPhysicalHeightAmplitude00_fixedEndpointLipschitz35V2
        u s Y₀ Y Y' r hs₀ hs₁ hY₀ hY hY'
  have hIntegral := integral_mono_ae hleft hmajorant hpoint
  have hmajorant_integral :
      ∫ r : ℝ, Set.indicator (Set.Ioc (0 : ℝ) s)
        (fun x : ℝ => c * ‖actualPhysicalL2SourcePotential u x‖) r ∂volume =
        c * actualPhysicalSourceNormPrimitive35V2 u s := by
    rw [integral_indicator measurableSet_Ioc, integral_const_mul]
    rw [← intervalIntegral.integral_of_le hs₀]
    rfl
  rw [actualPhysicalHeightAmplitude00Lp1_35V2_dist_eq_integral u Y₀ hY₀ p q]
  calc
    (∫ r : ℝ, dist (actualPhysicalHeightAmplitude00_35V3 u p.1 p.2 r)
        (actualPhysicalHeightAmplitude00_35V3 u q.1 q.2 r) ∂volume)
      ≤ ∫ r : ℝ, Set.indicator (Set.Ioc (0 : ℝ) s)
          (fun x : ℝ => c * ‖actualPhysicalL2SourcePotential u x‖) r ∂volume := hIntegral
    _ = c * actualPhysicalSourceNormPrimitive35V2 u s := hmajorant_integral
  
/-- The actual 11-channel fixed-endpoint estimate retains the unstarred source
and the original negative height exponent. -/
theorem actualPhysicalHeightAmplitude11_fixedEndpointLp1Distance36V3
    (u : PhysicalL2) (Y₀ s Y Y' : ℝ) (hY₀ : 0 ≤ Y₀)
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hY : Y ∈ Set.Icc (0 : ℝ) Y₀) (hY' : Y' ∈ Set.Icc (0 : ℝ) Y₀) :
    dist
      (actualPhysicalHeightAmplitude11Lp1_35V2 u Y₀ hY₀
        ⟨⟨s, ⟨hs₀, hs₁⟩⟩, ⟨Y, hY⟩⟩)
      (actualPhysicalHeightAmplitude11Lp1_35V2 u Y₀ hY₀
        ⟨⟨s, ⟨hs₀, hs₁⟩⟩, ⟨Y', hY'⟩⟩)
      ≤ 2 * Real.exp (2 * Y₀) * |Y - Y'| *
        actualPhysicalSourceNormPrimitive35V2 u s := by
  let p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀ :=
    ⟨⟨s, ⟨hs₀, hs₁⟩⟩, ⟨Y, hY⟩⟩
  let q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀ :=
    ⟨⟨s, ⟨hs₀, hs₁⟩⟩, ⟨Y', hY'⟩⟩
  let c : ℝ := 2 * Real.exp (2 * Y₀) * |Y - Y'|
  have hleft : Integrable (fun r : ℝ =>
      dist (actualPhysicalHeightAmplitude11_35V3 u p.1 p.2 r)
        (actualPhysicalHeightAmplitude11_35V3 u q.1 q.2 r)) volume := by
    have hA := actualPhysicalHeightAmplitude11_integrable35V3 u hs₀ hs₁ hY₀ hY.1 hY.2
    have hB := actualPhysicalHeightAmplitude11_integrable35V3 u hs₀ hs₁ hY₀ hY'.1 hY'.2
    have hsubEq :
        (fun r : ℝ => actualPhysicalHeightAmplitude11_35V3 u p.1 p.2 r -
          actualPhysicalHeightAmplitude11_35V3 u q.1 q.2 r) =
          actualPhysicalHeightAmplitude11_35V3 u p.1 p.2 -
            actualPhysicalHeightAmplitude11_35V3 u q.1 q.2 := by
      funext r
      rfl
    have hsub : Integrable
        (fun r : ℝ => actualPhysicalHeightAmplitude11_35V3 u p.1 p.2 r -
          actualPhysicalHeightAmplitude11_35V3 u q.1 q.2 r) volume := by
      rw [hsubEq]
      exact hA.sub hB
    simpa only [dist_eq_norm] using hsub.norm
  have hsource : IntegrableOn
      (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖)
      (Set.Ioc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp
      (actualPhysicalSourceNormIntervalIntegrable35V2 u)
  have hsource_s : IntegrableOn
      (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖)
      (Set.Ioc (0 : ℝ) s) volume :=
    hsource.mono_set (Set.Ioc_subset_Ioc le_rfl hs₁)
  have hmajorant_on : IntegrableOn
      (fun r : ℝ => c * ‖actualPhysicalL2SourcePotential u r‖)
      (Set.Ioc (0 : ℝ) s) volume := hsource_s.const_mul c
  have hmajorant : Integrable
      (Set.indicator (Set.Ioc (0 : ℝ) s)
        (fun r : ℝ => c * ‖actualPhysicalL2SourcePotential u r‖)) volume :=
    hmajorant_on.integrable_indicator measurableSet_Ioc
  have hpoint : ∀ᵐ r ∂(volume : Measure ℝ),
      dist (actualPhysicalHeightAmplitude11_35V3 u p.1 p.2 r)
          (actualPhysicalHeightAmplitude11_35V3 u q.1 q.2 r) ≤
        Set.indicator (Set.Ioc (0 : ℝ) s)
          (fun x : ℝ => c * ‖actualPhysicalL2SourcePotential u x‖) r := by
    filter_upwards [] with r
    simpa [p, q, c, dist_eq_norm] using
      actualPhysicalHeightAmplitude11_fixedEndpointLipschitz35V2
        u s Y₀ Y Y' r hs₀ hs₁ hY₀ hY hY'
  have hIntegral := integral_mono_ae hleft hmajorant hpoint
  have hmajorant_integral :
      ∫ r : ℝ, Set.indicator (Set.Ioc (0 : ℝ) s)
        (fun x : ℝ => c * ‖actualPhysicalL2SourcePotential u x‖) r ∂volume =
        c * actualPhysicalSourceNormPrimitive35V2 u s := by
    rw [integral_indicator measurableSet_Ioc, integral_const_mul]
    rw [← intervalIntegral.integral_of_le hs₀]
    rfl
  rw [actualPhysicalHeightAmplitude11Lp1_35V2_dist_eq_integral u Y₀ hY₀ p q]
  calc
    (∫ r : ℝ, dist (actualPhysicalHeightAmplitude11_35V3 u p.1 p.2 r)
        (actualPhysicalHeightAmplitude11_35V3 u q.1 q.2 r) ∂volume)
      ≤ ∫ r : ℝ, Set.indicator (Set.Ioc (0 : ℝ) s)
          (fun x : ℝ => c * ‖actualPhysicalL2SourcePotential u x‖) r ∂volume := hIntegral
    _ = c * actualPhysicalSourceNormPrimitive35V2 u s := hmajorant_integral

end NlsGge.SpectralFoundations
end
