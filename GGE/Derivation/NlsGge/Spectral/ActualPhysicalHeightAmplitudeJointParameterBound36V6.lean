import NlsGge.Spectral.ActualPhysicalHeightAmplitudeFixedEndpointLp1Distance36V3
import NlsGge.Spectral.ActualPhysicalHeightAmplitudeOrderedEndpointLp1Distance36V4

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis

/-- The actual source-norm primitive is monotone on its physical interval. -/
theorem actualPhysicalSourceNormPrimitive35V2_mono36V3
    (u : PhysicalL2) {s s' : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hs' : s' ∈ Set.Icc (0 : ℝ) 1)
    (hss' : s ≤ s') :
    actualPhysicalSourceNormPrimitive35V2 u s ≤
      actualPhysicalSourceNormPrimitive35V2 u s' := by
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) s')]
        (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖) :=
    ae_of_all _ (fun _ => norm_nonneg _)
  have hs'Icc : s' ∈ Set.uIcc (0 : ℝ) 1 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs'
  have hsourceS' : IntervalIntegrable
      (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖) volume 0 s' :=
    (actualPhysicalSourceNormIntervalIntegrable35V2 u).mono_set
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc hs'Icc)
  have hmono := intervalIntegral.integral_mono_interval
    (a := (0 : ℝ)) (b := s) (c := (0 : ℝ)) (d := s')
    le_rfl hs.1 hss' hnonneg
    hsourceS'
  simpa only [actualPhysicalSourceNormPrimitive35V2] using hmono

/-- Actual 00 L¹ amplitude family on the physical endpoint/height rectangle. -/
def actualPhysicalHeightAmplitude00Family36V6
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) :
    Lp (α := ℝ) ℂ 1 (volume : Measure ℝ) :=
  actualPhysicalHeightAmplitude00Lp1_35V2 u Y₀ hY₀ p

/-- Actual 00 family distance splits into the source-primitive endpoint
increment and the fixed-endpoint height variation. -/
theorem actualPhysicalHeightAmplitude00Family36V6_dist_bound
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) :
    dist (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ p)
      (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ q) ≤
      Real.exp (2 * Y₀) *
          |actualPhysicalSourceNormPrimitive35V2 u p.1 -
            actualPhysicalSourceNormPrimitive35V2 u q.1| +
        2 * Real.exp (2 * Y₀) *
          |(p.2 : ℝ) - (q.2 : ℝ)| * actualPhysicalSourceNormPrimitive35V2 u 1 := by
  let mid : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀ := ⟨p.1, q.2⟩
  have htri := dist_triangle
    (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ p)
    (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ mid)
    (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ q)
  have hheight := actualPhysicalHeightAmplitude00_fixedEndpointLp1Distance36V3
    u Y₀ p.1.1 p.2 q.2 hY₀ p.1.2.1 p.1.2.2 p.2.2 q.2.2
  have hGs : actualPhysicalSourceNormPrimitive35V2 u p.1 ≤
      actualPhysicalSourceNormPrimitive35V2 u 1 :=
    actualPhysicalSourceNormPrimitive35V2_mono36V3 u p.1.2
      ⟨by norm_num, le_rfl⟩ p.1.2.2
  have hheight' :
      dist (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ p)
        (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ mid) ≤
        2 * Real.exp (2 * Y₀) * |(p.2 : ℝ) - (q.2 : ℝ)| *
          actualPhysicalSourceNormPrimitive35V2 u 1 := by
    calc
      _ ≤ 2 * Real.exp (2 * Y₀) * |(p.2 : ℝ) - (q.2 : ℝ)| *
          actualPhysicalSourceNormPrimitive35V2 u p.1 := by
            simpa [actualPhysicalHeightAmplitude00Family36V6, mid] using hheight
      _ ≤ 2 * Real.exp (2 * Y₀) * |(p.2 : ℝ) - (q.2 : ℝ)| *
          actualPhysicalSourceNormPrimitive35V2 u 1 :=
            mul_le_mul_of_nonneg_left hGs (by positivity)
  have hend :
      dist (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ mid)
        (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ q) ≤
        Real.exp (2 * Y₀) *
          |actualPhysicalSourceNormPrimitive35V2 u p.1 -
            actualPhysicalSourceNormPrimitive35V2 u q.1| := by
    by_cases horder : p.1.1 ≤ q.1.1
    · have hgap := actualPhysicalSourceNormPrimitive35V2_mono36V3 u p.1.2 q.1.2 horder
      have hordered := actualPhysicalHeightAmplitude00_orderedEndpointLp1Distance36V4
        u Y₀ p.1.1 q.1.1 q.2 hY₀ p.1.2.1 horder q.1.2.2 q.2.2
      have habs :
          |actualPhysicalSourceNormPrimitive35V2 u p.1 -
            actualPhysicalSourceNormPrimitive35V2 u q.1| =
            actualPhysicalSourceNormPrimitive35V2 u q.1 -
              actualPhysicalSourceNormPrimitive35V2 u p.1 := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hgap)]
      simpa [actualPhysicalHeightAmplitude00Family36V6, mid, habs] using hordered
    · have horder' : q.1.1 ≤ p.1.1 := le_of_not_ge horder
      have hgap := actualPhysicalSourceNormPrimitive35V2_mono36V3 u q.1.2 p.1.2 horder'
      have hordered := actualPhysicalHeightAmplitude00_orderedEndpointLp1Distance36V4
        u Y₀ q.1.1 p.1.1 q.2 hY₀ q.1.2.1 horder' p.1.2.2 q.2.2
      have habs :
          |actualPhysicalSourceNormPrimitive35V2 u p.1 -
            actualPhysicalSourceNormPrimitive35V2 u q.1| =
            actualPhysicalSourceNormPrimitive35V2 u p.1 -
              actualPhysicalSourceNormPrimitive35V2 u q.1 :=
        abs_of_nonneg (sub_nonneg.mpr hgap)
      simpa [actualPhysicalHeightAmplitude00Family36V6, mid, dist_comm, habs] using hordered
  calc
    dist (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ p)
        (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ q)
        ≤ dist (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ p)
            (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ mid) +
          dist (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ mid)
            (actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀ q) := htri
    _ ≤ 2 * Real.exp (2 * Y₀) * |(p.2 : ℝ) - (q.2 : ℝ)| *
          actualPhysicalSourceNormPrimitive35V2 u 1 +
        Real.exp (2 * Y₀) *
          |actualPhysicalSourceNormPrimitive35V2 u p.1 -
            actualPhysicalSourceNormPrimitive35V2 u q.1| :=
          add_le_add hheight' hend
    _ = Real.exp (2 * Y₀) *
          |actualPhysicalSourceNormPrimitive35V2 u p.1 -
            actualPhysicalSourceNormPrimitive35V2 u q.1| +
        2 * Real.exp (2 * Y₀) * |(p.2 : ℝ) - (q.2 : ℝ)| *
          actualPhysicalSourceNormPrimitive35V2 u 1 := by ring

/-- Actual 11 L¹ amplitude family on the physical endpoint/height rectangle. -/
def actualPhysicalHeightAmplitude11Family36V6
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) :
    Lp (α := ℝ) ℂ 1 (volume : Measure ℝ) :=
  actualPhysicalHeightAmplitude11Lp1_35V2 u Y₀ hY₀ p

/-- Actual 11 family distance has the same physical source-primitive modulus,
with its original unstarred source. -/
theorem actualPhysicalHeightAmplitude11Family36V6_dist_bound
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) :
    dist (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ p)
      (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ q) ≤
      Real.exp (2 * Y₀) *
          |actualPhysicalSourceNormPrimitive35V2 u p.1 -
            actualPhysicalSourceNormPrimitive35V2 u q.1| +
        2 * Real.exp (2 * Y₀) *
          |(p.2 : ℝ) - (q.2 : ℝ)| * actualPhysicalSourceNormPrimitive35V2 u 1 := by
  let mid : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀ := ⟨p.1, q.2⟩
  have htri := dist_triangle
    (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ p)
    (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ mid)
    (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ q)
  have hheight := actualPhysicalHeightAmplitude11_fixedEndpointLp1Distance36V3
    u Y₀ p.1.1 p.2 q.2 hY₀ p.1.2.1 p.1.2.2 p.2.2 q.2.2
  have hGs : actualPhysicalSourceNormPrimitive35V2 u p.1 ≤
      actualPhysicalSourceNormPrimitive35V2 u 1 :=
    actualPhysicalSourceNormPrimitive35V2_mono36V3 u p.1.2
      ⟨by norm_num, le_rfl⟩ p.1.2.2
  have hheight' :
      dist (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ p)
        (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ mid) ≤
        2 * Real.exp (2 * Y₀) * |(p.2 : ℝ) - (q.2 : ℝ)| *
          actualPhysicalSourceNormPrimitive35V2 u 1 := by
    calc
      _ ≤ 2 * Real.exp (2 * Y₀) * |(p.2 : ℝ) - (q.2 : ℝ)| *
          actualPhysicalSourceNormPrimitive35V2 u p.1 := by
            simpa [actualPhysicalHeightAmplitude11Family36V6, mid] using hheight
      _ ≤ 2 * Real.exp (2 * Y₀) * |(p.2 : ℝ) - (q.2 : ℝ)| *
          actualPhysicalSourceNormPrimitive35V2 u 1 :=
            mul_le_mul_of_nonneg_left hGs (by positivity)
  have hend :
      dist (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ mid)
        (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ q) ≤
        Real.exp (2 * Y₀) *
          |actualPhysicalSourceNormPrimitive35V2 u p.1 -
            actualPhysicalSourceNormPrimitive35V2 u q.1| := by
    by_cases horder : p.1.1 ≤ q.1.1
    · have hgap := actualPhysicalSourceNormPrimitive35V2_mono36V3 u p.1.2 q.1.2 horder
      have hordered := actualPhysicalHeightAmplitude11_orderedEndpointLp1Distance36V4
        u Y₀ p.1.1 q.1.1 q.2 hY₀ p.1.2.1 horder q.1.2.2 q.2.2
      have habs :
          |actualPhysicalSourceNormPrimitive35V2 u p.1 -
            actualPhysicalSourceNormPrimitive35V2 u q.1| =
            actualPhysicalSourceNormPrimitive35V2 u q.1 -
              actualPhysicalSourceNormPrimitive35V2 u p.1 := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hgap)]
      simpa [actualPhysicalHeightAmplitude11Family36V6, mid, habs] using hordered
    · have horder' : q.1.1 ≤ p.1.1 := le_of_not_ge horder
      have hgap := actualPhysicalSourceNormPrimitive35V2_mono36V3 u q.1.2 p.1.2 horder'
      have hordered := actualPhysicalHeightAmplitude11_orderedEndpointLp1Distance36V4
        u Y₀ q.1.1 p.1.1 q.2 hY₀ q.1.2.1 horder' p.1.2.2 q.2.2
      have habs :
          |actualPhysicalSourceNormPrimitive35V2 u p.1 -
            actualPhysicalSourceNormPrimitive35V2 u q.1| =
            actualPhysicalSourceNormPrimitive35V2 u p.1 -
              actualPhysicalSourceNormPrimitive35V2 u q.1 :=
        abs_of_nonneg (sub_nonneg.mpr hgap)
      simpa [actualPhysicalHeightAmplitude11Family36V6, mid, dist_comm, habs] using hordered
  calc
    dist (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ p)
        (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ q)
        ≤ dist (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ p)
            (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ mid) +
          dist (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ mid)
            (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ q) := htri
    _ ≤ 2 * Real.exp (2 * Y₀) * |(p.2 : ℝ) - (q.2 : ℝ)| *
          actualPhysicalSourceNormPrimitive35V2 u 1 +
        Real.exp (2 * Y₀) *
          |actualPhysicalSourceNormPrimitive35V2 u p.1 -
            actualPhysicalSourceNormPrimitive35V2 u q.1| :=
          add_le_add hheight' hend
    _ = Real.exp (2 * Y₀) *
          |actualPhysicalSourceNormPrimitive35V2 u p.1 -
            actualPhysicalSourceNormPrimitive35V2 u q.1| +
        2 * Real.exp (2 * Y₀) * |(p.2 : ℝ) - (q.2 : ℝ)| *
          actualPhysicalSourceNormPrimitive35V2 u 1 := by ring

end NlsGge.SpectralFoundations
end
