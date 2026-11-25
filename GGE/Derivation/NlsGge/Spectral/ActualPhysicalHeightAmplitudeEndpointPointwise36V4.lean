import NlsGge.Measure.ActualPhysicalBoundedHeightAmplitudeLp1Prerequisite35V3

set_option autoImplicit false
noncomputable section

namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis

/-- For ordered physical endpoints, the 00 amplitude difference is supported
on the actual interval between the endpoints, with the physical conjugated
source and its bounded-height weight. -/
theorem actualPhysicalHeightAmplitude00_orderedEndpointPointwise36V4
    (u : PhysicalL2) (Y₀ s s' Y r : ℝ)
    (hY₀ : 0 ≤ Y₀) (hs₀ : 0 ≤ s) (hss' : s ≤ s') (hs'₁ : s' ≤ 1)
    (hY : Y ∈ Set.Icc (0 : ℝ) Y₀) :
    ‖actualPhysicalHeightAmplitude00_35V3 u s Y r -
        actualPhysicalHeightAmplitude00_35V3 u s' Y r‖ ≤
      Set.indicator (Set.Ioc s s')
        (fun x : ℝ => Real.exp (2 * Y₀) *
          ‖actualPhysicalL2SourcePotential u x‖) r := by
  have hsubset : Set.Ioc (0 : ℝ) s ⊆ Set.Ioc (0 : ℝ) s' :=
    Set.Ioc_subset_Ioc le_rfl hss'
  by_cases hrA : r ∈ Set.Ioc (0 : ℝ) s
  · have hrB : r ∈ Set.Ioc (0 : ℝ) s' := hsubset hrA
    have hrDiff : r ∉ Set.Ioc s s' := by
      intro h
      exact (not_lt_of_ge hrA.2) h.1
    simp [actualPhysicalHeightAmplitude00_35V3, hrA, hrB, hrDiff]
  · by_cases hrB : r ∈ Set.Ioc (0 : ℝ) s'
    · have hrsr : s < r := by
        by_contra h
        exact hrA ⟨hrB.1, le_of_not_gt h⟩
      have hrDiff : r ∈ Set.Ioc s s' := ⟨hrsr, hrB.2⟩
      have hr0 : 0 ≤ r := le_of_lt hrB.1
      have hr1 : r ≤ 1 := hrB.2.trans hs'₁
      have hYr : Y * r ≤ Y₀ := by
        calc
          Y * r ≤ Y₀ * r := mul_le_mul_of_nonneg_right hY.2 hr0
          _ ≤ Y₀ := by nlinarith [mul_le_mul_of_nonneg_left hr1 hY₀]
      have harg : 2 * Y * r ≤ 2 * Y₀ := by nlinarith
      have hexp : Real.exp (2 * Y * r) ≤ Real.exp (2 * Y₀) :=
        Real.exp_le_exp.mpr harg
      have hnorm :
          ‖star (actualPhysicalL2SourcePotential u r) *
              Complex.exp ((2 * Y * r : ℝ) : ℂ)‖ =
            ‖actualPhysicalL2SourcePotential u r‖ * Real.exp (2 * Y * r) := by
        rw [norm_mul, norm_star, Complex.norm_exp]
        simp
      simp only [actualPhysicalHeightAmplitude00_35V3,
        Set.indicator_of_notMem hrA, Set.indicator_of_mem hrB,
        Set.indicator_of_mem hrDiff]
      calc
        ‖0 - (star (actualPhysicalL2SourcePotential u r) *
            Complex.exp ((2 * Y * r : ℝ) : ℂ))‖
            = ‖actualPhysicalL2SourcePotential u r‖ * Real.exp (2 * Y * r) := by
              rw [zero_sub, norm_neg, hnorm]
        _ ≤ ‖actualPhysicalL2SourcePotential u r‖ * Real.exp (2 * Y₀) :=
          mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
        _ = Real.exp (2 * Y₀) * ‖actualPhysicalL2SourcePotential u r‖ := by ring
    · have hrDiff : r ∉ Set.Ioc s s' := by
        intro h
        exact hrB ⟨lt_of_le_of_lt hs₀ h.1, h.2⟩
      simp [actualPhysicalHeightAmplitude00_35V3, hrA, hrB, hrDiff]

/-- The same ordered-endpoint support statement for the actual 11 channel,
with unstarred source and the original negative height exponent. -/
theorem actualPhysicalHeightAmplitude11_orderedEndpointPointwise36V4
    (u : PhysicalL2) (Y₀ s s' Y r : ℝ)
    (hY₀ : 0 ≤ Y₀) (hs₀ : 0 ≤ s) (hss' : s ≤ s') (hs'₁ : s' ≤ 1)
    (hY : Y ∈ Set.Icc (0 : ℝ) Y₀) :
    ‖actualPhysicalHeightAmplitude11_35V3 u s Y r -
        actualPhysicalHeightAmplitude11_35V3 u s' Y r‖ ≤
      Set.indicator (Set.Ioc s s')
        (fun x : ℝ => Real.exp (2 * Y₀) *
          ‖actualPhysicalL2SourcePotential u x‖) r := by
  have hsubset : Set.Ioc (0 : ℝ) s ⊆ Set.Ioc (0 : ℝ) s' :=
    Set.Ioc_subset_Ioc le_rfl hss'
  by_cases hrA : r ∈ Set.Ioc (0 : ℝ) s
  · have hrB : r ∈ Set.Ioc (0 : ℝ) s' := hsubset hrA
    have hrDiff : r ∉ Set.Ioc s s' := by
      intro h
      exact (not_lt_of_ge hrA.2) h.1
    simp [actualPhysicalHeightAmplitude11_35V3, hrA, hrB, hrDiff]
  · by_cases hrB : r ∈ Set.Ioc (0 : ℝ) s'
    · have hrsr : s < r := by
        by_contra h
        exact hrA ⟨hrB.1, le_of_not_gt h⟩
      have hrDiff : r ∈ Set.Ioc s s' := ⟨hrsr, hrB.2⟩
      have hr0 : 0 ≤ r := le_of_lt hrB.1
      have hr1 : r ≤ 1 := hrB.2.trans hs'₁
      have hYr : Y * r ≤ Y₀ := by
        calc
          Y * r ≤ Y₀ * r := mul_le_mul_of_nonneg_right hY.2 hr0
          _ ≤ Y₀ := by nlinarith [mul_le_mul_of_nonneg_left hr1 hY₀]
      have harg : -2 * Y * r ≤ 2 * Y₀ := by nlinarith [hY.1, hr0]
      have hexp : Real.exp (-2 * Y * r) ≤ Real.exp (2 * Y₀) :=
        Real.exp_le_exp.mpr harg
      have hnorm :
          ‖actualPhysicalL2SourcePotential u r *
              Complex.exp ((-2 * Y * r : ℝ) : ℂ)‖ =
            ‖actualPhysicalL2SourcePotential u r‖ * Real.exp (-2 * Y * r) := by
        rw [norm_mul, Complex.norm_exp]
        simp
      simp only [actualPhysicalHeightAmplitude11_35V3,
        Set.indicator_of_notMem hrA, Set.indicator_of_mem hrB,
        Set.indicator_of_mem hrDiff]
      calc
        ‖0 - (actualPhysicalL2SourcePotential u r *
            Complex.exp ((-2 * Y * r : ℝ) : ℂ))‖
            = ‖actualPhysicalL2SourcePotential u r‖ * Real.exp (-2 * Y * r) := by
              rw [zero_sub, norm_neg, hnorm]
        _ ≤ ‖actualPhysicalL2SourcePotential u r‖ * Real.exp (2 * Y₀) :=
          mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
        _ = Real.exp (2 * Y₀) * ‖actualPhysicalL2SourcePotential u r‖ := by ring
    · have hrDiff : r ∉ Set.Ioc s s' := by
        intro h
        exact hrB ⟨lt_of_le_of_lt hs₀ h.1, h.2⟩
      simp [actualPhysicalHeightAmplitude11_35V3, hrA, hrB, hrDiff]

end NlsGge.SpectralFoundations
end
