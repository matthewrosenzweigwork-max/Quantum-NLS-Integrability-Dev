import NlsGge.Spectral.ActualL2PotentialTimesLInfStateV1
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis

/-- The actual period-one source parent measure. -/
def actualPhysicalUnitSourceMeasure35 : Measure ℝ :=
  volume.restrict (Set.Ioc (0 : ℝ) 1)

/-- The zero-extended 00-channel height amplitude. Its source is the actual
physical source-interval L² representative, and its support is the actual
variable interval `(0,s]`. -/
def actualPhysicalHeightAmplitude00_35V3 (u : PhysicalL2) (s Y : ℝ) : ℝ → ℂ :=
  Set.indicator (Set.Ioc (0 : ℝ) s) fun r =>
    star (actualPhysicalL2SourcePotential u r) * Complex.exp ((2 * Y * r : ℝ) : ℂ)

/-- The zero-extended 11-channel height amplitude, with the actual unstarred
source and the opposite real height sign. -/
def actualPhysicalHeightAmplitude11_35V3 (u : PhysicalL2) (s Y : ℝ) : ℝ → ℂ :=
  Set.indicator (Set.Ioc (0 : ℝ) s) fun r =>
    actualPhysicalL2SourcePotential u r * Complex.exp ((-2 * Y * r : ℝ) : ℂ)

/-- First concrete prerequisite: the actual 00 amplitude is integrable on full
real-line volume for bounded physical parameters. No continuity, Fourier limit,
or compact-family premise is assumed here. -/
theorem actualPhysicalHeightAmplitude00_integrable35V3
    (u : PhysicalL2) {s Y Y₀ : ℝ}
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hY₀ : 0 ≤ Y₀) (hY : 0 ≤ Y) (hYY₀ : Y ≤ Y₀) :
    Integrable (actualPhysicalHeightAmplitude00_35V3 u s Y) volume := by
  let μ₁ := actualPhysicalUnitSourceMeasure35
  let U : ℝ → ℂ := actualPhysicalL2SourcePotential u
  haveI : IsFiniteMeasure μ₁ := by
    dsimp [μ₁, actualPhysicalUnitSourceMeasure35]
    exact Real.isFiniteMeasure_restrict_Ioc 0 1
  have hU₂ : MemLp U 2 μ₁ := by
    change MemLp (actualPhysicalL2SourcePotential u) 2 μ₁
    exact Lp.memLp (actualPhysicalL2SourcePotential u)
  have hU : Integrable U μ₁ :=
    hU₂.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hsubset : Set.Ioc (0 : ℝ) s ⊆ Set.Ioc 0 1 := by
    intro r hr
    exact ⟨hr.1, hr.2.trans hs₁⟩
  have hμs : volume.restrict (Set.Ioc (0 : ℝ) s) ≤ μ₁ := by
    dsimp [μ₁, actualPhysicalUnitSourceMeasure35]
    exact Measure.restrict_mono_set volume hsubset
  have hUs : Integrable U (volume.restrict (Set.Ioc (0 : ℝ) s)) :=
    hU.mono_measure hμs
  have hdom : Integrable (fun r : ℝ => Real.exp (2 * Y₀) * ‖U r‖)
      (volume.restrict (Set.Ioc (0 : ℝ) s)) := by
    exact hUs.norm.const_mul (Real.exp (2 * Y₀))
  have hweight : AEStronglyMeasurable
      (fun r : ℝ => star (U r) * Complex.exp ((2 * Y * r : ℝ) : ℂ))
      (volume.restrict (Set.Ioc (0 : ℝ) s)) := by
    exact hUs.aestronglyMeasurable.star.mul (by fun_prop)
  have hbound : ∀ᵐ r ∂(volume.restrict (Set.Ioc (0 : ℝ) s)),
      ‖star (U r) * Complex.exp ((2 * Y * r : ℝ) : ℂ)‖ ≤
        Real.exp (2 * Y₀) * ‖U r‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 ≤ r := le_of_lt hr.1
    have hr1 : r ≤ 1 := hr.2.trans hs₁
    have harg : 2 * Y * r ≤ 2 * Y₀ := by nlinarith [hY, hYY₀, hr0, hr1]
    have hexp : Real.exp (2 * Y * r) ≤ Real.exp (2 * Y₀) := Real.exp_le_exp.mpr harg
    calc
      ‖star (U r) * Complex.exp ((2 * Y * r : ℝ) : ℂ)‖ =
          ‖U r‖ * Real.exp (2 * Y * r) := by
            rw [norm_mul, norm_star, Complex.norm_exp]
            simp
      _ ≤ ‖U r‖ * Real.exp (2 * Y₀) :=
          mul_le_mul_of_nonneg_left hexp (norm_nonneg (U r))
      _ = Real.exp (2 * Y₀) * ‖U r‖ := by ring
  have hweighted : Integrable
      (fun r : ℝ => star (U r) * Complex.exp ((2 * Y * r : ℝ) : ℂ))
      (volume.restrict (Set.Ioc (0 : ℝ) s)) :=
    hdom.mono' hweight hbound
  have hweightedOn : IntegrableOn
      (fun r : ℝ => star (U r) * Complex.exp ((2 * Y * r : ℝ) : ℂ))
      (Set.Ioc (0 : ℝ) s) volume := hweighted
  simpa [actualPhysicalHeightAmplitude00_35V3, U] using
    hweightedOn.integrable_indicator measurableSet_Ioc

/-- First concrete prerequisite: the actual 11 amplitude is integrable on full
real-line volume for bounded physical parameters. -/
theorem actualPhysicalHeightAmplitude11_integrable35V3
    (u : PhysicalL2) {s Y Y₀ : ℝ}
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hY₀ : 0 ≤ Y₀) (hY : 0 ≤ Y) (hYY₀ : Y ≤ Y₀) :
    Integrable (actualPhysicalHeightAmplitude11_35V3 u s Y) volume := by
  let μ₁ := actualPhysicalUnitSourceMeasure35
  let U : ℝ → ℂ := actualPhysicalL2SourcePotential u
  haveI : IsFiniteMeasure μ₁ := by
    dsimp [μ₁, actualPhysicalUnitSourceMeasure35]
    exact Real.isFiniteMeasure_restrict_Ioc 0 1
  have hU₂ : MemLp U 2 μ₁ := by
    change MemLp (actualPhysicalL2SourcePotential u) 2 μ₁
    exact Lp.memLp (actualPhysicalL2SourcePotential u)
  have hU : Integrable U μ₁ :=
    hU₂.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hsubset : Set.Ioc (0 : ℝ) s ⊆ Set.Ioc 0 1 := by
    intro r hr
    exact ⟨hr.1, hr.2.trans hs₁⟩
  have hμs : volume.restrict (Set.Ioc (0 : ℝ) s) ≤ μ₁ := by
    dsimp [μ₁, actualPhysicalUnitSourceMeasure35]
    exact Measure.restrict_mono_set volume hsubset
  have hUs : Integrable U (volume.restrict (Set.Ioc (0 : ℝ) s)) :=
    hU.mono_measure hμs
  have hdom : Integrable (fun r : ℝ => Real.exp (2 * Y₀) * ‖U r‖)
      (volume.restrict (Set.Ioc (0 : ℝ) s)) := by
    exact hUs.norm.const_mul (Real.exp (2 * Y₀))
  have hweight : AEStronglyMeasurable
      (fun r : ℝ => U r * Complex.exp ((-2 * Y * r : ℝ) : ℂ))
      (volume.restrict (Set.Ioc (0 : ℝ) s)) := by
    exact hUs.aestronglyMeasurable.mul (by fun_prop)
  have hbound : ∀ᵐ r ∂(volume.restrict (Set.Ioc (0 : ℝ) s)),
      ‖U r * Complex.exp ((-2 * Y * r : ℝ) : ℂ)‖ ≤
        Real.exp (2 * Y₀) * ‖U r‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 ≤ r := le_of_lt hr.1
    have hr1 : r ≤ 1 := hr.2.trans hs₁
    have harg : -2 * Y * r ≤ 2 * Y₀ := by nlinarith [hY, hY₀, hr0, hr1]
    have hexp : Real.exp (-2 * Y * r) ≤ Real.exp (2 * Y₀) := Real.exp_le_exp.mpr harg
    calc
      ‖U r * Complex.exp ((-2 * Y * r : ℝ) : ℂ)‖ =
          ‖U r‖ * Real.exp (-2 * Y * r) := by
            rw [norm_mul, Complex.norm_exp]
            simp
      _ ≤ ‖U r‖ * Real.exp (2 * Y₀) :=
          mul_le_mul_of_nonneg_left hexp (norm_nonneg (U r))
      _ = Real.exp (2 * Y₀) * ‖U r‖ := by ring
  have hweighted : Integrable
      (fun r : ℝ => U r * Complex.exp ((-2 * Y * r : ℝ) : ℂ))
      (volume.restrict (Set.Ioc (0 : ℝ) s)) :=
    hdom.mono' hweight hbound
  have hweightedOn : IntegrableOn
      (fun r : ℝ => U r * Complex.exp ((-2 * Y * r : ℝ) : ℂ))
      (Set.Ioc (0 : ℝ) s) volume := hweighted
  simpa [actualPhysicalHeightAmplitude11_35V3, U] using
    hweightedOn.integrable_indicator measurableSet_Ioc

/-- The full-volume L¹ witnesses above are exactly the MemLp(1) witnesses
used to construct the Fourier-family classes. -/
theorem actualPhysicalHeightAmplitude00_memLpOne35V3
    (u : PhysicalL2) {s Y Y₀ : ℝ}
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hY₀ : 0 ≤ Y₀) (hY : 0 ≤ Y) (hYY₀ : Y ≤ Y₀) :
    MemLp (actualPhysicalHeightAmplitude00_35V3 u s Y) 1 volume :=
  memLp_one_iff_integrable.mpr
    (actualPhysicalHeightAmplitude00_integrable35V3 u hs₀ hs₁ hY₀ hY hYY₀)

theorem actualPhysicalHeightAmplitude11_memLpOne35V3
    (u : PhysicalL2) {s Y Y₀ : ℝ}
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hY₀ : 0 ≤ Y₀) (hY : 0 ≤ Y) (hYY₀ : Y ≤ Y₀) :
    MemLp (actualPhysicalHeightAmplitude11_35V3 u s Y) 1 volume :=
  memLp_one_iff_integrable.mpr
    (actualPhysicalHeightAmplitude11_integrable35V3 u hs₀ hs₁ hY₀ hY hYY₀)

end NlsGge.SpectralFoundations
end
