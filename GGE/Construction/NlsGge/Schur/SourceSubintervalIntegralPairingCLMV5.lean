import NlsGge.Schur.SourceIntervalWeakPairingLimit
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import NlsGge.Schur.SourceSubintervalIndicatorAEEqPrerequisiteV1

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur

/-- The L² test function equal to one on the actual source subinterval `(0,t]`. -/
def sourceSubintervalIndicator (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    SourceIntervalL2 :=
  MeasureTheory.indicatorConstLp (s := Set.Ioc (0 : ℝ) t)
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) 2
    measurableSet_Ioc (by exact (MeasureTheory.measure_lt_top _ _).ne) (1 : ℂ)

/-- Pairing with the subinterval indicator is exactly the actual source
interval integral. This gives a bounded linear L² functional for each `t`;
no representative or pointwise regularity assumption is made on `f`. -/
theorem sourceIntervalTestPairing_sourceSubintervalIntegral
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (f : SourceIntervalL2) :
    sourceIntervalTestPairing (sourceSubintervalIndicator t ht) f =
      ∫ x in (0 : ℝ)..t, f x := by
  let μ : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)
  let S : Set ℝ := Set.Ioc (0 : ℝ) t
  have hS : S ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 ht.2⟩
  have htest : sourceSubintervalIndicator t ht =ᵐ[μ]
      S.indicator (fun _ : ℝ => (1 : ℂ)) := by
    simpa [sourceSubintervalIndicator, μ, S] using
      (indicatorConstLp_sourceSubinterval_ae t)
  rw [sourceIntervalTestPairing_integral]
  rw [intervalIntegral.integral_of_le ht.1]
  change (∫ x, f x * sourceSubintervalIndicator t ht x ∂μ) =
    ∫ x, f x ∂(MeasureTheory.volume.restrict S)
  calc
    (∫ x, f x * sourceSubintervalIndicator t ht x ∂μ) =
        ∫ x, S.indicator f x ∂μ := by
      apply integral_congr_ae
      filter_upwards [htest] with x hx
      by_cases hxs : x ∈ S
      · simp only [Set.indicator_of_mem hxs] at hx ⊢
        simpa [hx]
      · simp only [Set.indicator_of_notMem hxs] at hx ⊢
        simp [hx]
    _ = ∫ x, f x ∂(μ.restrict S) := by
      exact MeasureTheory.integral_indicator (μ := μ) (f := (f : ℝ → ℂ))
        (s := S) measurableSet_Ioc
    _ = ∫ x, f x ∂(MeasureTheory.volume.restrict S) := by
      rw [Measure.restrict_restrict_of_subset hS]

/-- The subinterval integration functional is the existing actual continuous
linear pairing with the indicator test. -/
def sourceSubintervalIntegralCLM (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : SourceIntervalL2 →L[ℂ] ℂ :=
  sourceIntervalTestPairing (sourceSubintervalIndicator t ht)

theorem sourceSubintervalIntegralCLM_apply (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (f : SourceIntervalL2) :
    sourceSubintervalIntegralCLM t ht f = ∫ x in (0 : ℝ)..t, f x := by
  exact sourceIntervalTestPairing_sourceSubintervalIntegral t ht f

end NlsGge.Schur

end
