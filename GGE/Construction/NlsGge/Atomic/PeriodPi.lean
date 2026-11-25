import NlsGge.Atomic.IntervalZSAction

/-! Literal normalized interval carriers for the period-pi Dirac rescaling.
The H1 carrier is the distributional derivative graph. Regular representatives,
endpoint traces, unitary transport and operator identities are theorem obligations. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.PeriodPi

open MeasureTheory Set
open scoped ContDiff ENNReal

/-- Lebesgue measure on `(0,pi]`, normalized to total mass one. -/
def normalizedMeasure : Measure ℝ :=
  ENNReal.ofReal (Real.pi⁻¹) • volume.restrict (Ioc (0 : ℝ) Real.pi)

/-- The actual normalized scalar L2 carrier on the period-pi interval. -/
abbrev SourceIntervalL2 := Lp ℂ 2 normalizedMeasure

/-- The Hilbert pair norm; `true` denotes the upper component as on the unit interval. -/
abbrev SourcePairL2 := PiLp 2 (fun _ : Bool => SourceIntervalL2)

/-- The literal compact-interior-test derivative equation, with no boundary relation. -/
def HasWeakDerivative (f g : ℝ → ℂ) : Prop :=
  ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Ioo (0 : ℝ) Real.pi →
      (∫ x in (0 : ℝ)..Real.pi, f x * ((deriv ψ x : ℝ) : ℂ)) =
        -(∫ x in (0 : ℝ)..Real.pi, g x * (ψ x : ℂ))

/-- Actual L2 value and derivative with the weak equation; no regularity conclusion assumed. -/
structure H1 where
  value : SourceIntervalL2
  derivative : SourceIntervalL2
  weak : HasWeakDerivative value derivative

/-- Pointwise affine pullback. -/
def rescaleValue (f : ℝ → ℂ) : ℝ → ℂ := fun t => f (Real.pi * t)

/-- Pointwise candidate derivative; the chain-rule theorem must justify its use. -/
def rescaleDerivative (g : ℝ → ℂ) : ℝ → ℂ :=
  fun t => (Real.pi : ℂ) * g (Real.pi * t)

end NlsGge.Atomic.PeriodPi
