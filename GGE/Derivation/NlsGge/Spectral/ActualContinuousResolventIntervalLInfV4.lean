import NlsGge.Spectral.ActualFullImaginaryFreeResolventContinuousNormBoundV4
import NlsGge.Schur.ActualSourceIntervalMeasureMassV1
import NlsGge.Schur.PhysicalSector
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur

private abbrev actualSourceIntervalMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc (0 : ℝ) 1)

/-- Restrict a continuous function on the actual doubled source circle to the
unit source interval as a bounded continuous function on `ℝ`. The global
periodic representative is used so the interval restriction is a genuine
`Lp ℂ ∞` element, rather than an unjustified cast from `L²`. -/
private def continuousSourceIntervalBCF (F : C(SpectralCircle, ℂ)) : BoundedContinuousFunction ℝ ℂ where
  toFun t := F ((t : ℝ) : SpectralCircle)
  continuous_toFun := F.continuous.comp (AddCircle.continuous_mk' (2 : ℝ))
  map_bounded' := by
    refine ⟨2 * ‖F‖, ?_⟩
    intro x y
    rw [dist_eq_norm]
    calc
      ‖F ((x : ℝ) : SpectralCircle) - F ((y : ℝ) : SpectralCircle)‖ ≤
          ‖F ((x : ℝ) : SpectralCircle)‖ + ‖F ((y : ℝ) : SpectralCircle)‖ := norm_sub_le _ _
      _ ≤ ‖F‖ + ‖F‖ := add_le_add (F.norm_coe_le_norm _) (F.norm_coe_le_norm _)
      _ = 2 * ‖F‖ := by ring

private theorem continuousSourceIntervalBCF_norm_le (F : C(SpectralCircle, ℂ)) :
    ‖continuousSourceIntervalBCF F‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le_of_nonempty
    (f := continuousSourceIntervalBCF F) (M := ‖F‖)).2
  intro t
  exact F.norm_coe_le_norm ((t : ℝ) : SpectralCircle)

/-- The continuous periodic representative defines an actual source-interval
L-infinity class. -/
private def continuousSourceIntervalLInf (F : C(SpectralCircle, ℂ)) :
    Lp ℂ ∞ (actualSourceIntervalMeasure) :=
  BoundedContinuousFunction.toLp ∞ actualSourceIntervalMeasure ℂ
    (continuousSourceIntervalBCF F)

private theorem continuousSourceIntervalLInf_ae (F : C(SpectralCircle, ℂ)) :
    (continuousSourceIntervalLInf F : ℝ → ℂ) =ᵐ[actualSourceIntervalMeasure]
      fun t => F ((t : ℝ) : SpectralCircle) := by
  exact BoundedContinuousFunction.coeFn_toLp ∞ actualSourceIntervalMeasure ℂ
    (continuousSourceIntervalBCF F)

private theorem continuousSourceIntervalLInf_norm_le (F : C(SpectralCircle, ℂ)) :
    ‖continuousSourceIntervalLInf F‖ ≤ ‖F‖ := by
  have hmeasure : measureUnivNNReal actualSourceIntervalMeasure = 1 := by
    simpa [actualSourceIntervalMeasure] using actualSourceIntervalMeasure_univNNReal
  have hmass : ((measureUnivNNReal actualSourceIntervalMeasure : ℝ) ^
      (∞ : ℝ≥0∞).toReal⁻¹) = 1 := by
    rw [hmeasure]
    simp
  calc
    ‖continuousSourceIntervalLInf F‖ ≤
        (measureUnivNNReal actualSourceIntervalMeasure : ℝ) ^
          (∞ : ℝ≥0∞).toReal⁻¹ * ‖continuousSourceIntervalBCF F‖ :=
      BoundedContinuousFunction.Lp_norm_le (μ := actualSourceIntervalMeasure)
        (p := ∞) (continuousSourceIntervalBCF F)
    _ = ‖continuousSourceIntervalBCF F‖ := by rw [hmass, one_mul]
    _ ≤ ‖F‖ := continuousSourceIntervalBCF_norm_le F

/-- The full imaginary free resolvent has a genuine source-interval L-infinity
representative obtained from its actual continuous Fourier representative. -/
def actualFullImaginaryResolventIntervalLInf
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SourcePairL2) (upper : Bool) :
    Lp ℂ ∞ (actualSourceIntervalMeasure) :=
  continuousSourceIntervalLInf
    (freeDomainContinuousComponent n
      (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x)) upper)

theorem actualFullImaginaryResolventIntervalLInf_ae
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SourcePairL2) (upper : Bool) :
    (actualFullImaginaryResolventIntervalLInf n y hy x upper : ℝ → ℂ) =ᵐ[
      actualSourceIntervalMeasure]
      fun t => freeDomainContinuousComponent n
        (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x)) upper
          ((t : ℝ) : SpectralCircle) := by
  exact continuousSourceIntervalLInf_ae _

theorem actualFullImaginaryResolventIntervalLInf_norm_le
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SourcePairL2) (upper : Bool) :
    ‖actualFullImaginaryResolventIntervalLInf n y hy x upper‖ ≤
      Real.sqrt (2 / y) * ‖x‖ := by
  calc
    ‖actualFullImaginaryResolventIntervalLInf n y hy x upper‖ ≤
        ‖freeDomainContinuousComponent n
          (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x)) upper‖ :=
      continuousSourceIntervalLInf_norm_le _
    _ ≤ Real.sqrt (2 / y) * ‖sourcePairRepr n x‖ :=
      sourceFullImaginaryResolventSquare_continuous_norm_le n y hy
        (sourcePairRepr n x) upper
    _ = Real.sqrt (2 / y) * ‖x‖ := by
      rw [(sourcePairRepr n).norm_map]

end NlsGge.Schur

end
