import NlsGge.Spectral.ActualRoughL2PotentialTimesFullImaginaryResolventV2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot

private abbrev actualResolventSourceMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc (0 : ℝ) 1)

private theorem freeDomainContinuousComponent_add
    (n : ℤ) (x y : freeWeightedDomainPointwise n) (upper : Bool) :
    freeDomainContinuousComponent n (x + y).val upper =
      freeDomainContinuousComponent n x.val upper +
        freeDomainContinuousComponent n y.val upper := by
  have hx := freeDomainContinuousComponent_hasSum n x.val x.property upper
  have hy := freeDomainContinuousComponent_hasSum n y.val y.property upper
  let χ : Sector n → C(SpectralCircle, ℂ) := fun m =>
    fourier (T := (2 : ℝ)) (if upper then m.val else -m.val)
  have hsum : HasSum (fun m : Sector n =>
      (x.val (upper, m) + y.val (upper, m)) • χ m)
      (freeDomainContinuousComponent n x.val upper +
        freeDomainContinuousComponent n y.val upper) := by
    refine (hx.add hy).congr_fun ?_
    intro m
    change (x.val (upper, m) + y.val (upper, m)) • χ m =
      x.val (upper, m) • χ m + y.val (upper, m) • χ m
    rw [add_smul]
  have hxy := freeDomainContinuousComponent_hasSum n (x + y).val (x + y).property upper
  exact hxy.unique hsum

private theorem freeDomainContinuousComponent_smul
    (n : ℤ) (a : ℂ) (x : freeWeightedDomainPointwise n) (upper : Bool) :
    freeDomainContinuousComponent n (a • x).val upper =
      a • freeDomainContinuousComponent n x.val upper := by
  have hx := freeDomainContinuousComponent_hasSum n x.val x.property upper
  let χ : Sector n → C(SpectralCircle, ℂ) := fun m =>
    fourier (T := (2 : ℝ)) (if upper then m.val else -m.val)
  have hsum : HasSum (fun m : Sector n =>
      (a • x.val) (upper, m) • χ m)
      (a • freeDomainContinuousComponent n x.val upper) := by
    refine (hx.const_smul a).congr_fun ?_
    intro m
    change (a • x.val (upper, m)) • χ m =
      a • (x.val (upper, m) • χ m)
    simp [smul_smul]
  have hax := freeDomainContinuousComponent_hasSum n (a • x).val (a • x).property upper
  exact hax.unique hsum

private def actualResolventDomainValue
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SourcePairL2) :
    freeWeightedDomainPointwise n :=
  ⟨sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x),
    sourceFullImaginaryResolventSquare_mem_freeWeightedDomain n y hy
      (sourcePairRepr n x)⟩

private theorem actualResolventDomainValue_add
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x z : SourcePairL2) :
    actualResolventDomainValue n y hy (x + z) =
      actualResolventDomainValue n y hy x + actualResolventDomainValue n y hy z := by
  apply Subtype.ext
  change sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n (x + z)) =
    sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x) +
      sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n z)
  rw [(sourcePairRepr n).map_add, map_add]

private theorem actualResolventDomainValue_smul
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (a : ℂ) (x : SourcePairL2) :
    actualResolventDomainValue n y hy (a • x) =
      a • actualResolventDomainValue n y hy x := by
  apply Subtype.ext
  change sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n (a • x)) =
    a • sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x)
  rw [(sourcePairRepr n).map_smul, map_smul]

private def actualResolventContinuousComponentLinearMap
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (upper : Bool) :
    SourcePairL2 →ₗ[ℂ] C(SpectralCircle, ℂ) where
  toFun x := freeDomainContinuousComponent n
    (actualResolventDomainValue n y hy x).val upper
  map_add' x z := by
    rw [actualResolventDomainValue_add]
    exact freeDomainContinuousComponent_add n _ _ upper
  map_smul' a x := by
    rw [actualResolventDomainValue_smul]
    exact freeDomainContinuousComponent_smul n a _ upper

private def actualResolventContinuousIntervalBCF
    (F : C(SpectralCircle, ℂ)) : BoundedContinuousFunction ℝ ℂ where
  toFun t := F ((t : ℝ) : SpectralCircle)
  continuous_toFun := F.continuous.comp (AddCircle.continuous_mk' (2 : ℝ))
  map_bounded' := by
    refine ⟨2 * ‖F‖, ?_⟩
    intro x z
    rw [dist_eq_norm]
    calc
      ‖F ((x : ℝ) : SpectralCircle) - F ((z : ℝ) : SpectralCircle)‖ ≤
          ‖F ((x : ℝ) : SpectralCircle)‖ + ‖F ((z : ℝ) : SpectralCircle)‖ := norm_sub_le _ _
      _ ≤ ‖F‖ + ‖F‖ := add_le_add (F.norm_coe_le_norm _) (F.norm_coe_le_norm _)
      _ = 2 * ‖F‖ := by ring

private def actualResolventContinuousIntervalBCFLinearMap :
    C(SpectralCircle, ℂ) →ₗ[ℂ] BoundedContinuousFunction ℝ ℂ where
  toFun := actualResolventContinuousIntervalBCF
  map_add' F G := by
    ext t
    rfl
  map_smul' a F := by
    ext t
    rfl

private theorem actualResolventContinuousIntervalBCF_norm_le
    (F : C(SpectralCircle, ℂ)) :
    ‖actualResolventContinuousIntervalBCF F‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le_of_nonempty
    (f := actualResolventContinuousIntervalBCF F) (M := ‖F‖)).2
  intro t
  exact F.norm_coe_le_norm ((t : ℝ) : SpectralCircle)

private def actualResolventContinuousIntervalBCFCLM :
    C(SpectralCircle, ℂ) →L[ℂ] BoundedContinuousFunction ℝ ℂ :=
  LinearMap.mkContinuous actualResolventContinuousIntervalBCFLinearMap 1 (by
    intro F
    change ‖actualResolventContinuousIntervalBCF F‖ ≤ 1 * ‖F‖
    rw [one_mul]
    exact actualResolventContinuousIntervalBCF_norm_le F)

private def actualResolventContinuousIntervalLInfCLM :
    C(SpectralCircle, ℂ) →L[ℂ] Lp ℂ ∞ actualResolventSourceMeasure :=
  (BoundedContinuousFunction.toLp ∞ actualResolventSourceMeasure ℂ).comp
    actualResolventContinuousIntervalBCFCLM

private def actualResolventComponentLInfCLM
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (upper : Bool) :
    SourcePairL2 →L[ℂ] Lp ℂ ∞ actualResolventSourceMeasure :=
  (actualResolventContinuousIntervalLInfCLM).comp
    ((actualResolventContinuousComponentLinearMap n y hy upper).mkContinuous
      (Real.sqrt (2 / y)) (by
        intro x
        change ‖freeDomainContinuousComponent n
          (actualResolventDomainValue n y hy x).val upper‖ ≤
            Real.sqrt (2 / y) * ‖x‖
        calc
          _ ≤ Real.sqrt (2 / y) * ‖sourcePairRepr n x‖ :=
            sourceFullImaginaryResolventSquare_continuous_norm_le n y hy
              (sourcePairRepr n x) upper
          _ = Real.sqrt (2 / y) * ‖x‖ := by
            rw [(sourcePairRepr n).norm_map]))

/-- A genuine linear map from the source Hilbert pair to its two actual interval
L-infinity resolvent classes. Its values are the V4 continuous representatives
from the corrected V2 channel ordering. -/
def actualFullImaginaryResolventIntervalLInfCLM
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) :
    SourcePairL2 →L[ℂ] ActualSourceIntervalLInfPair := by
  let e := PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : Bool => Lp ℂ ∞ actualResolventSourceMeasure)
  let f : (Bool → SourcePairL2 →L[ℂ] Lp ℂ ∞ actualResolventSourceMeasure) :=
    fun b => actualResolventComponentLInfCLM n y hy b
  let g : SourcePairL2 →L[ℂ]
      (Bool → Lp ℂ ∞ actualResolventSourceMeasure) :=
    ContinuousLinearMap.pi f
  exact e.symm.toContinuousLinearMap.comp g

@[simp] theorem actualFullImaginaryResolventIntervalLInfCLM_apply
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SourcePairL2) (b : Bool) :
    actualFullImaginaryResolventIntervalLInfCLM n y hy x b =
      actualFullImaginaryResolventIntervalLInf n y hy x b := by
  rfl

/-- The actual rough potential composed with the bounded full imaginary
resolvent is a source-Hilbert-space CLM. This is the positive-imaginary-axis
`V R₀` map; it does not by itself assert Neumann invertibility. -/
def actualRoughL2PotentialFullImaginaryResolventCLM
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2) :
    SourcePairL2 →L[ℂ] SourcePairL2 :=
  (actualL2PotentialParityPairSourceOperator u₁ u₂).comp
    (actualFullImaginaryResolventIntervalLInfCLM n y hy)

theorem actualRoughL2PotentialFullImaginaryResolventCLM_norm_le
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2) :
    ‖actualRoughL2PotentialFullImaginaryResolventCLM n y hy u₁ u₂‖ ≤
      Real.sqrt (2 / y) * (‖u₁‖ + ‖u₂‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖actualL2PotentialParityPairSourceOperator u₁ u₂
      (actualFullImaginaryResolventIntervalLInfPair n y hy x)‖ ≤ _
  exact actualRoughL2PotentialTimesFullImaginaryResolvent_norm_le n y hy u₁ u₂ x

end NlsGge.Schur

end
