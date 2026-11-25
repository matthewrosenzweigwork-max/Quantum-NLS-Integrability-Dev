import NlsGge.Spectral.ActualFullImaginaryResolventLInfCLMV3
import NlsGge.Spectral.ActualRoughL2PotentialTimesFullImaginaryResolventV2
import NlsGge.Spectral.SourceFreeDomainContinuousComponentSourceAEV3
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.Normed.Lp.PiLp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot

local instance : IsProbabilityMeasure spectralHaar := by
  unfold spectralHaar
  infer_instance

private abbrev actualWeightedDomainPotentialMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc (0 : ℝ) 1)

private theorem actualWeightedDomainComponent_add
    (n : ℤ) (x z : freeWeightedDomainPointwise n) (upper : Bool) :
    freeDomainContinuousComponent n (x + z).val upper =
      freeDomainContinuousComponent n x.val upper +
        freeDomainContinuousComponent n z.val upper := by
  have hx := freeDomainContinuousComponent_hasSum n x.val x.property upper
  have hz := freeDomainContinuousComponent_hasSum n z.val z.property upper
  let χ : Sector n → C(SpectralCircle, ℂ) := fun m =>
    fourier (T := (2 : ℝ)) (if upper then m.val else -m.val)
  have hsum : HasSum (fun m : Sector n =>
      (x.val (upper, m) + z.val (upper, m)) • χ m)
      (freeDomainContinuousComponent n x.val upper +
        freeDomainContinuousComponent n z.val upper) := by
    refine (hx.add hz).congr_fun ?_
    intro m
    change (x.val (upper, m) + z.val (upper, m)) • χ m =
      x.val (upper, m) • χ m + z.val (upper, m) • χ m
    rw [add_smul]
  exact (freeDomainContinuousComponent_hasSum n (x + z).val
    (x + z).property upper).unique hsum

private theorem actualWeightedDomainComponent_smul
    (n : ℤ) (a : ℂ) (x : freeWeightedDomainPointwise n) (upper : Bool) :
    freeDomainContinuousComponent n (a • x).val upper =
      a • freeDomainContinuousComponent n x.val upper := by
  have hx := freeDomainContinuousComponent_hasSum n x.val x.property upper
  let χ : Sector n → C(SpectralCircle, ℂ) := fun m =>
    fourier (T := (2 : ℝ)) (if upper then m.val else -m.val)
  have hsum : HasSum (fun m : Sector n => (a • x.val) (upper, m) • χ m)
      (a • freeDomainContinuousComponent n x.val upper) := by
    refine (hx.const_smul a).congr_fun ?_
    intro m
    change (a • x.val (upper, m)) • χ m = a • (x.val (upper, m) • χ m)
    simp [smul_smul]
  exact (freeDomainContinuousComponent_hasSum n (a • x).val
    (a • x).property upper).unique hsum

private def actualWeightedDomainComponentContinuousMap
    (n : ℤ) (upper : Bool) :
    freeWeightedDomainPointwise n →ₗ[ℂ] C(SpectralCircle, ℂ) where
  toFun x := freeDomainContinuousComponent n x.val upper
  map_add' x z := by
    exact actualWeightedDomainComponent_add n _ _ upper
  map_smul' a x := by
    exact actualWeightedDomainComponent_smul n a _ upper

private def actualWeightedDomainContinuousIntervalBCF
    (F : C(SpectralCircle, ℂ)) : BoundedContinuousFunction ℝ ℂ where
  toFun t := F ((t : ℝ) : SpectralCircle)
  continuous_toFun := F.continuous.comp (AddCircle.continuous_mk' (2 : ℝ))
  map_bounded' := by
    refine ⟨2 * ‖F‖, ?_⟩
    intro x z
    rw [dist_eq_norm]
    calc
      ‖F ((x : ℝ) : SpectralCircle) - F ((z : ℝ) : SpectralCircle)‖ ≤
          ‖F ((x : ℝ) : SpectralCircle)‖ + ‖F ((z : ℝ) : SpectralCircle)‖ :=
            norm_sub_le _ _
      _ ≤ ‖F‖ + ‖F‖ := add_le_add (F.norm_coe_le_norm _) (F.norm_coe_le_norm _)
      _ = 2 * ‖F‖ := by ring

private def actualWeightedDomainContinuousIntervalBCFLinearMap :
    C(SpectralCircle, ℂ) →ₗ[ℂ] BoundedContinuousFunction ℝ ℂ where
  toFun := actualWeightedDomainContinuousIntervalBCF
  map_add' F G := by
    ext t
    rfl
  map_smul' a F := by
    ext t
    rfl

private def actualWeightedDomainContinuousIntervalLInfLinearMap :
    C(SpectralCircle, ℂ) →ₗ[ℂ] Lp ℂ ∞ actualWeightedDomainPotentialMeasure :=
  (BoundedContinuousFunction.toLp ∞ actualWeightedDomainPotentialMeasure ℂ).toLinearMap.comp
    actualWeightedDomainContinuousIntervalBCFLinearMap

private def actualWeightedDomainComponentLInfLinearMap
    (n : ℤ) (upper : Bool) :
    freeWeightedDomainPointwise n →ₗ[ℂ] Lp ℂ ∞ actualWeightedDomainPotentialMeasure :=
  actualWeightedDomainContinuousIntervalLInfLinearMap.comp
    (actualWeightedDomainComponentContinuousMap n upper)

/-- Each actual weighted-domain vector has the source-interval L-infinity
representative furnished by its continuous Fourier reconstruction. This is a
linear map on the weighted-domain subtype, not a bounded map from ambient L2. -/
def actualSourceWeightedDomainLInfRepresentativeMap (n : ℤ) :
    freeWeightedDomainPointwise n →ₗ[ℂ] ActualSourceIntervalLInfPair where
  toFun x := WithLp.toLp 2 (fun b => actualWeightedDomainComponentLInfLinearMap n b x)
  map_add' x z := by
    apply PiLp.ext
    intro b
    exact (actualWeightedDomainComponentLInfLinearMap n b).map_add x z
  map_smul' a x := by
    apply PiLp.ext
    intro b
    exact (actualWeightedDomainComponentLInfLinearMap n b).map_smul a x

/-- The actual physical L2 potential acts on the weighted domain through its
source-interval L-infinity representatives. -/
def actualSourcePotentialOnWeightedDomain (n : ℤ) (u₁ u₂ : PhysicalL2) :
    freeWeightedDomainPointwise n →ₗ[ℂ] SourcePairL2 :=
  (actualL2PotentialParityPairSourceOperator u₁ u₂).toLinearMap.comp
    (actualSourceWeightedDomainLInfRepresentativeMap n)

theorem actualSourceWeightedDomainLInfRepresentativeMap_ae
    (n : ℤ) (x : freeWeightedDomainPointwise n) (upper : Bool) :
    (actualSourceWeightedDomainLInfRepresentativeMap n x upper : ℝ → ℂ) =ᵐ[
      actualWeightedDomainPotentialMeasure]
      fun t => freeDomainContinuousComponent n x.val upper
        ((t : ℝ) : SpectralCircle) := by
  exact BoundedContinuousFunction.coeFn_toLp ∞ actualWeightedDomainPotentialMeasure ℂ
    (actualWeightedDomainContinuousIntervalBCF
      (freeDomainContinuousComponent n x.val upper))

/-- The same continuous representative, viewed in actual source L2, is the
component of the original source-domain vector. -/
theorem actualSourceWeightedDomainLInfRepresentativeMap_toL2
    (n : ℤ) (x : freeWeightedDomainPointwise n) (upper : Bool) :
    BoundedContinuousFunction.toLp 2 actualWeightedDomainPotentialMeasure ℂ
      (actualWeightedDomainContinuousIntervalBCF
        (freeDomainContinuousComponent n x.val upper)) =
      sourceCoordinateComponent n x.val upper := by
  let F := freeDomainContinuousComponent n x.val upper
  let B := actualWeightedDomainContinuousIntervalBCF F
  have hEval := spectral_ae_pullback_first_half
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spectralHaar F)
  have hSource := freeDomainContinuousComponent_toSourceInterval_ae
    n x.val x.property upper
  apply Lp.ext
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2
      actualWeightedDomainPotentialMeasure ℂ B, hEval, hSource]
      with t hB hEval hSource
  change ((BoundedContinuousFunction.toLp 2 actualWeightedDomainPotentialMeasure ℂ B :
      Lp ℂ 2 actualWeightedDomainPotentialMeasure) : ℝ → ℂ) t = B t at hB
  change ((ContinuousMap.toLp 2 spectralHaar ℂ F :
      Lp ℂ 2 spectralHaar) : SpectralCircle → ℂ) ((t : ℝ) : SpectralCircle) =
        F ((t : ℝ) : SpectralCircle) at hEval
  change ((ContinuousMap.toLp 2 spectralHaar ℂ F :
      Lp ℂ 2 spectralHaar) : SpectralCircle → ℂ) ((t : ℝ) : SpectralCircle) =
        (sourceCoordinateComponent n x.val upper : ℝ → ℂ) t at hSource
  calc
    ((BoundedContinuousFunction.toLp 2 actualWeightedDomainPotentialMeasure ℂ B :
      Lp ℂ 2 actualWeightedDomainPotentialMeasure) : ℝ → ℂ) t = B t := hB
    _ = F ((t : ℝ) : SpectralCircle) := rfl
    _ = ((ContinuousMap.toLp 2 spectralHaar ℂ F :
      Lp ℂ 2 spectralHaar) : SpectralCircle → ℂ) ((t : ℝ) : SpectralCircle) := hEval.symm
    _ = sourceCoordinateComponent n x.val upper t := hSource

theorem actualSourcePotentialOnWeightedDomain_upper_ae
    (n : ℤ) (u₁ u₂ : PhysicalL2) (x : freeWeightedDomainPointwise n) :
    (actualSourcePotentialOnWeightedDomain n u₁ u₂ x true : ℝ → ℂ) =ᵐ[
      actualWeightedDomainPotentialMeasure]
      fun t => u₁ ((t : ℝ) : PhysicalCircle) *
        freeDomainContinuousComponent n x.val false ((t : ℝ) : SpectralCircle) := by
  change (actualL2PotentialParityPairSourceOperator u₁ u₂
      (actualSourceWeightedDomainLInfRepresentativeMap n x) true : ℝ → ℂ) =ᵐ[
        actualWeightedDomainPotentialMeasure] _
  rw [actualL2PotentialParityPairSourceOperator_apply_true]
  have hmul := actualSourceL2PotentialTimesLInf_ae u₁
    (actualSourceWeightedDomainLInfRepresentativeMap n x false)
  have hu := actualPhysicalL2SourcePotential_ae u₁
  have hr := actualSourceWeightedDomainLInfRepresentativeMap_ae n x false
  filter_upwards [hmul, hu, hr] with t hmul hu hr
  calc
    actualSourceL2PotentialTimesLInf u₁
        (actualSourceWeightedDomainLInfRepresentativeMap n x false) t =
        actualPhysicalL2SourcePotential u₁ t *
          actualSourceWeightedDomainLInfRepresentativeMap n x false t := hmul
    _ = u₁ ((t : ℝ) : PhysicalCircle) *
        freeDomainContinuousComponent n x.val false
          ((t : ℝ) : SpectralCircle) := by rw [hu, hr]

theorem actualSourcePotentialOnWeightedDomain_lower_ae
    (n : ℤ) (u₁ u₂ : PhysicalL2) (x : freeWeightedDomainPointwise n) :
    (actualSourcePotentialOnWeightedDomain n u₁ u₂ x false : ℝ → ℂ) =ᵐ[
      actualWeightedDomainPotentialMeasure]
      fun t => u₂ ((t : ℝ) : PhysicalCircle) *
        freeDomainContinuousComponent n x.val true ((t : ℝ) : SpectralCircle) := by
  change (actualL2PotentialParityPairSourceOperator u₁ u₂
      (actualSourceWeightedDomainLInfRepresentativeMap n x) false : ℝ → ℂ) =ᵐ[
        actualWeightedDomainPotentialMeasure] _
  rw [actualL2PotentialParityPairSourceOperator_apply_false]
  have hmul := actualSourceL2PotentialTimesLInf_ae u₂
    (actualSourceWeightedDomainLInfRepresentativeMap n x true)
  have hu := actualPhysicalL2SourcePotential_ae u₂
  have hr := actualSourceWeightedDomainLInfRepresentativeMap_ae n x true
  filter_upwards [hmul, hu, hr] with t hmul hu hr
  calc
    actualSourceL2PotentialTimesLInf u₂
        (actualSourceWeightedDomainLInfRepresentativeMap n x true) t =
        actualPhysicalL2SourcePotential u₂ t *
          actualSourceWeightedDomainLInfRepresentativeMap n x true t := hmul
    _ = u₂ ((t : ℝ) : PhysicalCircle) *
        freeDomainContinuousComponent n x.val true
          ((t : ℝ) : SpectralCircle) := by rw [hu, hr]

private def actualSourceFullImaginaryResolventDomainLinearMap
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) :
    SourcePairL2 →ₗ[ℂ] freeWeightedDomainPointwise n where
  toFun x := ⟨sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x),
    sourceFullImaginaryResolventSquare_mem_freeWeightedDomain n y hy
      (sourcePairRepr n x)⟩
  map_add' x z := by
    apply Subtype.ext
    change sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n (x + z)) = _
    rw [(sourcePairRepr n).map_add, map_add]
    rfl
  map_smul' a x := by
    apply Subtype.ext
    change sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n (a • x)) = _
    rw [(sourcePairRepr n).map_smul, map_smul]
    rfl

theorem actualSourceWeightedDomainLInfRepresentativeMap_fullResolvent
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SourcePairL2) :
    actualSourceWeightedDomainLInfRepresentativeMap n
      (actualSourceFullImaginaryResolventDomainLinearMap n y hy x) =
        actualFullImaginaryResolventIntervalLInfCLM n y hy x := by
  apply PiLp.ext
  intro upper
  let F := freeDomainContinuousComponent n
    (sourceFullImaginaryResolventSquare n y hy (sourcePairRepr n x)) upper
  let B := actualWeightedDomainContinuousIntervalBCF F
  rw [actualFullImaginaryResolventIntervalLInfCLM_apply]
  change BoundedContinuousFunction.toLp ∞ actualWeightedDomainPotentialMeasure ℂ B =
    actualFullImaginaryResolventIntervalLInf n y hy x upper
  apply Lp.ext
  filter_upwards [BoundedContinuousFunction.coeFn_toLp ∞
      actualWeightedDomainPotentialMeasure ℂ B,
    actualFullImaginaryResolventIntervalLInf_ae n y hy x upper] with t hB hR
  change ((BoundedContinuousFunction.toLp ∞ actualWeightedDomainPotentialMeasure ℂ B :
      Lp ℂ ∞ actualWeightedDomainPotentialMeasure) : ℝ → ℂ) t = B t at hB
  change (actualFullImaginaryResolventIntervalLInf n y hy x upper : ℝ → ℂ) t = _ at hR
  calc
    ((BoundedContinuousFunction.toLp ∞ actualWeightedDomainPotentialMeasure ℂ B :
      Lp ℂ ∞ actualWeightedDomainPotentialMeasure) : ℝ → ℂ) t = B t := hB
    _ = F ((t : ℝ) : SpectralCircle) := rfl
    _ = actualFullImaginaryResolventIntervalLInf n y hy x upper t := hR.symm

theorem actualSourcePotentialOnWeightedDomain_fullResolvent
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2) (x : SourcePairL2) :
    actualSourcePotentialOnWeightedDomain n u₁ u₂
        (actualSourceFullImaginaryResolventDomainLinearMap n y hy x) =
      actualRoughL2PotentialFullImaginaryResolventCLM n y hy u₁ u₂ x := by
  change actualL2PotentialParityPairSourceOperator u₁ u₂
      (actualSourceWeightedDomainLInfRepresentativeMap n
        (actualSourceFullImaginaryResolventDomainLinearMap n y hy x)) = _
  rw [actualSourceWeightedDomainLInfRepresentativeMap_fullResolvent]
  rfl

end NlsGge.Schur

end
