import NlsGge.Measure.InfinitePiFiniteHeadRawHeadTailProductAfterEqPiV3
import NlsGge.Measure.InfinitePiHeadTailProduct
import NlsGge.Measure.BoolHeadTailEquivCoordinatePrerequisiteV1
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
set_option pp.maxSteps 10000000
noncomputable section
open MeasureTheory

namespace NlsGge.Measure.RawHeadTailIndepFunActualProofV6

private def headRestrict (A : Set ℤ) : (ℤ → ℂ) → ((a : A) → ℂ) := A.domRestrict

private def tailRestrict (A : Set ℤ) : (ℤ → ℂ) → ((i : (Aᶜ : Set ℤ)) → ℂ) :=
  (Aᶜ : Set ℤ).domRestrict

private lemma rawHead_coordinate (A : Set ℤ) [DecidablePred (· ∈ A)]
    (z : ℤ → ℂ) :
    (RawHeadTailProductAfterEqPiV3.rawToHeadTailEquiv A z).1 = headRestrict A z := by
  funext a
  change
    (BoolToHeadTailProductAfterEqPiV1.boolToHeadTailEquiv A
      (BoolSigmaProbe2.actualSigmaGroupedEquiv A
        ((MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℂ)
          (Equiv.Set.sumCompl A)).symm z))).1 a = z a
  rw [BoolHeadTailEquivCoordinatePrerequisiteV1.boolToHeadTailEquiv_fst_apply]
  change
    ((MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℂ)
      (Equiv.Set.sumCompl A)).symm z) (Sum.inl a) = z a
  rfl

private lemma rawTail_coordinate (A : Set ℤ) [DecidablePred (· ∈ A)]
    (z : ℤ → ℂ) :
    (RawHeadTailProductAfterEqPiV3.rawToHeadTailEquiv A z).2 = tailRestrict A z := by
  funext i
  change
    (BoolToHeadTailProductAfterEqPiV1.boolToHeadTailEquiv A
      (BoolSigmaProbe2.actualSigmaGroupedEquiv A
        ((MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℂ)
          (Equiv.Set.sumCompl A)).symm z))).2 i = z i
  rw [BoolHeadTailEquivCoordinatePrerequisiteV1.boolToHeadTailEquiv_snd_apply]
  change
    ((MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℂ)
      (Equiv.Set.sumCompl A)).symm z) (Sum.inr i) = z i
  rfl

/-- The actual raw countable Gaussian law makes restriction to any set and its
complement independent. The joint pushforward identity is the previously
compiled/audited product-law result; the coordinate maps below are identified
with the actual restrictions, and independence is obtained from the pinned
map-product characterization. -/
lemma fullWeightSequenceGaussian_indepFun_restrict_complement_v6
    (c : ℕ → ℝ) (A : Set ℤ) [DecidablePred (· ∈ A)] :
    ProbabilityTheory.IndepFun (headRestrict A) (tailRestrict A)
      (fullWeightSequenceGaussian c) := by
  let μ := fullWeightSequenceGaussian c
  let e := RawHeadTailProductAfterEqPiV3.rawToHeadTailEquiv A
  let μHead := BoolToHeadTailProductAfterEqPiV1.headGaussianLaw c A
  let μTail := BoolToHeadTailProductAfterEqPiV1.tailGaussianLaw c A
  letI : IsProbabilityMeasure μHead := by
    dsimp [μHead, BoolToHeadTailProductAfterEqPiV1.headGaussianLaw]
    infer_instance
  letI : IsProbabilityMeasure μTail := by
    dsimp [μTail, BoolToHeadTailProductAfterEqPiV1.tailGaussianLaw]
    infer_instance
  have hJoint :
      μ.map (fun z => (headRestrict A z, tailRestrict A z)) = μHead.prod μTail := by
    have hPair :
        (fun z => (headRestrict A z, tailRestrict A z)) = e := by
      funext z
      exact Prod.ext (rawHead_coordinate A z).symm (rawTail_coordinate A z).symm
    rw [hPair]
    change (fullWeightSequenceGaussian c).map e = μHead.prod μTail
    exact RawHeadTailProductAfterEqPiV3.fullWeightSequenceGaussian_map_rawToHeadTailEquiv_afterEqPi_v3
      c A
  have hJointEquiv : μ.map e = μHead.prod μTail := by
    change (fullWeightSequenceGaussian c).map e = μHead.prod μTail
    exact RawHeadTailProductAfterEqPiV3.fullWeightSequenceGaussian_map_rawToHeadTailEquiv_afterEqPi_v3
      c A
  have hHead : μ.map (headRestrict A) = μHead := by
    have hCoord : headRestrict A = Prod.fst ∘ e := by
      funext z
      exact (rawHead_coordinate A z).symm
    rw [hCoord, ← Measure.map_map measurable_fst e.measurable, hJointEquiv]
    exact (measurePreserving_fst (μ := μHead) (ν := μTail)).map_eq
  have hTail : μ.map (tailRestrict A) = μTail := by
    have hCoord : tailRestrict A = Prod.snd ∘ e := by
      funext z
      exact (rawTail_coordinate A z).symm
    rw [hCoord, ← Measure.map_map measurable_snd e.measurable, hJointEquiv]
    exact (measurePreserving_snd (μ := μHead) (ν := μTail)).map_eq
  have hf : Measurable (headRestrict A) := by
    simpa [headRestrict] using (Set.measurable_restrict A)
  have hg : Measurable (tailRestrict A) := by
    simpa [tailRestrict] using (Set.measurable_restrict (Aᶜ : Set ℤ))
  apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (f := headRestrict A) (g := tailRestrict A) (μ := μ)
    hf.aemeasurable hg.aemeasurable).2
  rw [hJoint, hHead, hTail]

#check @fullWeightSequenceGaussian_indepFun_restrict_complement_v6

end NlsGge.Measure.RawHeadTailIndepFunActualProofV6
