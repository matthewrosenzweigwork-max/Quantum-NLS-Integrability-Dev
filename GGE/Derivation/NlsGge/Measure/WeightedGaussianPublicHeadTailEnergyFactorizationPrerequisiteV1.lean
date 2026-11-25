import NlsGge.Measure.CountableGaussian
import NlsGge.Measure.WeightedProjectionMaskedTailDefinitions
import NlsGge.Measure.RawHeadTailIndepFunPublicRestrictionsV1
import NlsGge.Measure.WeightedGaussianMaskedEnergyTailCompositionV2
import NlsGge.Measure.WeightedGaussianHeadRestrictionIdentityV2
import Mathlib.Probability.Independence.Basic

set_option autoImplicit false
set_option pp.maxSteps 10000000
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Measure.WeightedGaussianPublicHeadTailEnergyFactorizationPrerequisiteV1

def headRestriction (S : Finset ℤ) (z : ℤ → ℂ) : (i : S) → ℂ :=
  fun i => z i.1

def tailRestriction (S : Finset ℤ) (z : ℤ → ℂ) : ↥((S : Set ℤ)ᶜ) → ℂ :=
  fun i => z i.1

def tailExtension (S : Finset ℤ) (u : ↥((S : Set ℤ)ᶜ) → ℂ) : ℤ → ℂ :=
  fun n => if hn : n ∈ S then 0 else u ⟨n, by simpa using hn⟩

def maskedTailEnergy
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (S : Finset ℤ) (u : ↥((S : Set ℤ)ᶜ) → ℂ) : ℝ≥0∞ :=
  NlsGge.Measure.sequenceEnergy
    (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S)
    (tailExtension S u)

/-- The actual raw product law factors an arbitrary measurable finite-head box
and masked-energy threshold through the public finite-coordinate restriction. -/
lemma measure_inter_preimage_head_tailEnergy_public
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (S : Finset ℤ)
    (H : Set ((i : S) → ℂ)) (T : Set ℝ≥0∞)
    (hH : MeasurableSet H) (hT : MeasurableSet T) :
    (NlsGge.Measure.fullWeightSequenceGaussian c.val)
      (headRestriction S ⁻¹' H ∩
        (fun z : ℤ → ℂ => NlsGge.Measure.sequenceEnergy
          (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S) z) ⁻¹' T) =
    (NlsGge.Measure.fullWeightSequenceGaussian c.val) (headRestriction S ⁻¹' H) *
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)
        ((fun z : ℤ → ℂ => NlsGge.Measure.sequenceEnergy
          (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S) z) ⁻¹' T) := by
  let μ := NlsGge.Measure.fullWeightSequenceGaussian c.val
  let rawEnergy : (ℤ → ℂ) → ℝ≥0∞ := fun z => NlsGge.Measure.sequenceEnergy
    (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S) z
  have hind := NlsGge.Measure.RawHeadTailIndepFunPublicRestrictionsV1.fullWeightSequenceGaussian_indepFun_coordinateRestrictions_v1
    c.val (S : Set ℤ)
  have hext : Measurable (tailExtension S) := by
    apply measurable_pi_iff.mpr
    intro n
    by_cases hn : n ∈ S
    · simp [tailExtension, hn]
    · simpa [tailExtension, hn] using
        (measurable_pi_apply (⟨n, by simpa using hn⟩ : ↥((S : Set ℤ)ᶜ)))
  have henergy : Measurable (maskedTailEnergy c s S) :=
    (NlsGge.Measure.measurable_sequenceEnergy
      (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S)).comp hext
  have hEq : (fun z : ℤ → ℂ => maskedTailEnergy c s S (tailRestriction S z)) = rawEnergy := by
    have hbase := NlsGge.Measure.WeightedGaussianMaskedEnergyTailCompositionV2.maskedTailEnergy_comp_restriction
      c s S
    change (fun z : ℤ → ℂ => maskedTailEnergy c s S (tailRestriction S z)) = _ at hbase
    exact hbase
  have hcomp := hind.comp measurable_id henergy
  have hcomp' : ProbabilityTheory.IndepFun (headRestriction S)
      ((maskedTailEnergy c s S) ∘ tailRestriction S) μ := by
    change ProbabilityTheory.IndepFun
      (fun z : ℤ → ℂ => fun i : S => z i.1)
      ((maskedTailEnergy c s S) ∘
        (fun z : ℤ → ℂ => fun i : ↥((S : Set ℤ)ᶜ) => z i.1)) μ
    exact hcomp
  have hIndep : ProbabilityTheory.IndepFun (headRestriction S) rawEnergy μ := by
    rw [← hEq]
    exact hcomp' 
  have hf : Measurable (headRestriction S) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply i.1
  have hg : Measurable rawEnergy :=
    NlsGge.Measure.measurable_sequenceEnergy
      (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S)
  have hSets :=
    (ProbabilityTheory.indepFun_iff_indepSet_preimage
      (f := headRestriction S) (g := rawEnergy) (μ := μ) hf hg).mp hIndep H T hH hT
  exact hSets.measure_inter_eq_mul

#check @measure_inter_preimage_head_tailEnergy_public

end NlsGge.Measure.WeightedGaussianPublicHeadTailEnergyFactorizationPrerequisiteV1
