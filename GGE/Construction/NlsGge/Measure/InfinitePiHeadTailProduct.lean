import NlsGge.Measure.InfinitePiGroupedDefinitions
import NlsGge.Measure.InfinitePiGroupedPrerequisites
import NlsGge.Measure.InfinitePiGroupedFiniteIndex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProductMeasure

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NlsGge.Measure.BoolToHeadTailProductAfterEqPiV1

abbrev Block (A : Set ℤ) (b : Bool) :=
  (j : bif b then (Aᶜ : Set ℤ) else A) → ℂ

def boolToHeadTailEquiv (A : Set ℤ) :
    ((b : Bool) → Block A b) ≃ᵐ ((a : A) → ℂ) × ((i : (Aᶜ : Set ℤ)) → ℂ) :=
  (MeasurableEquiv.piCongrLeft (Block A) finTwoEquiv).symm.trans
    (MeasurableEquiv.piFinTwo (fun i : Fin 2 => Block A (finTwoEquiv i)))

def headGaussianLaw (c : ℕ → ℝ) (A : Set ℤ) : Measure ((a : A) → ℂ) :=
  Measure.infinitePi (fun a : A => complexGaussian (fullWeightRate c a))

def tailGaussianLaw (c : ℕ → ℝ) (A : Set ℤ) : Measure ((i : (Aᶜ : Set ℤ)) → ℂ) :=
  Measure.infinitePi (fun i : (Aᶜ : Set ℤ) => complexGaussian (fullWeightRate c i))

/-- The actual Bool-block Gaussian law maps to the product of its head and
set-complement block laws via finite-index reindexing and splitting. This is
only the block map-law identity, not an independence/full-support claim. -/
lemma groupedLaw_map_headTailEquiv_afterEqPi
    (c : ℕ → ℝ) (A : Set ℤ) [DecidablePred (· ∈ A)] :
    (BoolSigmaProbe2.actualSigmaGroupedLaw c A).map (boolToHeadTailEquiv A) =
      (headGaussianLaw c A).prod (tailGaussianLaw c A) := by
  let ν : (b : Bool) → Measure (Block A b) :=
    BoolSigmaEqPiPrerequisiteV1.actualBlockLaw c A
  have hCoordProb : ∀ p : BoolSigmaProbe2.BoolSumIndex A,
      IsProbabilityMeasure (BoolSigmaProbe2.actualSigmaGaussianFamily c A p) :=
    NlsGge.Measure.BoolSigmaLawPrerequisites3.actualSigmaGaussianFamily_isProbability_v3 c A
  letI : ∀ b : Bool, ∀ j : bif b then (Aᶜ : Set ℤ) else A,
      IsProbabilityMeasure (BoolSigmaProbe2.actualSigmaGaussianFamily c A ⟨b, j⟩) := by
    intro b j
    exact hCoordProb ⟨b, j⟩
  have hBlockProb : ∀ b : Bool, IsProbabilityMeasure (ν b) := by
    intro b
    dsimp [ν, BoolSigmaEqPiPrerequisiteV1.actualBlockLaw]
    infer_instance
  letI : ∀ b : Bool, IsProbabilityMeasure (ν b) := hBlockProb
  let e := finTwoEquiv
  let X : Bool → Type := Block A
  let pReindex := MeasurableEquiv.piCongrLeft X e
  let pSplit := MeasurableEquiv.piFinTwo (fun i : Fin 2 => X (e i))
  have hReindex :
      (Measure.pi ν).map pReindex.symm = Measure.pi (fun i : Fin 2 => ν (e i)) := by
    exact ((MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq pReindex).mp
      (Measure.pi_map_piCongrLeft e ν)).symm
  have hSplit :
      (Measure.pi (fun i : Fin 2 => ν (e i))).map pSplit =
        (ν (e 0)).prod (ν (e 1)) := by
    exact (measurePreserving_piFinTwo (fun i : Fin 2 => ν (e i))).map_eq
  have hGrouped :=
    BoolSigmaEqPiPrerequisiteV1.actualSigmaGroupedLaw_eq_pi_v1 c A
  rw [hGrouped]
  change (Measure.pi ν).map (pSplit ∘ pReindex.symm) = _
  rw [← Measure.map_map pSplit.measurable pReindex.symm.measurable]
  rw [hReindex]
  exact hSplit

end NlsGge.Measure.BoolToHeadTailProductAfterEqPiV1
