import NlsGge.Measure.InfinitePiReindex
import NlsGge.Measure.InfinitePiGroupedLaw
import NlsGge.Measure.InfinitePiHeadTailProduct
import Mathlib.Probability.ProductMeasure

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NlsGge.Measure.RawHeadTailProductAfterEqPiV3

/-- The actual raw sequence is sent to its head and set-complement coordinates
by the pinned partition reindexing and the accepted Bool-block equivalences. -/
def rawToHeadTailEquiv (A : Set ℤ) [DecidablePred (· ∈ A)] :
    (ℤ → ℂ) ≃ᵐ ((a : A) → ℂ) × ((i : (Aᶜ : Set ℤ)) → ℂ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℂ) (Equiv.Set.sumCompl A)).symm.trans
    ((BoolSigmaProbe2.actualSigmaGroupedEquiv A).trans
      (BoolToHeadTailProductAfterEqPiV1.boolToHeadTailEquiv A))

/-- The joint pushforward of the actual raw countable Gaussian law is the
product of the actual head and complement laws. This is only a joint map-law
identity; it does not itself claim independence or full support. -/
lemma fullWeightSequenceGaussian_map_rawToHeadTailEquiv_afterEqPi_v3
    (c : ℕ → ℝ) (A : Set ℤ) [DecidablePred (· ∈ A)] :
    (fullWeightSequenceGaussian c).map (rawToHeadTailEquiv A) =
      (BoolToHeadTailProductAfterEqPiV1.headGaussianLaw c A).prod
        (BoolToHeadTailProductAfterEqPiV1.tailGaussianLaw c A) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℂ) (Equiv.Set.sumCompl A)
  let G := BoolSigmaProbe2.actualSigmaGroupedEquiv A
  let H := BoolToHeadTailProductAfterEqPiV1.boolToHeadTailEquiv A
  have hReindex := fullWeightSequenceGaussian_reindex_sumCompl_v2 c A
  have hRawReindex :
      (fullWeightSequenceGaussian c).map e.symm =
        Measure.infinitePi
          (fun u : A ⊕ (Aᶜ : Set ℤ) =>
            complexGaussian (fullWeightRate c (Equiv.Set.sumCompl A u))) := by
    exact ((MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq e).mp hReindex).symm
  have hGrouped :=
    fullWeightSequenceGaussian_sumGroupedLaw_afterPrerequisites_v4 c A
  have hHeadTail :=
    BoolToHeadTailProductAfterEqPiV1.groupedLaw_map_headTailEquiv_afterEqPi c A
  change (fullWeightSequenceGaussian c).map ((G.trans H) ∘ e.symm) = _
  rw [← Measure.map_map (G.trans H).measurable e.symm.measurable]
  rw [hRawReindex]
  change (Measure.infinitePi
      (fun u : A ⊕ (Aᶜ : Set ℤ) =>
        complexGaussian (fullWeightRate c (Equiv.Set.sumCompl A u)))).map (H ∘ G) = _
  rw [← Measure.map_map H.measurable G.measurable]
  rw [hGrouped]
  exact hHeadTail

end NlsGge.Measure.RawHeadTailProductAfterEqPiV3
