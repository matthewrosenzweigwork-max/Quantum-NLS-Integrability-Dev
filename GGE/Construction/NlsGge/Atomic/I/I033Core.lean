import Mathlib
import NlsGge.Atomic.I.I025Core
import NlsGge.Measure.GibbsVariational38

                                                                                                                       
                                                                                  
                                                                                                      
                                                                                                                        
                                                                                                                         
                                                                                                           
                                                                                                               
                                                                                                  
                                                                                                                 
                                                                      
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.I033C

theorem measurable_sequenceRemainder (Bk : BirkhoffTop38)
    (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z) (W : ℝ → ℝ) (hW : Continuous W) :
    Measurable (sequenceRemainder W) := by
  have hPm : Measurable physicalOfSequence := by
    rw [show physicalOfSequence = Bk.cleanΦinv from (funext hB).symm]
    exact Bk.measurable_cleanΦinv
  unfold sequenceRemainder
  exact measurable_const.max
    ((NlsGge.ThirdConsultation.I025C.measurable_remainderForWeight W hW).comp hPm)

theorem sequenceRemainder_nonneg (W : ℝ → ℝ) (z : ℤ → ℂ) : 0 ≤ sequenceRemainder W z :=
  le_max_left _ _

theorem law_eq (c : ℕ → ℝ) :
    weightedSequenceLaw (weight c) =
      gibbsLaw38 (fullWeightSequenceGaussian c) (sequenceRemainder (weight c)) := rfl

theorem normalizer_eq (c : ℕ → ℝ) :
    limitNormalizer (weight c) =
      gibbsPartition38 (fullWeightSequenceGaussian c) (sequenceRemainder (weight c)) := rfl

theorem i033_of (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (ρ : Measure (ℤ → ℂ)) [IsProbabilityMeasure ρ]
    (hac : ρ ≪ fullWeightSequenceGaussian c.val)
    (hK : InformationTheory.klDiv ρ (fullWeightSequenceGaussian c.val) ≠ ⊤)
    (hR : Integrable (sequenceRemainder (weight c.val)) ρ) :
    ρ ≪ weightedSequenceLaw (weight c.val) ∧
    InformationTheory.klDiv ρ (weightedSequenceLaw (weight c.val)) ≠ ⊤ ∧
    (InformationTheory.klDiv ρ (weightedSequenceLaw (weight c.val))).toReal =
      (InformationTheory.klDiv ρ (fullWeightSequenceGaussian c.val)).toReal +
        (∫ z : ℤ → ℂ, sequenceRemainder (weight c.val) z ∂ρ) +
        Real.log (limitNormalizer (weight c.val)) := by
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hW := weight_continuous38 hl (fun j => (hb j).1) (fun j => (hb j).2)
  have hRm := measurable_sequenceRemainder Bk hB (weight c.val) hW
  have h0 := sequenceRemainder_nonneg (weight c.val)
  obtain ⟨-, hK'⟩ := InformationTheory.klDiv_ne_top_iff.mp hK
  obtain ⟨hne, hre⟩ := toReal_klDiv_gibbs38 (fullWeightSequenceGaussian c.val) _ hRm h0 ρ hac hK' hR
  rw [law_eq, normalizer_eq]
  exact ⟨hac.trans (ac_gibbsLaw38 _ _ hRm h0), hne, hre⟩

theorem i034_of (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    let γ := fullWeightSequenceGaussian c.val
    let R := sequenceRemainder (weight c.val)
    let μ := weightedSequenceLaw (weight c.val)
    let Z := limitNormalizer (weight c.val)
    Integrable R μ ∧ (∫ z : ℤ → ℂ, R z ∂μ) ≤ 1 / (Real.exp 1 * Z) ∧
    freeEnergy38 γ R μ = ENNReal.ofReal (-Real.log Z) ∧
    freeEnergy38 γ R μ < ⊤ ∧
    ∀ ρ : Measure (ℤ → ℂ), IsProbabilityMeasure ρ →
      ENNReal.ofReal (-Real.log Z) ≤ freeEnergy38 γ R ρ ∧
      (freeEnergy38 γ R ρ = ENNReal.ofReal (-Real.log Z) ↔ ρ = μ) := by
  dsimp only
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hW := weight_continuous38 hl (fun j => (hb j).1) (fun j => (hb j).2)
  have hRm := measurable_sequenceRemainder Bk hB (weight c.val) hW
  have h0 := sequenceRemainder_nonneg (weight c.val)
  rw [law_eq, normalizer_eq]
  refine ⟨integrable_gibbsLaw38 _ _ hRm h0, integral_gibbsLaw38_le _ _ hRm h0,
    freeEnergy38_gibbs _ _ hRm h0, ?_, fun ρ hρ => ⟨freeEnergy38_ge _ _ hRm h0 ρ,
      freeEnergy38_eq_iff _ _ hRm h0 ρ⟩⟩
  rw [freeEnergy38_gibbs _ _ hRm h0]
  exact ENNReal.ofReal_lt_top

end NlsGge.ThirdConsultation.I033C
