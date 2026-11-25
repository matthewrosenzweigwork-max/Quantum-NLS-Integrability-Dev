import Mathlib
import NlsGge.Atomic.I.I017Core
import NlsGge.ThirdConsultation.I.LimitLaws

/- I ENSEMBLE CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORT (no packet increment).
   Target NlsGge/Atomic/I/IEnsembleCore.lean, namespace NlsGge.ThirdConsultation.IEnsC.
   B-generic cores of Pro's round-14 bridges `actual_remainder_ae_eq` and `actual_ensemble_eq_I`: for ANY house record B
   whose cleaned inverse is the I inverse on all sequences (hB), (i) Rbar38 = sequenceRemainder γ_W-a.e. (on Omega038,
   which has full γ_W measure, Rbar38 = remainder38 ∘ cleanΦinv ≥ 0 = remainderForWeight ∘ physicalOfSequence, so the
   max is inactive; off Omega038 no pointwise claim), (ii) the four law/normalizer identities.  Integral and withDensity
   identities use only that a.e. equality, as Pro requires.
   Route note: Pro lists I024/I025 as suppliers of the good-set remainder facts; here they come from the landed house
   lemmas Rbar38_of_mem, Rbar38_nonneg, ae_mem_Omega038 (same source argument, specialised through hB). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.Birkhoff NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.IEnsC

theorem remainder_ae_of (B : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (lo up : ℝ) (c : BoundedCoefficients lo up) :
    B.Rbar38 c.val =ᵐ[fullWeightSequenceGaussian c.val] sequenceRemainder (weight c.val) := by
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lo ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ up := fun j => (hb j).2
  have hW := weight_continuous38 hl hb' hu'
  filter_upwards [ae_mem_Omega038 lo up c.val hl hb' hu'] with z hz
  have hnn := B.Rbar38_nonneg lo up c.val hl hb' hu' z
  unfold sequenceRemainder
  rw [← hB z, NlsGge.ThirdConsultation.I017C.remainderForWeight_eq c.val hW, ← B.Rbar38_of_mem c.val hz,
    max_eq_right hnn]

theorem ZW_eq_of (B : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (lo up : ℝ) (c : BoundedCoefficients lo up) :
    B.ZW38 c.val = limitNormalizer (weight c.val) := by
  unfold limitNormalizer gibbsPartition38 BirkhoffTop38.ZW38
  change _ = ∫ z, Real.exp (-sequenceRemainder (weight c.val) z) ∂(fullWeightSequenceGaussian c.val)
  exact integral_congr_ae ((remainder_ae_of B hB lo up c).mono fun z hz => by simp only [hz])

theorem muHat_eq_of (B : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (lo up : ℝ) (c : BoundedCoefficients lo up) :
    B.muHatW38 c.val = weightedSequenceLaw (weight c.val) := by
  have hZ := ZW_eq_of B hB lo up c
  unfold weightedSequenceLaw gibbsLaw38 BirkhoffTop38.muHatW38 Measure.tilted
  change _ = (fullWeightSequenceGaussian c.val).withDensity
    (fun z => ENNReal.ofReal (Real.exp (-sequenceRemainder (weight c.val) z) /
      ∫ x, Real.exp (-sequenceRemainder (weight c.val) x) ∂(fullWeightSequenceGaussian c.val)))
  have hZ' : ∫ x, Real.exp (-sequenceRemainder (weight c.val) x) ∂(fullWeightSequenceGaussian c.val) =
      B.ZW38 c.val := hZ.symm
  rw [hZ']
  exact withDensity_congr_ae ((remainder_ae_of B hB lo up c).mono fun z hz => by simp only [hz])

theorem muW_eq_of (B : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (lo up : ℝ) (c : BoundedCoefficients lo up) :
    B.muW38 c.val = physicalLaw (weight c.val) := by
  unfold BirkhoffTop38.muW38 physicalLaw
  rw [muHat_eq_of B hB lo up c, show B.cleanΦinv = physicalOfSequence from funext hB]

theorem ensemble_finite_of (B : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, B.cleanΦinv z = physicalOfSequence z)
    (lo up : ℝ) (c : BoundedCoefficients lo up) (Λ : Finset ℤ) :
    B.ZΛ38 c.val Λ = finiteRelativeNormalizer (weight c.val) Λ ∧
    B.nuHat38 c.val Λ = finiteGapCoordinateLaw (weight c.val) Λ ∧
    B.nu38 c.val Λ = finiteGapLaw (weight c.val) Λ := by
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lo ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ up := fun j => (hb j).2
  have hN := NlsGge.ThirdConsultation.I017C.law_eq_nuHat B hB lo up c.val hl hb' hu' Λ
  refine ⟨(NlsGge.ThirdConsultation.I017C.rel_eq B hB lo up c.val hl hb' hu' Λ).symm, hN.symm, ?_⟩
  unfold finiteGapLaw BirkhoffTop38.nu38
  rw [hN, NlsGge.ThirdConsultation.I017C.field_eq38 B hB Λ]

end NlsGge.ThirdConsultation.IEnsC
