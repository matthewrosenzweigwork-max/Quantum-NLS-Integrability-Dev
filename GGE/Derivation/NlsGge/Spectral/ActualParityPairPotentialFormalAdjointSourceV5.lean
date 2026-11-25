import NlsGge.Spectral.ActualL2PotentialParityPairSourceOperatorV2
import NlsGge.Schur.PhysicalSector
import NlsGge.Spectral.ActualOffDiagonalPotentialPairingIntegrandV4
import NlsGge.Spectral.ActualPhysicalPotentialSourceConjugacyV3
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot

private abbrev actualParityPairPotentialMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc (0 : ℝ) 1)

private theorem actualSourceIntervalInner_eq_integral
    (f g : SourceIntervalL2) :
    inner ℂ f g = ∫ t, star (f t) * g t ∂actualParityPairPotentialMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards with t
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

/-- The actual two-channel L² multiplier is formally adjoint on the physical
real-potential slice. The L∞ states and their matching L² representatives are
kept as separate actual carriers; no ambient L²-to-L∞ coercion is used. -/
theorem actualL2PotentialParityPairSourceOperator_formal_adjoint_of_source_conjugacy
    (u₁ u₂ : PhysicalL2) (hphysical : u₂ = star u₁)
    (f g : ActualSourceIntervalLInfPair) (F G : SourcePairL2)
    (hf : ∀ b : Bool, (f b : ℝ → ℂ) =ᵐ[actualParityPairPotentialMeasure]
      (F b : ℝ → ℂ))
    (hg : ∀ b : Bool, (g b : ℝ → ℂ) =ᵐ[actualParityPairPotentialMeasure]
      (G b : ℝ → ℂ)) :
    inner ℂ (actualL2PotentialParityPairSourceOperator u₁ u₂ f) G =
      inner ℂ F (actualL2PotentialParityPairSourceOperator u₁ u₂ g) := by
  have hreal := actualPhysicalL2SourcePotential_star_ae u₁ u₂ hphysical
  have hfirst :
      inner ℂ (actualSourceL2PotentialTimesLInf u₁ (f false)) (G true) =
        inner ℂ (F false) (actualSourceL2PotentialTimesLInf u₂ (g true)) := by
    rw [actualSourceIntervalInner_eq_integral, actualSourceIntervalInner_eq_integral]
    apply integral_congr_ae
    have hmul₁ := actualSourceL2PotentialTimesLInf_ae u₁ (f false)
    have hmul₂ := actualSourceL2PotentialTimesLInf_ae u₂ (g true)
    filter_upwards [hmul₁, hmul₂, hf false, hg true, hreal]
      with t hmul₁t hmul₂t hft hgt hreal_t
    change star (actualSourceL2PotentialTimesLInf u₁ (f false) t) * G true t =
      star (F false t) * actualSourceL2PotentialTimesLInf u₂ (g true) t
    rw [hmul₁t, hmul₂t, ← hgt, ← hft, hreal_t]
    simp only [star_mul, star_star]
    ring
  have hsecond :
      inner ℂ (actualSourceL2PotentialTimesLInf u₂ (f true)) (G false) =
        inner ℂ (F true) (actualSourceL2PotentialTimesLInf u₁ (g false)) := by
    rw [actualSourceIntervalInner_eq_integral, actualSourceIntervalInner_eq_integral]
    apply integral_congr_ae
    have hmul₁ := actualSourceL2PotentialTimesLInf_ae u₂ (f true)
    have hmul₂ := actualSourceL2PotentialTimesLInf_ae u₁ (g false)
    filter_upwards [hmul₁, hmul₂, hf true, hg false, hreal]
      with t hmul₁t hmul₂t hft hgt hreal_t
    change star (actualSourceL2PotentialTimesLInf u₂ (f true) t) * G false t =
      star (F true t) * actualSourceL2PotentialTimesLInf u₁ (g false) t
    rw [hmul₁t, hmul₂t, ← hgt, ← hft, hreal_t]
    simp only [star_mul, star_star]
    ring
  simp only [PiLp.inner_apply, Fintype.sum_bool,
    actualL2PotentialParityPairSourceOperator_apply_true,
    actualL2PotentialParityPairSourceOperator_apply_false]
  calc
    inner ℂ (actualSourceL2PotentialTimesLInf u₁ (f false)) (G true) +
        inner ℂ (actualSourceL2PotentialTimesLInf u₂ (f true)) (G false) =
      inner ℂ (F false) (actualSourceL2PotentialTimesLInf u₂ (g true)) +
        inner ℂ (F true) (actualSourceL2PotentialTimesLInf u₁ (g false)) :=
          congrArg₂ (fun a b : ℂ => a + b) hfirst hsecond
    _ = inner ℂ (F true) (actualSourceL2PotentialTimesLInf u₁ (g false)) +
        inner ℂ (F false) (actualSourceL2PotentialTimesLInf u₂ (g true)) :=
          add_comm _ _

end NlsGge.Schur

end
