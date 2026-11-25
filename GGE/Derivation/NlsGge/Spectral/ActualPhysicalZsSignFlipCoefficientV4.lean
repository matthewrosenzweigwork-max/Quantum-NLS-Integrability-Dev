import NlsGge.Spectral.ActualReflectedPhysicalCoefficientForContinuousStateV1
import NlsGge.Spectral.ActualPhysicalSignFlipScalarCoefficientMinimumV1
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped Matrix
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Constant component sign flip; its conjugacy leaves the original spectral
parameter unchanged and negates the actual physical potential. -/
def actualPhysicalZsSignFlipVector (v : Fin 2 → ℂ) : Fin 2 → ℂ := ![v 0, -v 1]

theorem actualPhysicalZsSignFlipVector_involutive (v : Fin 2 → ℂ) :
    actualPhysicalZsSignFlipVector (actualPhysicalZsSignFlipVector v) = v := by
  funext i
  fin_cases i <;> simp [actualPhysicalZsSignFlipVector]

/-- The sign-flip conjugacy uses actual Lp-cover identities only almost
everywhere, never an assumed pointwise negative representative. -/
theorem actualPhysicalL2ZsCoefficient_ae_signFlip
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 →
      zsCoefficientComplex
        (fun x => naturalPhysicalCoverL2 (-u) (x : SpectralCircle)) z t *ᵥ
          actualPhysicalZsSignFlipVector v =
      actualPhysicalZsSignFlipVector
        (zsCoefficientComplex
          (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z t *ᵥ v) := by
  have hn := (ae_restrict_iff' measurableSet_Ioc).mp
    (naturalPhysicalCoverL2_neg_source_ae u)
  have hu := (ae_restrict_iff' measurableSet_Ioc).mp
    (actualPhysicalL2SourcePotential_cover_ae u)
  have h0 : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by simp [ae_iff, measure_singleton]
  filter_upwards [hn, hu, h0] with t hnt hut ht0
  intro ht
  have htcc : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  have hti : t ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne htcc.1 (Ne.symm ht0), htcc.2⟩
  have hm : naturalPhysicalCoverL2 (-u) (t : SpectralCircle) =
      -naturalPhysicalCoverL2 u (t : SpectralCircle) :=
    (hnt hti).trans (congrArg Neg.neg (hut hti))
  simpa only [zsCoefficientComplex, actualPhysicalZsSignFlipVector, hm] using
    actualPhysicalSignFlipScalarCoefficientMinimum31
      (naturalPhysicalCoverL2 u (t : SpectralCircle)) z v

/-- One common AE set works for every state, including a time-dependent
column. The AE quantifier precedes the state quantifier. -/
theorem actualPhysicalL2ZsCoefficient_ae_signFlip_allStates
    (u : PhysicalL2) (z : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 → ∀ v : Fin 2 → ℂ,
      zsCoefficientComplex
        (fun x => naturalPhysicalCoverL2 (-u) (x : SpectralCircle)) z t *ᵥ
          actualPhysicalZsSignFlipVector v =
      actualPhysicalZsSignFlipVector
        (zsCoefficientComplex
          (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z t *ᵥ v) := by
  have hn := (ae_restrict_iff' measurableSet_Ioc).mp
    (naturalPhysicalCoverL2_neg_source_ae u)
  have hu := (ae_restrict_iff' measurableSet_Ioc).mp
    (actualPhysicalL2SourcePotential_cover_ae u)
  have h0 : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by simp [ae_iff, measure_singleton]
  filter_upwards [hn, hu, h0] with t hnt hut ht0
  intro ht v
  have htcc : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  have hti : t ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne htcc.1 (Ne.symm ht0), htcc.2⟩
  have hm : naturalPhysicalCoverL2 (-u) (t : SpectralCircle) =
      -naturalPhysicalCoverL2 u (t : SpectralCircle) :=
    (hnt hti).trans (congrArg Neg.neg (hut hti))
  simpa only [zsCoefficientComplex, actualPhysicalZsSignFlipVector, hm] using
    actualPhysicalSignFlipScalarCoefficientMinimum31
      (naturalPhysicalCoverL2 u (t : SpectralCircle)) z v

end NlsGge.SpectralFoundations
end
