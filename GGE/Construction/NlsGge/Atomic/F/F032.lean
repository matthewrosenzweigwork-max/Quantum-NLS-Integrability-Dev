/- F032 PRODUCTION02 (codex_luna13, AUTHOR; uncompiled worker draft).
   Target NlsGge/Atomic/F/F032.lean, namespace NlsGge.ThirdConsultation.F.
   Head copied verbatim from followup13 STATEMENTS/F.md §F-032, lines 712-727;
   round-17 binding is retain_head_unchanged.
   Route: f031 L1 convergence + Mathlib integral continuity for the normalizer;
   f015/F05 actual-law identification; the F08 finite and weak law formulas.
   No new design definitions are needed: F010Host and F030Host already host the
   F-032 design objects. -/
import Mathlib
import NlsGge.Atomic.F.F015
import NlsGge.Atomic.F.F031

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.F
open NlsGge.GKDefinitionDesign

/-- **F-032** (head verbatim): relative normalizers converge and the original finite bare field laws
converge against every bounded continuous observable on the common Sobolev space. -/
theorem f032 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    0 < finiteNormalizer m β ∧
    Tendsto (finiteOrderRelativeZ m β) atTop (nhds (finiteNormalizer m β)) ∧
    IsProbabilityMeasure (finiteGapLaw m β) ∧
    (∀ N : ℕ, IsProbabilityMeasure (nuBare38 m β N)) ∧
    ∀ F : BoundedContinuousFunction (Hm1 m) ℝ,
      (∀ N : ℕ,
        (∫ u, F u ∂nuBare38 m β N) =
          (∫ u, F (truncSobolev38 _ N u) * weightFN38 m β N u ∂gammaFM38 m β) /
            finiteOrderRelativeZ m β N) ∧
      Tendsto (fun N =>
        (∫ u, F (truncSobolev38 _ N u) * weightFN38 m β N u ∂gammaFM38 m β) /
          finiteOrderRelativeZ m β N) atTop (nhds (∫ u, F u ∂finiteGapLaw m β)) ∧
      Tendsto (fun N => ∫ u, F u ∂nuBare38 m β N) atTop
        (nhds (∫ u, F u ∂finiteGapLaw m β)) := by
  have h15 := f015 m hm β hβ
  have hPositive : 0 < finiteNormalizer m β := h15.2.2.2.1
  have h05 := NlsGge.Birkhoff.F05_identity38
    NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
    NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38 hm hβ
  have hNormalizerEq : finiteNormalizer m β =
      NlsGge.Birkhoff.ZM38 NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38 m β := by
    calc
      finiteNormalizer m β =
          ∫ u, Real.exp (-(Vm38 m β u)) ∂gammaFM38 m β := (h15.2.2.1).symm
      _ = NlsGge.Birkhoff.ZM38
            NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38 m β := h05.2.2.1
  have hLaw :
      NlsGge.Birkhoff.muM38 NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38 m β =
        finiteGapLaw m β := by
    rw [h05.2.2.2, h15.1]
    congr 1
    funext u
    rw [hNormalizerEq, div_eq_mul_inv]
    apply congrArg ENNReal.ofReal
    exact mul_comm _ _
  have hGapProbability : IsProbabilityMeasure (finiteGapLaw m β) := by
    rw [← hLaw]
    exact NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.isProbabilityMeasure_muM38 hm hβ
  have hBareProbability : ∀ N : ℕ, IsProbabilityMeasure (nuBare38 m β N) := by
    intro N
    exact NlsGge.Birkhoff.isProbabilityMeasure_nuBare38 hm hβ N
  obtain ⟨_, _, hWeightIntegrable, _, _, hL1⟩ := f031 m hm β hβ
  have hWeightIntegralTendsto :
      Tendsto (fun N : ℕ => ∫ u, weightFN38 m β N u ∂gammaFM38 m β) atTop
        (nhds (∫ u, weightFInf38 m β u ∂gammaFM38 m β)) :=
    MeasureTheory.tendsto_integral_of_L1'
      (f := weightFInf38 m β)
      (F := fun N : ℕ => weightFN38 m β N)
      (l := atTop)
      (Filter.Eventually.of_forall hWeightIntegrable) hL1
  have hLimitIntegral :
      (∫ u, weightFInf38 m β u ∂gammaFM38 m β) = finiteNormalizer m β := by
    change (∫ u, Real.exp (-(Vm38 m β u)) ∂gammaFM38 m β) = finiteNormalizer m β
    exact h15.2.2.1
  have hRelativeIntegral : ∀ N : ℕ,
      (∫ u, weightFN38 m β N u ∂gammaFM38 m β) = finiteOrderRelativeZ m β N := by
    intro N
    exact (f030 m hm β hβ N).2.2.2.2.1
  have hRelativeSequence :
      (fun N : ℕ => finiteOrderRelativeZ m β N) =
        fun N => ∫ u, weightFN38 m β N u ∂gammaFM38 m β := by
    funext N
    exact (hRelativeIntegral N).symm
  have hNormalizerTendsto :
      Tendsto (finiteOrderRelativeZ m β) atTop (nhds (finiteNormalizer m β)) := by
    change Tendsto (fun N : ℕ => finiteOrderRelativeZ m β N) atTop
      (nhds (finiteNormalizer m β))
    rw [hRelativeSequence, ← hLimitIntegral]
    exact hWeightIntegralTendsto
  refine ⟨hPositive, hNormalizerTendsto, hGapProbability, hBareProbability, ?_⟩
  intro F
  have hBareFormula : ∀ N : ℕ,
      (∫ u, F u ∂nuBare38 m β N) =
        (∫ u, F (truncSobolev38 _ N u) * weightFN38 m β N u ∂gammaFM38 m β) /
          finiteOrderRelativeZ m β N := by
    intro N
    have hFMeasurable : Measurable (fun u : Hm1 m => F u) := F.continuous.measurable
    have hTestMeasurable :
        Measurable (fun u : Hm1 m =>
          F (truncSobolev38 _ N u) * weightFN38 m β N u) :=
      (hFMeasurable.comp
        (NlsGge.Birkhoff.continuous_truncSobolev38 _ N).measurable).mul
        (NlsGge.Birkhoff.measurable_weightFN38 m β N)
    have hTestTransfer := NlsGge.Birkhoff.integral_gammaF38 hm hβ
      (fun u : Hm1 m => F (truncSobolev38 _ N u) * weightFN38 m β N u)
      hTestMeasurable
    have hWeightTransfer := NlsGge.Birkhoff.integral_gammaF38 hm hβ
      (weightFN38 m β N) (NlsGge.Birkhoff.measurable_weightFN38 m β N)
    have hPN : ∀ᵐ x ∂(gammaM38 m β),
        PN38 m N x = truncSobolev38 _ N (gaussianRealization38 m x) :=
      (NlsGge.Birkhoff.ae_PN_eq_trunc38 hm hβ).mono fun x hx => hx N
    have hWeight : weightN38 m β N =ᵐ[gammaM38 m β]
        fun x => weightFN38 m β N (gaussianRealization38 m x) :=
      NlsGge.Birkhoff.ae_weightN_eq38 hm hβ N
    have hNumerator :
        (∫ x, F (PN38 m N x) * weightN38 m β N x ∂gammaM38 m β) =
          (∫ u, F (truncSobolev38 _ N u) * weightFN38 m β N u ∂gammaFM38 m β) := by
      calc
        (∫ x, F (PN38 m N x) * weightN38 m β N x ∂gammaM38 m β) =
            (∫ x, F (truncSobolev38 _ N (gaussianRealization38 m x)) *
              weightFN38 m β N (gaussianRealization38 m x) ∂gammaM38 m β) := by
          apply integral_congr_ae
          filter_upwards [hPN, hWeight] with x hPNx hWeightx
          rw [hPNx, hWeightx]
        _ = ∫ u, F (truncSobolev38 _ N u) * weightFN38 m β N u ∂gammaFM38 m β :=
          hTestTransfer.symm
    have hDenominator :
        (∫ x, weightN38 m β N x ∂gammaM38 m β) =
          (∫ u, weightFN38 m β N u ∂gammaFM38 m β) := by
      calc
        (∫ x, weightN38 m β N x ∂gammaM38 m β) =
            (∫ x, weightFN38 m β N (gaussianRealization38 m x) ∂gammaM38 m β) :=
          integral_congr_ae hWeight
        _ = ∫ u, weightFN38 m β N u ∂gammaFM38 m β := hWeightTransfer.symm
    have hRelative := hRelativeIntegral N
    calc
      (∫ u, F u ∂nuBare38 m β N) =
          (∫ x, F (PN38 m N x) * weightN38 m β N x ∂gammaM38 m β) /
            ∫ x, weightN38 m β N x ∂gammaM38 m β :=
        NlsGge.Birkhoff.integral_nuBare38 hm hβ N F hFMeasurable
      _ =
          (∫ u, F (truncSobolev38 _ N u) * weightFN38 m β N u ∂gammaFM38 m β) /
            finiteOrderRelativeZ m β N := by
        rw [hNumerator, hDenominator, hRelative]
  have hWeak := NlsGge.Birkhoff.BirkhoffInput38.F08_weak_integral38
    NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
    NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38 hm hβ F
  rw [hLaw] at hWeak
  have hRatioSequence :
      (fun N : ℕ =>
        (∫ u, F (truncSobolev38 _ N u) * weightFN38 m β N u ∂gammaFM38 m β) /
          finiteOrderRelativeZ m β N) =
        fun N => ∫ u, F u ∂nuBare38 m β N := by
    funext N
    exact (hBareFormula N).symm
  have hRatioTendsto :
      Tendsto (fun N : ℕ =>
        (∫ u, F (truncSobolev38 _ N u) * weightFN38 m β N u ∂gammaFM38 m β) /
          finiteOrderRelativeZ m β N) atTop
        (nhds (∫ u, F u ∂finiteGapLaw m β)) := by
    rw [hRatioSequence]
    exact hWeak
  exact ⟨hBareFormula, hRatioTendsto, hWeak⟩

end NlsGge.ThirdConsultation.F

end
