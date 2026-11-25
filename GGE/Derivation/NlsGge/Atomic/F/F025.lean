import Mathlib
import NlsGge.Birkhoff.F07MassMoment38c
import NlsGge.Atomic.F.F024
import NlsGge.Atomic.F.F025Host

/- F025 PRODUCTION01 (proof development continuing proof development; not independently reviewed).
   Target NlsGge/Atomic/F/F025.lean, namespace NlsGge.ThirdConsultation.F. F-024 is landed at bd3f11290;
   production imports it normally. The round-17 binding retains the followup13 head unchanged.
   The separate root main-probe bundle imports landed F-024 and inlines only F025Host and this packet. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.F
open NlsGge.GKDefinitionDesign

/-- **F-025 core** at inputs `B, O`, with the lowered normalizer identified through `hNf`. -/
theorem f025_of_inputs (B : BirkhoffInput38) (O : OneSmoothingInput38 B) (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) (δ : ℝ)
    (hδ : 0 < δ) (hδβ : δ < β (m - 1)) (Nf : ℝ) (hNf : ZM38 B m (lowerCoef38 m β δ) = Nf) :
    (∀ u : Hm1 m, (chargeSobolev38 m 0 u) ^ m ≤ chargeSobolev38 m (m - 1) u) ∧
    Integrable (tiltedTerminal m β δ) (gammaFM38 m β) ∧
    (∫ u, tiltedTerminal m β δ u ∂gammaFM38 m β) ≤ Nf / tiltProduct m β δ := by
  obtain ⟨hint, hI⟩ := B.F07_expMass38 O hm hβ hδ hδβ
  rw [f024_dDelta_eq m hm β δ, hNf] at hI
  exact ⟨fun u => chargeMoment_mass_sobolev38 m hm u, hint, hI⟩

/-- **F-025** (head verbatim). -/
theorem f025 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) (δ : ℝ)
    (hδ : 0 < δ) (hδβ : δ < β (m - 1)) :
    (∀ u : Hm1 m, (chargeSobolev38 m 0 u) ^ m ≤ chargeSobolev38 m (m - 1) u) ∧
    Integrable (tiltedTerminal m β δ) (gammaFM38 m β) ∧
    (∫ u, tiltedTerminal m β δ u ∂gammaFM38 m β) ≤
      finiteNormalizer m (lowerCoef38 m β δ) / tiltProduct m β δ := by
  have hβ' : ∀ j ≤ m, 0 < lowerCoef38 m β δ j := lowerCoef_pos38 hβ hδβ
  have hNf : ZM38 NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38 m (lowerCoef38 m β δ) =
      finiteNormalizer m (lowerCoef38 m β δ) :=
    ((F05_identity38 NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
      NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38 hm hβ').2.2.1).symm.trans
      (f015 m hm (lowerCoef38 m β δ) hβ').2.2.1
  exact f025_of_inputs NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
    NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38 m hm β hβ δ hδ hδβ
    (finiteNormalizer m (lowerCoef38 m β δ)) hNf

end NlsGge.ThirdConsultation.F
