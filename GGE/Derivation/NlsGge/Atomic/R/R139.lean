import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Birkhoff.W10Localized38g
import NlsGge.Birkhoff.W10Localized38h
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

/- R-139 PRODUCTION01 (proof development, AUTHOR; not reviewed). PACKET R-139, target NlsGge/Atomic/R/R139.lean (TASK_INDEX,
   REUSE/EXTRACT). Both heads (r139_main, r139_2) and the preamble VERBATIM from followup13 STATEMENTS/R.md §R-139 (= r14,
   string-checked; r16 no change) with OWNER-APPROVED REPAIR 24 only: `B.muW38` -> `(B).muW38`, `B.locLimitLaw38` ->
   `(B).locLimitLaw38`. Proofs: the printed exact landed source reuse W10Localized38g.W10_normalized_Es38 and
   W10Localized38h.W10_normalized_Sobolev38 at the actual pair (binders and conclusions literally the printed ones; s is
   implicit in the landed statements). Positivity first: r139_main's first conjunct is μ_W(χ_R) > 0 (landed
   muW_chiR_pos38), proved before the ratio limit; the limit law is the landed normalized locLimitLaw38, not a bare ratio of
   totalized integrals. Measure.map measurability stays inside the landed producers. No dependence on the unlanded
   R-137 (h771) or R-138 (h774). Own imports (B1 lesson): OneSmoothing (notations/actual pair), W10Localized38g/h
   (producers, chiR38, locLimitLaw38, CutoffProfile38); rest = preamble namespaces. MAIN-ONLY. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r139_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (hFb : ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    0 < ∫ u, chiR38 χ R u ∂((B).muW38 c.val) ∧
    Tendsto (fun N : ℕ =>
        (∫ x, F (physOfE38 c s (projE38 c s N x)) * chiR38 χ R (physOfE38 c s (projE38 c s N x)) *
          fN38 c s N x ∂(fullWeightedSequenceGaussian c s)) /
        ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s)) atTop
      (𝓝 (∫ u, F u ∂((B).locLimitLaw38 c χ R))) :=
  (B).W10_normalized_Es38 O c hs hs' hχ hR F hF hFb

theorem r139_2 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)))
    (hFb : ∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) :
    Tendsto (fun N : ℕ =>
        (∫ x, F (physOfE38 c s (projE38 c s N x)) * chiR38 χ R (physOfE38 c s (projE38 c s N x)) *
          fN38 c s N x ∂(fullWeightedSequenceGaussian c s)) /
        ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s)) atTop
      (𝓝 (∫ u, F u ∂((B).locLimitLaw38 c χ R))) :=
  (B).W10_normalized_Sobolev38 O c hs hs' hχ hR r hr F hF hFb

end NlsGge.ThirdConsultation.R
