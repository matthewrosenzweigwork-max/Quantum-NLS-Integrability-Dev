import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.Birkhoff.W05FiniteGap38
import NlsGge.Birkhoff.W05ChargeSeries38
import NlsGge.Birkhoff.S04FiniteGapInvariance38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.Hierarchy.A01Spectral38

/- R-105 PRODUCTION01 (proof development, AUTHOR; not reviewed; needs ROOT MAIN PROBE). PACKET R-105, target
   NlsGge/Atomic/R/R105.lean (TASK_INDEX, REUSE/EXTRACT). Heads and preamble VERBATIM from followup13 STATEMENTS/R.md
   §R-105 (l.1437–1471 = r14 PRO_DEFINITION_RESPONSE_FP80_14.md l.4199–4229; BINDING_INDEX_FP80_14 target_names
   r105_main and actual_finiteGap_approximation_smooth) except the owner-APPROVED lexical repair 24
   (`B.field` → `(B).field` under the `local notation "B"`; AUDIT_DEFERRED_NOTES01), as in landed R-099/R-119.
   * r105_main: the printed exact landed source reuse W05FiniteGap38.lean:finiteGap_approximation_W05_38 at
     B = PDE.actualBirkhoffInput38, O = PDE.actualOneSmoothingInput38.
   * actual_finiteGap_approximation_smooth (Pro: "recorded in the companion", not an undefined predicate):
     smooth representative from W05ChargeSeries38.spectralEnergyW38_eq_chargeSeries_physOfE38 (every 𝓕⁻¹x, x ∈ E_s);
     finite gap: 𝓕⁻¹(approx) = Φ⁻¹(P_Λ Φ u) = finiteGapField38 Λ w (physOfE_finiteGapApproxE38, projFin38_eq_extZero38)
     has finitely supported Φ (finite_support_Φ_finiteGapField38); an open gap has positive action
     (actualGapAction_pos_of_open38) and action = |Φ_n|² (action_L2), so open gaps ⊆ supp Φ.
   Extra imports only provide the namespaces/names used. No hypothesis added.
   REPAIR-22-CLASS LEXICAL ADDITIONS (need root/reviewer confirmation, as for KO-018 / T-026 preludes): the printed
   preamble opens `ENNReal` but not `ContDiff`, so `ContDiff ℝ ∞ U` in the companion head would read `∞ : ℝ≥0∞`
   (selftest lane 488274be: type mismatch); added `open scoped ContDiff`. `smoothL2_38` lives only in
   NlsGge.HierarchyRiccati.Core (Hierarchy/A01Spectral38); added `open NlsGge.HierarchyRiccati.Core` + that import.
   Tokens and order of both heads are otherwise verbatim (plus repair 24). -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
open scoped ContDiff
open NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r105_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)  (hs : s < 3 / 4)
    (x : ECarrier38 c s) {Λ : ℕ → Finset ℤ} (hΛ : IsExhaustion38 Λ) :
    Tendsto (fun N : ℕ => (B).finiteGapApproxE38 c s O x (Λ N)) atTop (𝓝 x) ∧
    (∀ N : ℕ,
      physOfE38 c s ((B).finiteGapApproxE38 c s O x (Λ N)) =
        (B).cleanΦinv (projFin38 (Λ N) ((B).Φ (physOfE38 c s x)))) ∧
    (∀ N : ℕ, Summable (fun n : ℤ => remainderSummand38 c.val
        (physOfE38 c s ((B).finiteGapApproxE38 c s O x (Λ N))) n) ∧
      0 ≤ remainder38 c.val (physOfE38 c s ((B).finiteGapApproxE38 c s O x (Λ N)))) ∧
    Tendsto (fun N : ℕ => remainder38 c.val (physOfE38 c s ((B).finiteGapApproxE38 c s O x (Λ N))))
      atTop (𝓝 (remainder38 c.val (physOfE38 c s x))) ∧
    0 ≤ remainder38 c.val (physOfE38 c s x) :=
  BirkhoffInput38.finiteGap_approximation_W05_38 B c s O hs x hΛ

theorem actual_finiteGap_approximation_smooth {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (x : ECarrier38 c s)
    (Lambda : ℕ → Finset ℤ) (hLambda : IsExhaustion38 Lambda) :
    ∀ N : ℕ,
      NlsGge.ThirdConsultation.finiteGap
        (physOfE38 c s ((B).finiteGapApproxE38 c s O x (Lambda N))) ∧
      ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
        (hper : Function.Periodic U 1),
        smoothL2_38 U hU hper =
          physOfE38 c s ((B).finiteGapApproxE38 c s O x (Lambda N)) := by
  intro N
  refine ⟨?_, ?_⟩
  · -- finitely many open gaps: open gap ⇒ positive action = |Φ_n|² ⇒ n ∈ supp Φ (finite)
    set u : PhysicalL2 := physOfE38 c s ((B).finiteGapApproxE38 c s O x (Lambda N)) with hu
    have hfield : u = (B).finiteGapField38 (Lambda N)
        ((Lambda N).restrict ((B).Φ (physOfE38 c s x))) := by
      rw [hu, BirkhoffInput38.physOfE_finiteGapApproxE38, projFin38_eq_extZero38]
      rfl
    have hfin : {n : ℤ | (B).Φ u n ≠ 0}.Finite := by
      rw [hfield]
      exact BirkhoffTop38.finite_support_Φ_finiteGapField38 _ _ _
    unfold NlsGge.ThirdConsultation.finiteGap
    refine hfin.subset (fun n hn => ?_)
    have hord : NlsGge.SpectralFoundations.actualGapLowerAllE02_38 u n ≤
        NlsGge.SpectralFoundations.actualGapUpperAllE02_38 u n := by
      obtain ⟨y, hy⟩ := (NlsGge.SpectralFoundations.actualGapLevelSet_eq_Icc_E02_38 u n).1
      rw [(NlsGge.SpectralFoundations.actualGapLevelSet_eq_Icc_E02_38 u n).2] at hy
      exact hy.1.trans hy.2
    have hlt : NlsGge.SpectralFoundations.actualGapLowerAllE02_38 u n <
        NlsGge.SpectralFoundations.actualGapUpperAllE02_38 u n := lt_of_le_of_ne hord hn
    have hpos := NlsGge.Birkhoff.actualGapAction_pos_of_open38 u n hlt
    rw [← (B).action_L2 u n] at hpos
    intro h0
    have h0' : (B).T (fourierSeq38 u) n = 0 := h0
    rw [h0', norm_zero] at hpos
    norm_num at hpos
  · obtain ⟨U, hU, hper, hUu, -⟩ :=
      spectralEnergyW38_eq_chargeSeries_physOfE38 c s ((B).finiteGapApproxE38 c s O x (Lambda N))
    exact ⟨U, hU, hper, hUu⟩

end NlsGge.ThirdConsultation.R
