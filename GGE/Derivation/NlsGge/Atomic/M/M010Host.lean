import Mathlib
import NlsGge.Atomic.M.M009Support8
import NlsGge.Spectral.ActualGapActionAllNE02_38
import NlsGge.Spectral.ActualQuasimomentumE02_38

/- M-010 HOST01 (proof development, AUTHOR; not reviewed).  Round-14 hosts for the M primitive transport
   (PRO_DEFINITION_RESPONSE_FP80_14.md, cluster 4 "The primitive boundary accessor is staged" and the M.openGap / M.closedGap /
   M.spectralHeight paragraph).  Only the STAGE-1 literal predicates and the three gap hosts are installed here:
   `positiveHeightFilter`, `boundaryPoint`, `HasBoundaryValue`, `M.spectralHeight`, `M.openGap`, `M.closedGap`.
   (`boundaryValue`/`boundaryPrimitive` are admitted only in M010Support2 after the unique-existence obligation.)
   Grep of NlsGge/ (2026-11-01): none of these names exists in namespaces NlsGge.ThirdConsultation.M / .MPrimitive.
   DEVIATION (flagged for root, see M010_NOTES.md): Pro's DEFINITIONS/M body of `M.openGap` is `actualGapE02_38 u n`
   (window version, needs box/window hypotheses to be the n-th gap); the head of M-010 clause 1 is FALSE for it (large
   constant potential: window is one big gap of label 0).  Here `openGap`/`closedGap` use the landed AllN endpoints, i.e.
   the body of the landed KO.openGap / KO.closedGap, which is what the source "open gap g_n" is. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.M
noncomputable section

def spectralHeight (u : PhysicalL2) (_n : ℤ) (x : ℝ) : ℝ :=
  actualGapHeightE02_38 u x

def openGap (u : PhysicalL2) (n : ℤ) : Set ℝ :=
  Set.Ioo (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)

def closedGap (u : PhysicalL2) (n : ℤ) : Set ℝ :=
  Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)

end
end NlsGge.ThirdConsultation.M

namespace NlsGge.ThirdConsultation.MPrimitive
noncomputable section

abbrev PositiveHeight := {t : ℝ // 0 < t}

def positiveHeightFilter : Filter PositiveHeight :=
  Filter.comap (fun t : PositiveHeight => t.1) (𝓝[>] (0 : ℝ))

def boundaryPoint (x : ℝ) (upper : Bool) (t : PositiveHeight) : ℂ :=
  (x : ℂ) + (if upper then Complex.I else -Complex.I) * (t.1 : ℂ)

def HasBoundaryValue (u : PhysicalL2) (x : ℝ) (upper : Bool) (A : ℂ) : Prop :=
  ∃ F : PositiveHeight → ℂ,
    (∀ t : PositiveHeight,
      ∃ ht : realSlice u ∈ gkW ∧
          boundaryPoint x upper t ∈ endpointClosureFiber (realSlice u),
        F t = M.primitive ⟨(realSlice u, boundaryPoint x upper t), ht⟩) ∧
    Tendsto F positiveHeightFilter (𝓝 A)

end
end NlsGge.ThirdConsultation.MPrimitive
